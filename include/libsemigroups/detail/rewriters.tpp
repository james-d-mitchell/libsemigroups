//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2025 Joseph Edwards + James D. Mitchell
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// This file contains the implementation of a Rule<ReductionOrder> object
// containers for Rule<ReductionOrder> objects. It also includes rewriter
// classes that can be used to rewrite strings relative to a collection of
// rules.

namespace libsemigroups::detail {
  ////////////////////////////////////////////////////////////////////////
  // Rule
  ////////////////////////////////////////////////////////////////////////

  template <typename ReductionOrder>
  Rule<ReductionOrder>::Rule(int64_t id) : _lhs(), _rhs(), _id(-1 * id) {
    LIBSEMIGROUPS_ASSERT(_id < 0);
  }

  template <typename ReductionOrder>
  void Rule<ReductionOrder>::activate_no_checks() noexcept {
    LIBSEMIGROUPS_ASSERT(_id != 0);
    LIBSEMIGROUPS_ASSERT(!active());
    _id *= -1;
  }

  template <typename ReductionOrder>
  void Rule<ReductionOrder>::deactivate_no_checks() noexcept {
    LIBSEMIGROUPS_ASSERT(_id != 0);
    LIBSEMIGROUPS_ASSERT(active());
    _id *= -1;
  }

  ////////////////////////////////////////////////////////////////////////
  // RuleLookup
  ////////////////////////////////////////////////////////////////////////

  // Reverse lex order
  template <typename ReductionOrder>
  bool RuleLookup<ReductionOrder>::operator<(RuleLookup const& that) const {
    auto it_this = _last - 1;
    auto it_that = that._last - 1;
    while (it_this > _first && it_that > that._first && *it_this == *it_that) {
      --it_that;
      --it_this;
    }
    return *it_this < *it_that;
  }

  ////////////////////////////////////////////////////////////////////////
  // Rules
  ////////////////////////////////////////////////////////////////////////

  template <typename ReductionOrder>
  Rules<ReductionOrder>::Stats::Stats() noexcept {
    init();
  }

  template <typename ReductionOrder>
  typename Rules<ReductionOrder>::Stats&
  Rules<ReductionOrder>::Stats::init() noexcept {
    max_word_length        = 0;
    max_active_word_length = 0;
    max_active_rules       = 0;
    min_length_lhs_rule    = std::numeric_limits<size_t>::max();
    total_rules            = 0;
    return *this;
  }

  template <typename ReductionOrder>
  Rules<ReductionOrder>& Rules<ReductionOrder>::init() {
    // Put all active rules and those rules in the stack into the
    // inactive_rules list
    for (Rule<ReductionOrder>* ptr : _active_rules) {
      ptr->deactivate_no_checks();
      _inactive_rules.insert(_inactive_rules.end(), ptr);
    }
    _active_rules.clear();
    for (auto& it : _cursors) {
      it = _active_rules.end();
    }
    return *this;
  }

  template <typename ReductionOrder>
  Rules<ReductionOrder>& Rules<ReductionOrder>::operator=(Rules const& that) {
    init();
    for (Rule<ReductionOrder> const* rule : that) {
      add_rule(copy_rule(rule));
    }
    for (size_t i = 0; i < _cursors.size(); ++i) {
      _cursors[i] = _active_rules.begin();
      std::advance(
          _cursors[i],
          std::distance(that.begin(),
                        static_cast<const_iterator>(that._cursors[i])));
    }
    return *this;
  }

  template <typename ReductionOrder>
  Rules<ReductionOrder>& Rules<ReductionOrder>::operator=(Rules&& that) {
    // We swap to ensure that all rules are properly deleted
    std::swap(_active_rules, that._active_rules);
    std::swap(_inactive_rules, that._inactive_rules);
    _cursors = std::move(that._cursors);
    _stats   = std::move(that._stats);
    return *this;
  }

  template <typename ReductionOrder>
  Rules<ReductionOrder>::~Rules() {
    for (Rule<ReductionOrder>* rule : _active_rules) {
      delete rule;
    }
    for (Rule<ReductionOrder>* rule : _inactive_rules) {
      delete rule;
    }
  }

  template <typename ReductionOrder>
  Rule<ReductionOrder>* Rules<ReductionOrder>::new_rule() {
    ++_stats.total_rules;
    Rule<ReductionOrder>* rule;
    if (!_inactive_rules.empty()) {
      rule = _inactive_rules.front();
      rule->set_id_no_checks(_stats.total_rules);
      _inactive_rules.erase(_inactive_rules.begin());
    } else {
      rule = new Rule<ReductionOrder>(_stats.total_rules);
    }
    LIBSEMIGROUPS_ASSERT(!rule->active());
    return rule;
  }

  template <typename ReductionOrder>
  Rule<ReductionOrder>*
  Rules<ReductionOrder>::copy_rule(Rule<ReductionOrder> const* rule) {
    return new_rule(rule->lhs().cbegin(),
                    rule->lhs().cend(),
                    rule->rhs().cbegin(),
                    rule->rhs().cend());
  }

  template <typename ReductionOrder>
  typename Rules<ReductionOrder>::iterator
  Rules<ReductionOrder>::erase_from_active_rules(iterator it) {
    // _stats.unique_lhs_rules.erase(*((*it)->lhs()));
    LIBSEMIGROUPS_ASSERT(!(*it)->active());
    // TODO(1) calling the next two lines double deactivates some rules (those
    // coming from make_active_rule_pending), weirdly everything works when
    // this happens (tests pass, though some assertions fail in debug mode)
    // and test 139 is twice as fast for some reason!

    // Rule<ReductionOrder>* rule = *it;
    // rule->deactivate_no_checks();

    if (it != _cursors[0] && it != _cursors[1]) {
      it = _active_rules.erase(it);
    } else if (it == _cursors[0] && it != _cursors[1]) {
      _cursors[0] = _active_rules.erase(it);
      it          = _cursors[0];
    } else if (it != _cursors[0] && it == _cursors[1]) {
      _cursors[1] = _active_rules.erase(it);
      it          = _cursors[1];
    } else {
      _cursors[0] = _active_rules.erase(it);
      _cursors[1] = _cursors[0];
      it          = _cursors[0];
    }
    return it;
  }

  template <typename ReductionOrder>
  void Rules<ReductionOrder>::add_rule(Rule<ReductionOrder>* rule) {
    LIBSEMIGROUPS_ASSERT(rule->lhs() != rule->rhs());
    _stats.max_word_length
        = std::max(_stats.max_word_length, rule->lhs().size());
    _stats.max_active_rules
        = std::max(_stats.max_active_rules, number_of_active_rules());
    // _stats.unique_lhs_rules.insert(*rule->lhs());
    rule->activate_no_checks();
    _active_rules.push_back(rule);
    for (auto& it : _cursors) {
      if (it == end()) {
        --it;
      }
    }
    if (rule->lhs().size() < _stats.min_length_lhs_rule) {
      // TODO(later) this is not valid when using non-length reducing
      // orderings (such as RECURSIVE)
      _stats.min_length_lhs_rule = rule->lhs().size();
    }
  }

  template <typename ReductionOrder>
  size_t Rules<ReductionOrder>::max_active_word_length() const {
    auto comp = [](Rule<ReductionOrder> const* p,
                   Rule<ReductionOrder> const* q) -> bool {
      return p->lhs().size() < q->lhs().size();
    };
    auto max = std::max_element(begin(), end(), comp);
    if (max != end()) {
      _stats.max_active_word_length
          = std::max(_stats.max_active_word_length, (*max)->lhs().size());
    }
    return _stats.max_active_word_length;
  }

  ////////////////////////////////////////////////////////////////////////
  // RewriteBase
  ////////////////////////////////////////////////////////////////////////

  template <typename ReductionOrder>
  RewriteBase<ReductionOrder>::RewriteBase()
      : _cached_confluent(false),
        _confluence_known(false),
        _max_pending_rules(0),
        _pending_rules(),
        _ticker_running(false) {}

  template <typename ReductionOrder>
  RewriteBase<ReductionOrder>& RewriteBase<ReductionOrder>::init() {
    Rules<ReductionOrder>::init();
    // Put all active rules and those rules in the stack into the
    // inactive_rules list
    for (Rule<ReductionOrder>* rule : _pending_rules) {
      Rules<ReductionOrder>::add_inactive_rule(rule);
    }
    _pending_rules.clear();
    _max_pending_rules = 0;
    _cached_confluent  = false;
    _confluence_known  = false;
    _ticker_running    = false;
    return *this;
  }

  template <typename ReductionOrder>
  RewriteBase<ReductionOrder>::RewriteBase(RewriteBase&& that)
      : _cached_confluent(that._cached_confluent.load()),
        _confluence_known(that._confluence_known.load()),
        _max_pending_rules(std::move(that._max_pending_rules)),
        _pending_rules(std::move(that._pending_rules)),
        _ticker_running(std::move(that._ticker_running)) {}

  template <typename ReductionOrder>
  RewriteBase<ReductionOrder>&
  RewriteBase<ReductionOrder>::operator=(RewriteBase const& that) {
    Rules<ReductionOrder>::operator=(that);
    _cached_confluent = that._cached_confluent.load();
    _confluence_known = that._confluence_known.load();
    _pending_rules.clear();
    _ticker_running = that._ticker_running;

    for (auto const* rule : that._pending_rules) {
      _pending_rules.emplace_back(copy_rule(rule));
    }
    return *this;
  }

  template <typename ReductionOrder>
  RewriteBase<ReductionOrder>&
  RewriteBase<ReductionOrder>::operator=(RewriteBase&& that) {
    Rules<ReductionOrder>::operator=(std::move(that));
    _cached_confluent = that._cached_confluent.load();
    _confluence_known = that._confluence_known.load();
    // Again we swap so that all rules are properly deleted
    std::swap(_pending_rules, that._pending_rules);
    _ticker_running = std::move(that._ticker_running);
    return *this;
  }

  template <typename ReductionOrder>
  RewriteBase<ReductionOrder>::~RewriteBase() {
    for (Rule<ReductionOrder>* rule : _pending_rules) {
      delete rule;
    }
    _pending_rules.clear();
  }

  template <typename ReductionOrder>
  void RewriteBase<ReductionOrder>::set_cached_confluent(tril val) const {
    if (val == tril::TRUE) {
      _confluence_known = true;
      _cached_confluent = true;
    } else if (val == tril::FALSE) {
      _confluence_known = true;
      _cached_confluent = false;
    } else {
      _confluence_known = false;
    }
  }

  template <typename ReductionOrder>
  bool
  RewriteBase<ReductionOrder>::add_pending_rule(Rule<ReductionOrder>* rule) {
    LIBSEMIGROUPS_ASSERT(!rule->active());
    if (rule->lhs() != rule->rhs()) {
      rule->reorder();
      _pending_rules.push_back(rule);
      _max_pending_rules = std::max(_max_pending_rules, _pending_rules.size());
      return true;
    } else {
      Rules<ReductionOrder>::add_inactive_rule(rule);
      return false;
    }
  }

  template <typename ReductionOrder>
  bool RewriteBase<ReductionOrder>::confluent() {
    using std::chrono::high_resolution_clock;
    using std::chrono::time_point;

    if (number_of_pending_rules() != 0) {
      set_cached_confluent(tril::unknown);
      return false;
    } else if (confluence_known()) {
      return RewriteBase<ReductionOrder>::cached_confluent();
    }

    std::atomic_uint64_t seen = 0;
    if (reporting_enabled() && !_ticker_running) {
      detail::Guard  state(_state, State::checking_confluence);
      detail::Guard  ticker(_ticker_running, true);
      time_point     start_time = high_resolution_clock::now();
      detail::Ticker t(
          [&]() { report_progress_from_thread(seen, start_time); });
      return confluent_impl(seen);
    } else {
      return confluent_impl(seen);
    }
  }

  template <typename ReductionOrder>
  void RewriteBase<ReductionOrder>::report_progress_from_thread(
      std::atomic_uint64_t const&                           seen,
      std::chrono::high_resolution_clock::time_point const& start_time) {
    if (_state == State::none) {
      using detail::string_time;
      auto gd       = detail::group_digits;
      auto active   = gd(number_of_active_rules());
      auto inactive = gd(number_of_inactive_rules());
      auto pending  = gd(number_of_pending_rules());
      auto defined  = gd(stats().total_rules);

      report_default("KnuthBendix: rules {} (active) | {} (inactive) | {} "
                     "(pending) | {} "
                     "(defined) | {}\n",
                     active,
                     inactive,
                     pending,
                     defined,
                     string_time(delta(start_time)));
    } else if (_state == State::checking_confluence) {
      report_checking_confluence(seen, start_time);
    } else {
      LIBSEMIGROUPS_ASSERT(_state == State::reducing_pending_rules);
      report_reducing_rules(seen, start_time);
    }
  }

  template <typename ReductionOrder>
  Rule<ReductionOrder>* RewriteBase<ReductionOrder>::next_pending_rule() {
    LIBSEMIGROUPS_ASSERT(_pending_rules.size() != 0);
    Rule<ReductionOrder>* rule = _pending_rules.back();
    _pending_rules.pop_back();
    return rule;
  }

  ////////////////////////////////////////////////////////////////////////
  // RewriteFromLeft
  ////////////////////////////////////////////////////////////////////////

  template <typename ReductionOrder>
  RewriteFromLeft<ReductionOrder>::~RewriteFromLeft() = default;

  template <typename ReductionOrder>
  RewriteFromLeft<ReductionOrder>& RewriteFromLeft<ReductionOrder>::init() {
    RewriteBase<ReductionOrder>::init();
    _set_rules.clear();
    return *this;
  }

  template <typename ReductionOrder>
  RewriteFromLeft<ReductionOrder>&
  RewriteFromLeft<ReductionOrder>::operator=(RewriteFromLeft const& that) {
    init();
    RewriteBase<ReductionOrder>::operator=(that);
    for (auto* rule : *this) {
#ifdef LIBSEMIGROUPS_DEBUG
      LIBSEMIGROUPS_ASSERT(_set_rules.emplace(RuleLookup(rule)).second);
#else
      _set_rules.emplace(RuleLookup(rule));
#endif
    }
    return *this;
  }

  template <typename ReductionOrder>
  typename RewriteFromLeft<ReductionOrder>::iterator
  RewriteFromLeft<ReductionOrder>::make_active_rule_pending(iterator it) {
    Rule<ReductionOrder>* rule = *it;
    rule->deactivate_no_checks();
    add_pending_rule(rule);
#ifdef LIBSEMIGROUPS_DEBUG
    LIBSEMIGROUPS_ASSERT(_set_rules.erase(RuleLookup(rule)));
#else
    _set_rules.erase(RuleLookup(rule));
#endif
    LIBSEMIGROUPS_ASSERT(_set_rules.size() == number_of_active_rules() - 1);
    return Rules<ReductionOrder>::erase_from_active_rules(it);
  }

  template <typename ReductionOrder>
  void RewriteFromLeft<ReductionOrder>::add_rule(Rule<ReductionOrder>* rule) {
    Rules<ReductionOrder>::add_rule(rule);
    // _stats.unique_lhs_rules.insert(*rule->lhs());
#ifdef LIBSEMIGROUPS_DEBUG
    LIBSEMIGROUPS_ASSERT(_set_rules.emplace(RuleLookup(rule)).second);
#else
    _set_rules.emplace(RuleLookup(rule));
#endif
    LIBSEMIGROUPS_ASSERT(_set_rules.size() == number_of_active_rules());
    set_cached_confluent(tril::unknown);
  }

  template <typename ReductionOrder>
  // REWRITE_FROM_LEFT from Sims, p67
  // Caution: this uses the assumption that rules are length reducing, if they
  // are not, then u might not have sufficient space!
  void RewriteFromLeft<ReductionOrder>::rewrite2(native_word_type& u) {
    if (u.size() < stats().min_length_lhs_rule) {
      return;
    }

    auto v_begin = u.begin();  // 0
    auto v_end   = u.begin() + stats().min_length_lhs_rule - 1;
    auto w_begin = v_end;
    auto w_end   = u.end();  // u.size()

    RuleLookup lookup;

    while (w_begin != w_end) {
      *v_end = *w_begin;
      ++v_end;
      ++w_begin;

      auto it = _set_rules.find(lookup(v_begin, v_end));
      if (it != _set_rules.end()) {
        Rule<ReductionOrder> const* rule = (*it).rule();
        if (rule->lhs().size() <= static_cast<size_t>(v_end - v_begin)) {
          LIBSEMIGROUPS_ASSERT(detail::is_suffix(
              v_begin, v_end, rule->lhs().cbegin(), rule->lhs().cend()));
          v_end -= rule->lhs().size();
          // u.resize(u.size() + rule->rhs() - rule->lhs);
          w_begin -= rule->rhs().size();
          std::copy(rule->rhs().cbegin(), rule->rhs().cend(), w_begin);
        }
      }
      while (w_begin != w_end
             && stats().min_length_lhs_rule - 1
                    > static_cast<size_t>((v_end - v_begin))) {
        *v_end = *w_begin;
        ++v_end;
        ++w_begin;
      }
    }
    u.erase(v_end - u.cbegin());
  }

  template <typename ReductionOrder>
  void RewriteFromLeft<ReductionOrder>::rewrite(native_word_type& v) {
    if (v.size() < stats().min_length_lhs_rule) {
      return;
    }

    size_t const n = stats().min_length_lhs_rule;
    // TODO we could try to modify rewrite2 to work with indices rather
    // than allocating w here every time (indices not iterators because
    // indices are independent of memory allocation)
    // TODO we could also, make w a data member like in RewriteTrie
    std::string w(v.rbegin(), v.rbegin() + v.size() - n + 1);
    v.erase(v.begin() + n - 1, v.end());

    RuleLookup lookup;

    while (!w.empty()) {
      v.push_back(w.back());
      w.pop_back();

      auto it = _set_rules.find(lookup(v.begin(), v.end()));
      if (it != _set_rules.end()) {
        Rule<ReductionOrder> const* rule = (*it).rule();
        if (rule->lhs().size() <= static_cast<size_t>(v.size())) {
          LIBSEMIGROUPS_ASSERT(detail::is_suffix(
              v.begin(), v.end(), rule->lhs().cbegin(), rule->lhs().cend()));
          v.erase(v.end() - rule->lhs().size(), v.end());
          w.append(rule->rhs().rbegin(), rule->rhs().rend());
        }
      }

      if (!w.empty() && n > v.size() + 1) {
        if (w.size() < n - v.size()) {
          // w = (w.begin(), w.begin() + 1, ..., w.end() - 1)
          //   = (w.rend() - 1, w.rend() - 2, ..., w.rbegin())
          v.append(w.rbegin(), w.rend() - 1);
          w.erase(w.begin() + 1, w.end());
        } else {
          // if k = n - v.size() - 1
          // w = (w.rend() - 1, ..., w.rbegin() + k - 1, ..., w.rbegin())
          //   = (w.begin(), ..., w.end() - k, ..., w.end() - 1)
          size_t k = n - v.size() - 1;
          v.append(w.rbegin(), w.rbegin() + k);
          w.erase(w.end() - k, w.end());
        }
      }
    }
  }

  template <typename ReductionOrder>
  void RewriteFromLeft<ReductionOrder>::report_checking_confluence(
      std::atomic_uint64_t const&                           seen,
      std::chrono::high_resolution_clock::time_point const& start_time) const {
    if (reporting_enabled()) {
      auto total_pairs
          = std::pow(Rules<ReductionOrder>::number_of_active_rules(), 2);

      auto total_pairs_s = detail::group_digits(total_pairs);
      auto now           = std::chrono::high_resolution_clock::now();
      auto time
          = std::chrono::duration_cast<std::chrono::seconds>(now - start_time);
      report_no_prefix("{:-<95}\n", "");
      report_default("KnuthBendix: locally confluent for: {0:>{width}} / "
                     "{1:>{width}} ({2:>4.1f}%) pairs of rules ({3}s)\n",
                     detail::group_digits(seen),
                     total_pairs_s,
                     (total_pairs != 0)
                         ? 100 * static_cast<double>(seen) / total_pairs
                         : 100,
                     time.count(),
                     fmt::arg("width", total_pairs_s.size()));
    }
  }

  template <typename ReductionOrder>
  bool
  RewriteFromLeft<ReductionOrder>::confluent_impl(std::atomic_uint64_t& seen) {
    using std::chrono::time_point;
    time_point start_time = std::chrono::high_resolution_clock::now();

    set_cached_confluent(tril::TRUE);
    native_word_type word1;
    native_word_type word2;

    for (auto it1 = begin(); it1 != end(); ++it1) {
      Rule<ReductionOrder> const* rule1 = *it1;
      // Seems to be much faster to do this in reverse.
      for (auto it2 = rbegin(); it2 != rend(); ++it2) {
        seen++;
        Rule<ReductionOrder> const* rule2 = *it2;
        for (auto it = rule1->lhs().cend() - 1; it >= rule1->lhs().cbegin();
             --it) {
          // Find longest common prefix of suffix B of rule1.lhs() defined
          // by it and R = rule2.lhs()
          auto prefix = detail::maximum_common_prefix(it,
                                                      rule1->lhs().cend(),
                                                      rule2->lhs().cbegin(),
                                                      rule2->lhs().cend());
          if (prefix.first == rule1->lhs().cend()
              || prefix.second == rule2->lhs().cend()) {
            // Seems that this function isn't called enough to merit using
            // MSV's here.
            word1.assign(rule1->lhs().cbegin(),
                         it);            // A
            word1.append(rule2->rhs());  // S
            word1.append(prefix.first,
                         rule1->lhs().cend());  // D

            word2.assign(rule1->rhs());  // Q
            word2.append(prefix.second,
                         rule2->lhs().cend());  // E

            if (word1 != word2) {
              rewrite(word1);
              rewrite(word2);
              if (word1 != word2) {
                set_cached_confluent(tril::FALSE);
                if (reporting_enabled()) {
                  report_checking_confluence(seen, start_time);
                }
                return false;
              }
            }
          }
        }
      }
    }
    if (reporting_enabled()) {
      report_checking_confluence(seen, start_time);
    }
    return cached_confluent();
  }

  template <typename ReductionOrder>
  bool RewriteFromLeft<ReductionOrder>::process_pending_rules() {
    // TODO(1) try maintaining pending_rules as a heap
    std::sort(this->_pending_rules.begin(),
              this->_pending_rules.end(),
              [](Rule<ReductionOrder> const* x, Rule<ReductionOrder> const* y) {
                return x->lhs() > y->lhs();
              });

    auto           start_time = std::chrono::high_resolution_clock::now();
    detail::Ticker ticker;
    bool           old_ticker_running = this->_ticker_running;

    bool rules_added = false;

    while (number_of_pending_rules() != 0) {
      Rule<ReductionOrder>* rule1 = next_pending_rule();
      LIBSEMIGROUPS_ASSERT(!rule1->active());
      LIBSEMIGROUPS_ASSERT(rule1->lhs() != rule1->rhs());
      // Rewrite both sides and reorder if necessary . . .
      rewrite(rule1);

      // Check rule is non-trivial
      if (rule1->lhs() != rule1->rhs()) {
        native_word_type& lhs = rule1->lhs();

        for (auto it = begin(); it != end();) {
          Rule<ReductionOrder>* rule2 = *it;

          // Check if lhs is contained within either the lhs or rhs of rule2
          // TODO(1) investigate whether or not this can be improved?
          if (rule2->lhs().find(lhs) != native_word_type::npos
              || rule2->rhs().find(lhs) != native_word_type::npos) {
            // If it is, rule2 must be deactivated and re-processed
            it = make_active_rule_pending(it);
          } else {
            ++it;
          }
        }
        add_rule(rule1);
        rules_added = true;
      } else {
        add_inactive_rule(rule1);
      }
      if (!this->_ticker_running && reporting_enabled()
          && delta(start_time) >= std::chrono::seconds(1)) {
        this->_ticker_running = true;
        ticker(
            [this, start_time]() { report_progress_from_thread(start_time); });
      }
    }
    this->_ticker_running = old_ticker_running;
    return rules_added;
  }
}  // namespace libsemigroups::detail
