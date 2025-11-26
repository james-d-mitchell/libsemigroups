//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2023-2025 Joseph Edwards + James D. Mitchell
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
//

#include "libsemigroups/detail/rewriters.hpp"

#include <algorithm>
#include <atomic>
#include <chrono>

#include "libsemigroups/runner.hpp"  // for Ticker

#include "libsemigroups/detail/guard.hpp"   // for Guard
#include "libsemigroups/detail/report.hpp"  // for report_default

namespace libsemigroups {
  namespace detail {

    ////////////////////////////////////////////////////////////////////////
    // RewriteTrie
    ////////////////////////////////////////////////////////////////////////

    RewriteTrie::RewriteTrie()
        : RewriteBase(),
          _new_rule_map(),
          _new_rule_trie(),
          _rewrite_tmp_buf(),
          _rule_map(),
          _rule_trie(0),
          _ticker_running(false) {}

    RewriteTrie::~RewriteTrie() = default;

    RewriteTrie& RewriteTrie::init() {
      RewriteBase::init();
      _rule_map.clear();
      _rule_trie.init();
      // Do nothing to _rewrite_tmp_buf, _new_rule_map, or _new_rule_trie
      return *this;
    }

    RewriteTrie& RewriteTrie::operator=(RewriteTrie const& that) {
      init();
      RewriteBase::operator=(that);
      _rule_trie = that._rule_trie;
      for (Rule<>* rule : *this) {
        index_type node = _rule_trie.traverse_trie_no_checks(
            rule->lhs().cbegin(), rule->lhs().cend());
        LIBSEMIGROUPS_ASSERT(_rule_trie.terminal(node));
        _rule_map.emplace(node, rule);
      }

      return *this;
    }

    // As with RewriteFromLeft::rewrite, this assumes that all rules are
    // length reducing.
    void RewriteTrie::rewrite2(native_word_type& u) {
      // Check if u is rewriteable
      if (u.size() < stats().min_length_lhs_rule) {
        return;
      }

      _rewrite_tmp_buf.clear();
      index_type current = _rule_trie.root;
      _rewrite_tmp_buf.push_back(current);

#ifdef LIBSEMIGROUPS_DEBUG
      iterator v_begin = u.begin();
#endif
      iterator v_end   = u.begin();
      iterator w_begin = v_end;
      iterator w_end   = u.end();

      while (w_begin != w_end) {
        // Read first letter of w and traverse trie
        auto x = *w_begin;
        ++w_begin;
        current = _rule_trie.traverse_no_checks(current,
                                                static_cast<letter_type>(x));

        if (!_rule_trie.node_no_checks(current).terminal()) {
          _rewrite_tmp_buf.push_back(current);
          *v_end = x;
          ++v_end;
        } else {
          auto rule_it = _rule_map.find(current);
          // Find rule that corresponds to terminal node
          Rule<> const* rule     = rule_it->second;
          auto          lhs_size = rule->lhs().size();
          LIBSEMIGROUPS_ASSERT(lhs_size != 0);

          // Check the lhs is smaller than the portion of the word that has
          // been read
          LIBSEMIGROUPS_ASSERT(lhs_size
                               <= static_cast<size_t>(v_end - v_begin) + 1);
          v_end -= lhs_size - 1;
          w_begin -= rule->rhs().size();
          // Replace lhs with rhs in-place
          std::copy(rule->rhs().cbegin(), rule->rhs().cend(), w_begin);
          _rewrite_tmp_buf.erase(_rewrite_tmp_buf.end() - lhs_size + 1,
                                 _rewrite_tmp_buf.end());
          current = _rewrite_tmp_buf.back();
        }
      }
      u.erase(v_end - u.cbegin());
    }

    void RewriteTrie::rewrite(native_word_type& v) {
      // Check if v is rewriteable
      if (v.size() < stats().min_length_lhs_rule) {
        return;
      }

      _rewrite_tmp_buf.clear();
      index_type current = _rule_trie.root;
      _rewrite_tmp_buf.push_back(current);

      std::string w;  // unread suffix of input word
      std::swap(v, w);
      std::reverse(w.begin(), w.end());

      while (!w.empty()) {
        // Read first letter of w and traverse trie
        auto x = w.back();
        w.pop_back();
        current = _rule_trie.traverse_no_checks(current,
                                                static_cast<letter_type>(x));

        if (!_rule_trie.node_no_checks(current).terminal()) {
          _rewrite_tmp_buf.push_back(current);
          v.push_back(x);
        } else {
          Rule<> const* rule = _rule_map.find(current)->second;
          // TODO add comment about off by one
          LIBSEMIGROUPS_ASSERT(rule->lhs().size() <= v.size() + 1);
          v.erase(v.end() - (rule->lhs().size() - 1), v.end());
          w.append(rule->rhs().rbegin(), rule->rhs().rend());
          _rewrite_tmp_buf.erase(_rewrite_tmp_buf.end() - rule->lhs().size()
                                     + 1,
                                 _rewrite_tmp_buf.end());
          current = _rewrite_tmp_buf.back();
        }
      }
    }

    bool RewriteTrie::process_pending_rules() {
      using detail::aho_corasick_impl::begin_search_no_checks;
      using detail::aho_corasick_impl::end_search_no_checks;

      auto           start_time = std::chrono::high_resolution_clock::now();
      detail::Ticker ticker;
      detail::Guard  guard(_ticker_running);
      std::atomic_uint64_t seen = 0;

      // TODO(1) use a heap for these maybe?
      std::sort(
          _pending_rules.begin(),
          _pending_rules.end(),
          [](Rule<> const* x, Rule<> const* y) { return x->lhs() > y->lhs(); });

      bool rules_added = false;
      // TODO(1) could make this a setting, or use a different condition (such
      // as number_of_active_rules / 2 or something)
      bool use_separate_trie
          = number_of_pending_rules() < number_of_active_rules();

      while (number_of_pending_rules() != 0) {
        if (use_separate_trie) {
          _new_rule_trie.init(_rule_trie.alphabet_size());
          _new_rule_map.clear();
        }
        bool rules_added_this_pass = false;
        while (number_of_pending_rules() != 0) {
          Rule<>* rule = next_pending_rule();
          LIBSEMIGROUPS_ASSERT(!rule->active());
          LIBSEMIGROUPS_ASSERT(rule->lhs() != rule->rhs());
          // Rewrite both sides and reorder if necessary . . .
          rewrite(rule);

          if (rule->lhs() != rule->rhs()) {
            add_rule(rule);
            if (use_separate_trie) {
              index_type node = _new_rule_trie.add_word_no_checks(
                  rule->lhs().cbegin(), rule->lhs().cend());
#ifdef LIBSEMIGROUPS_DEBUG
              auto [it, inserted] =
#endif
                  _new_rule_map.emplace(node, rule);
              // Shouldn't be possible for 2 rules with equal left-hand
              // sides to exist, since the later added one will be rewritten
              // using the first.
              LIBSEMIGROUPS_ASSERT(inserted);
            }
            rules_added           = true;
            rules_added_this_pass = true;
          } else {
            add_inactive_rule(rule);
          }
          if (!_ticker_running && reporting_enabled()
              && delta(start_time) >= std::chrono::seconds(1)) {
            _ticker_running = true;
            ticker([this, &start_time, &seen]() {
              report_progress_from_thread(seen, start_time);
            });
          }
        }

        if (rules_added_this_pass) {
          Guard sg(_state);
          _state = State::reducing_pending_rules;

          AhoCorasickImpl* new_rule_trie
              = use_separate_trie ? &_new_rule_trie : &_rule_trie;
          decltype(_rule_map)* rule_map
              = use_separate_trie ? &_new_rule_map : &_rule_map;

          for (auto it = begin(); it != end();) {
            ++seen;
            Rule<>* rule = *it;
            // Check whether any rule contains the left-hand-side of the "new"
            // rule
            bool increment = true;
            for (auto const& word : {rule->lhs(), rule->rhs()}) {
              auto first = begin_search_no_checks(*new_rule_trie, word);
              auto last  = end_search_no_checks(*new_rule_trie, word);

              if (std::any_of(first, last, [rule, rule_map](auto node_index) {
                    return (*rule_map)[node_index] != rule;
                  })) {
                it        = make_active_rule_pending(it);
                increment = false;
                break;
              }
            }
            if (increment) {
              ++it;
            }
            if (!_ticker_running && reporting_enabled()
                && delta(start_time) >= std::chrono::seconds(1)) {
              _ticker_running = true;
              ticker([this, &start_time, &seen]() {
                report_progress_from_thread(seen, start_time);
              });
            }
          }
        }
      }

      return rules_added;
    }

    bool RewriteTrie::confluent_impl(std::atomic_uint64_t& seen) {
      using std::chrono::time_point;
      time_point start_time = std::chrono::high_resolution_clock::now();

      index_type link;
      set_cached_confluent(tril::TRUE);

      // For each rule, check if any descendent of any suffix breaks
      // confluence
      for (auto node_it = _rule_map.begin(); node_it != _rule_map.end();
           ++node_it) {
        seen++;
        link = _rule_trie.suffix_link_no_checks(node_it->first);
        LIBSEMIGROUPS_ASSERT(node_it->first != _rule_trie.root);
        while (link != _rule_trie.root) {
          if (!descendants_confluent(
                  node_it->second, link, _rule_trie.height_no_checks(link))) {
            set_cached_confluent(tril::FALSE);
            report_checking_confluence(seen, start_time);
            return false;
          }
          link = _rule_trie.suffix_link_no_checks(link);
        }
      }

      report_checking_confluence(seen, start_time);
      return true;
    }

    [[nodiscard]] bool
    RewriteTrie::descendants_confluent(Rule<> const* rule1,
                                       index_type    current_node,
                                       size_t        overlap_length) const {
      LIBSEMIGROUPS_ASSERT(rule1->active());
      if (_rule_trie.node_no_checks(current_node).terminal()) {
        Rule<> const* rule2 = _rule_map.find(current_node)->second;
        // Process overlap
        // Word looks like ABC where the LHS of rule1 corresponds to AB,
        // the LHS of rule2 corresponds to BC, and |C|=nodes.size() - 1.
        // AB -> X, BC -> Y
        // ABC gets rewritten to XC and AY
        // TODO(1) remove allocation, use a MultiView, and check equality,
        // then copy inside the if-condition
        native_word_type word1;
        native_word_type word2;

        word1.assign(rule1->rhs());  // X
        word1.append(rule2->lhs().cbegin() + overlap_length,
                     rule2->lhs().cend());  // C

        word2.assign(rule1->lhs().cbegin(),
                     rule1->lhs().cend() - overlap_length);  // A
        word2.append(rule2->rhs());                          // Y

        if (word1 != word2) {
          rewrite(word1);
          rewrite(word2);
          if (word1 != word2) {
            set_cached_confluent(tril::FALSE);
            return false;
          }
        }
        return true;
      }

      // Read each possible letter and traverse down the trie
      for (letter_type x = 0; x != _rule_trie.alphabet_size(); ++x) {
        auto child = _rule_trie.child_no_checks(current_node, x);
        if (child != UNDEFINED) {
          if (!descendants_confluent(rule1, child, overlap_length)) {
            return false;
          }
        }
      }
      return true;
    }

    Rules<>::iterator
    RewriteTrie::make_active_rule_pending(Rules::iterator it) {
      Rule<>* rule = *it;
      rule->deactivate_no_checks();
      add_pending_rule(rule);
      index_type node = _rule_trie.rm_word_no_checks(rule->lhs().cbegin(),
                                                     rule->lhs().cend());
      _rule_map.erase(node);
      return Rules::erase_from_active_rules(it);
    }

    void RewriteTrie::report_checking_confluence(
        std::atomic_uint64_t const&                           seen,
        std::chrono::high_resolution_clock::time_point const& start_time)
        const {
      if (reporting_enabled()) {
        auto total_rules   = Rules::number_of_active_rules();
        auto total_rules_s = detail::group_digits(total_rules);
        auto now           = std::chrono::high_resolution_clock::now();
        auto time          = std::chrono::duration_cast<std::chrono::seconds>(
            now - start_time);
        report_no_prefix("{:-<95}\n", "");
        report_default("KnuthBendix: locally confluent for: {0:>{width}} / "
                       "{1:>{width}} ({2:>4.1f}%) rules ({3}s)\n",
                       detail::group_digits(seen),
                       total_rules_s,
                       (total_rules != 0)
                           ? 100 * static_cast<double>(seen) / total_rules
                           : 100,
                       time.count(),
                       fmt::arg("width", total_rules_s.size()));
      }
    }

    void RewriteTrie::report_reducing_rules(
        std::atomic_uint64_t const&                           seen,
        std::chrono::high_resolution_clock::time_point const& start_time)
        const {
      auto gd = detail::group_digits;
      using detail::string_time;
      if (reporting_enabled()) {
        // TODO(1) This could maybe be better, more like the formatting in
        // "report_progress_from_thread"
        auto total_rules = Rules::number_of_active_rules();
        report_default("KnuthBendix: reducing rules: {0:>{width}} / "
                       "{1:>{width}} ({2:>4.1f}%) ({3})\n",
                       gd(seen),
                       gd(total_rules),
                       (total_rules != 0)
                           ? 100 * static_cast<double>(seen) / total_rules
                           : 100,
                       string_time(delta(start_time)),
                       fmt::arg("width", gd(total_rules).size()));
      }
    }
  }  // namespace detail
}  // namespace libsemigroups
