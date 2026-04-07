//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019-2025 James D. Mitchell
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

namespace libsemigroups {
  namespace detail {
    // Implemented in cpp file
    void prefixes_string(std::unordered_map<Rule::native_word_type, size_t>& st,
                         Rule::native_word_type const&                       x,
                         size_t&                                             n);

    ////////////////////////////////////////////////////////////////////////
    // Overlap measures --- KnuthBendixImpl nested classes
    ////////////////////////////////////////////////////////////////////////

    template <typename RewritingSystem, typename ReductionOrder>
    struct KnuthBendixImpl<RewritingSystem, ReductionOrder>::ABC
        : KnuthBendixImpl<RewritingSystem, ReductionOrder>::OverlapMeasure {
      size_t operator()(detail::Rule const*                              AB,
                        detail::Rule const*                              BC,
                        typename native_word_type::const_iterator const& it) {
        LIBSEMIGROUPS_ASSERT(AB->state() == Rule::State::active
                             && BC->state() == Rule::State::active);
        LIBSEMIGROUPS_ASSERT(AB->lhs().cbegin() <= it);
        LIBSEMIGROUPS_ASSERT(it < AB->lhs().cend());
        // |A| + |BC|
        return (it - AB->lhs().cbegin()) + BC->lhs().size();
      }
    };

    template <typename RewritingSystem, typename ReductionOrder>
    struct KnuthBendixImpl<RewritingSystem, ReductionOrder>::AB_BC
        : KnuthBendixImpl<RewritingSystem, ReductionOrder>::OverlapMeasure {
      size_t operator()(detail::Rule const*                              AB,
                        detail::Rule const*                              BC,
                        typename native_word_type::const_iterator const& it) {
        LIBSEMIGROUPS_ASSERT(AB->state() == Rule::State::active
                             && BC->state() == Rule::State::active);
        LIBSEMIGROUPS_ASSERT(AB->lhs().cbegin() <= it);
        LIBSEMIGROUPS_ASSERT(it < AB->lhs().cend());
        (void) it;
        // |AB| + |BC|
        return AB->lhs().size() + BC->lhs().size();
      }
    };

    template <typename RewritingSystem, typename ReductionOrder>
    struct KnuthBendixImpl<RewritingSystem, ReductionOrder>::MAX_AB_BC
        : KnuthBendixImpl<RewritingSystem, ReductionOrder>::OverlapMeasure {
      size_t operator()(detail::Rule const*                              AB,
                        detail::Rule const*                              BC,
                        typename native_word_type::const_iterator const& it) {
        LIBSEMIGROUPS_ASSERT(AB->state() == Rule::State::active
                             && BC->state() == Rule::State::active);
        LIBSEMIGROUPS_ASSERT(AB->lhs().cbegin() <= it);
        LIBSEMIGROUPS_ASSERT(it < AB->lhs().cend());
        (void) it;
        // max(|AB|, |BC|)
        return std::max(AB->lhs().size(), BC->lhs().size());
      }
    };

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendix::Settings - constructor - public
    //////////////////////////////////////////////////////////////////////////

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem,
                    ReductionOrder>::Settings::Settings() noexcept {
      init();
    }

    template <typename RewritingSystem, typename ReductionOrder>
    typename KnuthBendixImpl<RewritingSystem, ReductionOrder>::Settings&
    KnuthBendixImpl<RewritingSystem,
                    ReductionOrder>::Settings::init() noexcept {
      // TODO(1) experiment with starting size to optimise speed.
      max_pending_rules         = 128;  // TODO rm this isn't used currently
      check_confluence_interval = 4'096;
      max_overlap               = POSITIVE_INFINITY;
      max_rules                 = POSITIVE_INFINITY;
      overlap_policy            = options::overlap::ABC;
      return *this;
    }

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::Stats::Stats() noexcept {
      init();
    }

    template <typename RewritingSystem, typename ReductionOrder>
    typename KnuthBendixImpl<RewritingSystem, ReductionOrder>::Stats&
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::Stats::init() noexcept {
      prev_active_rules   = 0;
      prev_inactive_rules = 0;
      prev_total_rules    = 0;
      return *this;
    }

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendixImpl - setters for Settings - public
    //////////////////////////////////////////////////////////////////////////

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>&
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::overlap_policy(
        typename options::overlap p) {
      if (p == _settings.overlap_policy && _overlap_measure != nullptr) {
        return *this;
      }
      switch (p) {
        case options::overlap::ABC:
          _overlap_measure.reset(new ABC());
          break;
        case options::overlap::AB_BC:
          _overlap_measure.reset(new AB_BC());
          break;
        case options::overlap::MAX_AB_BC:
          _overlap_measure.reset(new MAX_AB_BC());
          break;
        default:
          LIBSEMIGROUPS_ASSERT(false);
      }
      _settings.overlap_policy = p;
      return *this;
    }

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendixImpl - constructors and destructor - public
    //////////////////////////////////////////////////////////////////////////

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::KnuthBendixImpl()
        : CongruenceCommon(),
          _gen_pairs_initted(),
          _gilman_graph(),
          _gilman_graph_node_labels(),
          _overlap_measure(nullptr),
          _presentation(),
          _rewriter(),
          _settings(),
          _stats(),
          _tmp_element1() {
      init();
    }

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>&
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::init() {
      CongruenceCommon::init();
      report_prefix("KnuthBendix");

      _gen_pairs_initted = false;
      _gilman_graph.init(0, 0);
      _gilman_graph_node_labels.clear();
      _overlap_measure = nullptr;
      _presentation.init();
      _rewriter.init();
      _settings.init();
      _stats.init();

      // The next line sets _overlap_measure to be something sensible.
      overlap_policy(_settings.overlap_policy);
      return *this;
    }

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>&
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::operator=(
        KnuthBendixImpl const& that) {
      CongruenceCommon::operator=(that);
      _gen_pairs_initted        = that._gen_pairs_initted;
      _gilman_graph             = that._gilman_graph;
      _gilman_graph_node_labels = that._gilman_graph_node_labels;
      _overlap_measure          = nullptr;
      _presentation             = that._presentation;
      _rewriter                 = that._rewriter;
      _settings                 = that._settings;
      _stats                    = that._stats;

      // The next line sets _overlap_measure to be something sensible.
      overlap_policy(_settings.overlap_policy);

      return *this;
    }

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>&
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::operator=(
        KnuthBendixImpl&& that) {
      CongruenceCommon::operator=(std::move(that));
      _gen_pairs_initted        = std::move(that._gen_pairs_initted);
      _gilman_graph             = std::move(that._gilman_graph);
      _gilman_graph_node_labels = std::move(that._gilman_graph_node_labels);
      _overlap_measure          = std::move(that._overlap_measure);
      _presentation             = std::move(that._presentation);
      _rewriter                 = std::move(that._rewriter);
      _settings                 = std::move(that._settings);
      _stats                    = std::move(that._stats);
      return *this;
    }

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::KnuthBendixImpl(
        KnuthBendixImpl&& that)
        : KnuthBendixImpl() {
      operator=(std::move(that));
    }

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::KnuthBendixImpl(
        KnuthBendixImpl const& that)
        : KnuthBendixImpl() {
      operator=(that);
    }

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::~KnuthBendixImpl()
        = default;

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::KnuthBendixImpl(
        congruence_kind                  knd,
        Presentation<native_word_type>&& p)
        : KnuthBendixImpl() {
      init(knd, std::move(p));
    }

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>&
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::init(
        congruence_kind                  knd,
        Presentation<native_word_type>&& p) {
      // TODO(1) assert that the alphabet + rules are good
      // p.throw_if_bad_alphabet_or_rules();
      LIBSEMIGROUPS_ASSERT(presentation::is_normalized(p));
      init();
      kind(knd);
      _presentation = std::move(p);
      init_from_internal_presentation();
      return *this;
    }

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::KnuthBendixImpl(
        congruence_kind                       knd,
        Presentation<native_word_type> const& p)
        : KnuthBendixImpl() {
      init(knd, p);
    }

    template <typename RewritingSystem, typename ReductionOrder>
    KnuthBendixImpl<RewritingSystem, ReductionOrder>&
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::init(
        congruence_kind                       knd,
        Presentation<native_word_type> const& p) {
      // Call rvalue ref init
      return init(knd, Presentation(p));
    }

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendixImpl - attributes - public
    //////////////////////////////////////////////////////////////////////////

    template <typename RewritingSystem, typename ReductionOrder>
    uint64_t
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::number_of_classes() {
      if (is_obviously_infinite(*this)) {
        return POSITIVE_INFINITY;
      }

      int const modifier
          = (internal_presentation().contains_empty_word() ? 0 : -1);
      if (internal_presentation().alphabet().empty()) {
        return 1 + modifier;
      } else {
        uint64_t result = v4::paths::count(gilman_graph(), 0);
        return result == POSITIVE_INFINITY ? result : result + modifier;
      }
    }

    template <typename RewritingSystem, typename ReductionOrder>
    template <typename Iterator1,
              typename Iterator2,
              typename Iterator3,
              typename Iterator4>
    tril KnuthBendixImpl<RewritingSystem, ReductionOrder>::
        currently_contains_no_checks(Iterator1 first1,
                                     Iterator2 last1,
                                     Iterator3 first2,
                                     Iterator4 last2) const {
      if (std::equal(first1, last1, first2, last2)) {
        return tril::TRUE;
      }
      // TODO(1) remove allocations here
      native_word_type w1, w2;
      reduce_no_run_no_checks(std::back_inserter(w1), first1, last1);
      reduce_no_run_no_checks(std::back_inserter(w2), first2, last2);
      if (w1 == w2) {
        return tril::TRUE;
      } else if (finished()
                 || (internal_presentation().rules.empty()
                     && internal_generating_pairs().empty())) {
        return tril::FALSE;
      }
      return tril::unknown;
    }

    template <typename RewritingSystem, typename ReductionOrder>
    template <typename OutputIterator,
              typename InputIterator1,
              typename InputIterator2>
    OutputIterator
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::reduce_no_run_no_checks(
        OutputIterator d_first,
        InputIterator1 first,
        InputIterator2 last) const {
      // TODO(1) improve this to not require _tmp_element1
      if constexpr (std::is_same_v<InputIterator1, char const*>) {
        static_assert(std::is_same_v<InputIterator2, char const*>);
        _tmp_element1.assign(first, std::distance(first, last));
      } else {
        _tmp_element1.assign(first, last);
      }
      const_cast<KnuthBendixImpl<RewritingSystem, ReductionOrder>&>(*this)
          .rewrite_inplace(_tmp_element1);
      return std::copy(
          std::begin(_tmp_element1), std::end(_tmp_element1), d_first);
    }

    // TODO(1) export a version of this for use elsewhere
    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem, ReductionOrder>::report_presentation()
        const {
      // NOTE: this function does the same as presentation::to_report_string,
      // which we cannot use directly here because we don't have a presentation
      // object to pass to it (and possibly because of some cyclic dependency
      // that this would introduce).
      using detail::group_digits;
      size_t min = POSITIVE_INFINITY, max = 0, len = 0;
      for (auto const& rule : _rewriter.rules()) {
        auto rule_len = rule.first.size() + rule.second.size();
        len += rule_len;
        min = (rule_len < min ? rule_len : min);
        max = (rule_len > max ? rule_len : max);
      }
      if (min == POSITIVE_INFINITY) {
        min = 0;
      }

      report_default("KnuthBendix: |A| = {}, |R| = {}, "
                     "|u| + |v| \u2208 [{}, {}], \u2211(|u| + |v|) = {}\n",
                     internal_presentation().alphabet().size(),
                     group_digits(_rewriter.number_of_rules()),
                     group_digits(min),
                     group_digits(max),
                     group_digits(len));
    }

    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem, ReductionOrder>::report_before_run() {
      if (reporting_enabled()) {
        report_no_prefix("{:+<95}\n", "");
        report_default("KnuthBendix: STARTING . . .\n");
        report_no_prefix("{:+<95}\n", "");
        report_presentation();
      }
    }

    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem,
                         ReductionOrder>::report_progress_from_thread() {
      using detail::group_digits;
      using detail::signed_group_digits;
      using std::chrono::duration_cast;

      using high_resolution_clock = std::chrono::high_resolution_clock;

      auto active  = _rewriter.number_of_rules();
      auto defined = _rewriter.stats().total_rules;

      int64_t const active_diff  = active - _stats.prev_active_rules;
      int64_t const defined_diff = defined - _stats.prev_total_rules;

      auto run_time = duration_cast<nanoseconds>(high_resolution_clock::now()
                                                 - start_time());
      auto const mean_defined
          = group_digits(std::pow(10, 9) * static_cast<double>(defined)
                         / run_time.count())
            + "/s";

      detail::ReportCell<4> rc;
      rc.min_width(12);
      rc("KnuthBendix: rules {} (active) | X (inactive) | {} (defined)\n",
         group_digits(active),
         group_digits(defined));

      rc("KnuthBendix: diff  {} (active) | X (inactive) | {} (defined)\n",
         signed_group_digits(active_diff),
         signed_group_digits(defined_diff));

      rc("KnuthBendix: time  {} (total)  | X (killed)   | {} (defined)\n",
         detail::string_time(run_time),
         mean_defined);

      stats_check_point();
    }

    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem, ReductionOrder>::report_after_run() {
      if (reporting_enabled()) {
        report_progress_from_thread();
        if (finished()) {
          using detail::group_digits;
          detail::ReportCell<2> rc;
          rc.min_width(12);
          rc("KnuthBendix: RUN STATISTICS\n");
          rc("KnuthBendix: max number of pending rules {}\n",
             group_digits(_rewriter.stats().max_pending_rules));
          rc("KnuthBendix: max length lhs rule         {}\n",
             group_digits(_rewriter.stats().max_length_lhs_rule));
        }

        report_no_prefix("{:-<95}\n", "");
        report_presentation();

        report_no_prefix("{:+<95}\n", "");
        report_default("KnuthBendix: STOPPING -- ");

        if (finished()) {
          report_no_prefix("finished!\n");
        } else if (dead()) {
          report_no_prefix("killed!\n");
        } else if (timed_out()) {
          report_no_prefix("timed out!\n");
        } else if (stopped_by_predicate()) {
          report_no_prefix("stopped by predicate!\n");
        } else {
          report_no_prefix("max. overlap length of {} reached!\n",
                           max_overlap());
        }
        report_no_prefix("{:+<95}\n", "");
      }
    }

    // report_no_prefix(msg);
    // REVIEW was it okay to remove const here? Needed to do so to maybe process
    // some rules.
    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem, ReductionOrder>::rewrite_inplace(
        native_word_type& w) {
      add_octo(w);
      _rewriter.rewrite(w);
      rm_octo(w);
    }

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendixImpl - other methods - private
    //////////////////////////////////////////////////////////////////////////

    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem, ReductionOrder>::stats_check_point() {
      _stats.prev_active_rules = _rewriter.number_of_rules();
      _stats.prev_total_rules  = _rewriter.stats().total_rules;
    }

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendixImpl - main methods - public
    //////////////////////////////////////////////////////////////////////////

    template <typename RewritingSystem, typename ReductionOrder>
    bool
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::finished_impl() const {
      return _rewriter.confluent_known() && _rewriter.confluent();
    }

    template <typename RewritingSystem, typename ReductionOrder>
    bool
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::stop_running() const {
      return stopped() || _rewriter.number_of_rules() > _settings.max_rules;
    }

    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem,
                         ReductionOrder>::init_from_generating_pairs() {
      if (_gen_pairs_initted) {
        return;
      }
      _gen_pairs_initted = true;

      auto& p     = _presentation;
      auto& pairs = internal_generating_pairs();

      if (kind() == congruence_kind::onesided && !pairs.empty()) {
        LIBSEMIGROUPS_ASSERT(
            p.alphabet().size()
            < std::numeric_limits<typename native_word_type::value_type>::max()
                  - std::numeric_limits<
                      typename native_word_type::value_type>::min());
        p.alphabet(p.alphabet()
                   + static_cast<typename native_word_type::value_type>(
                       p.alphabet().size()));
        _rewriter.increase_alphabet_size_by(1);
      }

      for (auto it = pairs.cbegin(); it != pairs.cend(); ++it) {
        // it points at a word_type
        p.rules.emplace_back(it->cbegin(), it->cend());

        add_octo(p.rules.back());
        ++it;
        p.rules.emplace_back(it->cbegin(), it->cend());
        add_octo(p.rules.back());
        rewriting_system::add_rule(
            _rewriter, p.rules.cend()[-2], p.rules.cend()[-1]);
      }
    }

    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem, ReductionOrder>::run_real() {
      while (!_rewriter.confluent()) {
        if constexpr (is_specialization_of_v<RewritingSystem,
                                             detail::RewritingSystemTrie>) {
          OverlapIteratorTrie       first(_rewriter.trie());
          OverlapIteratorTrie const last;

          while (first != last) {
            if (stop_running()) {
              return;
            }
            Rule const* rule1          = first->lhs;
            Rule const* rule2          = first->rhs;
            size_t      overlap_length = first->length;

            MultiView u(rule1->rhs());
            u.append(rule2->lhs().cbegin() + overlap_length,
                     rule2->lhs().cend());

            MultiView v(rule1->lhs().cbegin(),
                        rule1->lhs().cend() - overlap_length);
            v.append(rule2->rhs().cbegin(), rule2->rhs().cend());

            _rewriter.add_rule(u.begin(), u.end(), v.begin(), v.end());
            ++first;
          }
        } else {
          // _rewriter.rules() calls process_pending_rules, so can't call it
          // inside the rule1 loop below.
          auto rules = _rewriter.rules();
          for (auto rule1 : rules) {
            if (stop_running()) {
              return;
            }
            // WARNING: We cannot call process_pending_rules here, because it
            // messes up the "rules", i.e. makes the corresponding iterators
            // invalid due to adding rules. So, in some examples we accumulate
            // many many pending rules inside these 2 for loops, before they are
            // processed by _rewriter.confluent() above. This makes some tests
            // much slower than they were before (and possibly others faster),
            // e.g. [016]. Hence the 3 lines below, which then makes e.g. [016]
            // run faster but other tests run much much slower. We will fix this
            // later. FIXME

            // else if
            // (_rewriter.break_from_overlap_check()) { break;
            // }
            for (auto rule2 : rules) {
              overlap(rule1, rule2);
            }
          }
        }
      }

      if (_settings.max_overlap == POSITIVE_INFINITY
          && _settings.max_rules == POSITIVE_INFINITY && !stop_running()) {
        _rewriter.set_cached_confluent(tril::TRUE);
      }
    }

    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem, ReductionOrder>::run_impl() {
      stats_check_point();
      reset_start_time();

      init_from_generating_pairs();
      if (_rewriter.confluent() && !stop_running()) {
        // _rewriter._pending_rules can be non-empty if non-reduced rules were
        // used to define the KnuthBendixImpl.  If _rewriter._pending_rules is
        // non-empty, then it means that the rules in _rewriter might not define
        // the system.
        report_default("KnuthBendix: the system is confluent already!\n");
        return;
      } else if (_rewriter.number_of_rules() >= max_rules()) {
        report_default(
            "KnuthBendix: too many rules, found {}, max_rules() is {}\n",
            _rewriter.number_of_rules(),
            max_rules());
        return;
      }

      report_before_run();
      if (reporting_enabled()) {
        detail::Ticker t([&]() { report_progress_from_thread(); },
                         std::chrono::seconds(1));
        run_real();
      } else {
        run_real();
      }

      report_after_run();
    }

    template <typename RewritingSystem, typename ReductionOrder>
    WordGraph<uint32_t> const&
    KnuthBendixImpl<RewritingSystem, ReductionOrder>::gilman_graph() {
      using detail::Rule;
      if (_gilman_graph.number_of_nodes() == 0
          && !internal_presentation().alphabet().empty()) {
        // TODO(1) should implement a SettingsGuard as in ToddCoxeterImpl
        // reset the settings so that we really run!
        max_rules(POSITIVE_INFINITY);
        run();
        LIBSEMIGROUPS_ASSERT(finished());
        LIBSEMIGROUPS_ASSERT(_rewriter.confluent());
        std::unordered_map<Rule::native_word_type, size_t> prefixes;
        prefixes.emplace(Rule::native_word_type(), 0);
        size_t n = 1;
        for (auto const& rule : _rewriter.rules()) {
          detail::prefixes_string(prefixes, rule.first, n);
        }

        _gilman_graph_node_labels.resize(prefixes.size(),
                                         Rule::native_word_type());
        for (auto const& p : prefixes) {
          _gilman_graph_node_labels[p.second] = p.first;
        }

        _gilman_graph.add_nodes(prefixes.size());
        _gilman_graph.add_to_out_degree(
            internal_presentation().alphabet().size());

        for (auto& p : prefixes) {
          for (auto i : internal_presentation().alphabet()) {
            auto s  = p.first + native_word_type({i});
            auto it = prefixes.find(s);
            if (it != prefixes.end()) {
              _gilman_graph.target(p.second, i, it->second);
            } else {
              auto t = s;
              _rewriter.rewrite(t);
              if (t == s) {
                while (!s.empty()) {
                  s  = native_word_type(s.begin() + 1, s.end());
                  it = prefixes.find(s);
                  if (it != prefixes.end()) {
                    _gilman_graph.target(p.second, i, it->second);
                    break;
                  }
                }
              }
            }
          }
        }
        if (kind() != congruence_kind::twosided
            && !internal_generating_pairs().empty()) {
          auto const& p    = internal_presentation();
          auto        octo = p.index(p.alphabet().back());
          auto        src  = _gilman_graph.target_no_checks(0, octo);
          LIBSEMIGROUPS_ASSERT(src != UNDEFINED);
          _gilman_graph.remove_label_no_checks(octo);
          auto nodes = v4::word_graph::nodes_reachable_from(_gilman_graph, src);
          LIBSEMIGROUPS_ASSERT(std::find(nodes.cbegin(), nodes.cend(), src)
                               != nodes.cend());
          // This is a bit awkward, it exists to ensure
          // that node 0 in the induced subdigraph is src.
          std::vector<decltype(src)> sorted_nodes(nodes.cbegin(), nodes.cend());
          // The order which nodes come out of nodes_reachable_from is
          // non-deterministic and so we sort the nodes
          std::sort(sorted_nodes.begin(), sorted_nodes.end());
          if (sorted_nodes[0] != src) {
            std::iter_swap(
                sorted_nodes.begin(),
                std::find(sorted_nodes.begin(), sorted_nodes.end(), src));
          }

          _gilman_graph.induced_subgraph_no_checks(sorted_nodes.cbegin(),
                                                   sorted_nodes.cend());
        }
      }
      return _gilman_graph;
    }

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendixImpl - converting ints <-> string/char - private
    //////////////////////////////////////////////////////////////////////////

    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem, ReductionOrder>::add_octo(
        native_word_type& w) const {
      if (kind() != congruence_kind::twosided
          && !internal_generating_pairs().empty()) {
        w = internal_presentation().alphabet().back() + w;
      }
    }

    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem, ReductionOrder>::rm_octo(
        native_word_type& w) const {
      if (kind() != congruence_kind::twosided
          && !internal_generating_pairs().empty()) {
        LIBSEMIGROUPS_ASSERT(w.front()
                             == internal_presentation().alphabet().back());
        w.erase(w.begin());
      }
    }

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendixImpl - methods for rules - private
    //////////////////////////////////////////////////////////////////////////

    // TODO(1) move this to the single call site
    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem,
                         ReductionOrder>::init_from_internal_presentation() {
      auto const& p = _presentation;

      _rewriter.increase_alphabet_size_by(p.alphabet().size());

      auto const first = p.rules.cbegin();
      auto const last  = p.rules.cend();
      for (auto it = first; it != last; it += 2) {
        auto lhs = *it, rhs = *(it + 1);
        _rewriter.add_rule(lhs.begin(), lhs.end(), rhs.begin(), rhs.end());
      }
    }

    // OVERLAP_2 from Sims, p77
    // TODO move to RewritingSystemSet
    template <typename RewritingSystem, typename ReductionOrder>
    void KnuthBendixImpl<RewritingSystem, ReductionOrder>::overlap(
        rule_const_reference u,
        rule_const_reference v) {
      native_word_type const& ulhs = u.first;
      native_word_type const& vlhs = v.first;
      native_word_type const& urhs = u.second;
      native_word_type const& vrhs = v.second;

      auto const lower_limit = ulhs.cend() - std::min(ulhs.size(), vlhs.size());

      for (auto it = ulhs.cend() - 1;
           it > lower_limit && it < ulhs.cend() && !stop_running();
           --it) {
        //           && (_settings.max_overlap == POSITIVE_INFINITY
        //               || (*_overlap_measure)(u, v, it) <=
        //               _settings.max_overlap);
        // Check if B = [it, ulhs.cend()) is a prefix of v.first
        if (detail::is_prefix(vlhs.cbegin(), vlhs.cend(), it, ulhs.cend())) {
          // u = P_i = AB -> Q_i and v = P_j = BC -> Q_j This version of
          // new_rule does not reorder _rewriter.add_rule(AQ_j, Q_iC);
          detail::MultiView<native_word_type> x(ulhs.cbegin(), it);
          x.append(vrhs.cbegin(), vrhs.cend());
          detail::MultiView<native_word_type> y(urhs.cbegin(), urhs.cend());
          y.append(vlhs.cbegin() + (ulhs.cend() - it),
                   vlhs.cend());  // rule = AQ_j -> Q_iC
          _rewriter.add_rule(x.begin(), x.end(), y.begin(), y.end());
        }
      }
    }
  }  // namespace detail

  template <typename RewritingSystem, typename ReductionOrder>
  std::ostream&
  operator<<(std::ostream&                                             os,
             detail::KnuthBendixImpl<RewritingSystem, ReductionOrder>& kb) {
    os << kb.rewriting_system().rules();
    return os;
  }

  template <typename RewritingSystem, typename ReductionOrder>
  std::string to_human_readable_repr(
      detail::KnuthBendixImpl<RewritingSystem, ReductionOrder>& kb) {
    using detail::group_digits;
    std::string conf, genpairs;
    if (kb.rewriting_system().confluent_known()) {
      conf = "confluent ";
      if (!kb.rewriting_system().confluent()) {
        conf = "non-" + conf;
      }
    }

    return fmt::format(
        "<{}{} KnuthBendix over {} with {} gen. pair{}, {} rule{}>",
        conf,
        kb.kind() == congruence_kind::twosided ? "2-sided" : "1-sided",
        to_human_readable_repr(kb.internal_presentation()),
        group_digits(kb.number_of_generating_pairs()),
        kb.number_of_generating_pairs() == 1 ? "" : "s",
        group_digits(kb.rewriting_system().number_of_rules()),
        kb.rewriting_system().number_of_rules() == 1 ? "" : "s");
  }

}  // namespace libsemigroups
