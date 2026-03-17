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

// This file contains the implementation of a Rule object containers for Rule
// objects. It also includes rewriter classes that can be used to rewrite
// strings relative to a collection of rules.

#ifndef LIBSEMIGROUPS_DETAIL_REWRITERS_HPP_
#define LIBSEMIGROUPS_DETAIL_REWRITERS_HPP_

#include <atomic>         // for atomic
#include <chrono>         // for time_point
#include <list>           // for list
#include <set>            // for set
#include <string>         // for basic_string, operator==
#include <unordered_map>  // for unordered_map

#include "libsemigroups/config.hpp"  // for LIBSEMIGROUPS_DEBUG
#include "libsemigroups/debug.hpp"   // for LIBSEMIGROUPS_ASSERT
#include "libsemigroups/order.hpp"   // for shortlex_compare
#include "libsemigroups/runner.hpp"  // for delta
#include "libsemigroups/types.hpp"   // for u8string

#include "aho-corasick-impl.hpp"  // for AhoCorasickImpl
#include "multi-view.hpp"         // for MultiView
#include "report.hpp"             // for reporting_enabled
#include "value-guard.hpp"        // for ValueGuard

namespace libsemigroups {
  namespace detail {

    namespace rewriting_system {

      template <typename RewritingSystem, typename Word>
      void add_rule(RewritingSystem& rs, Word const& lhs, Word const& rhs) {
        rs.add_rule(lhs.begin(), lhs.end(), rhs.begin(), rhs.end());
      }

      template <typename Thing>
      struct is_length_decreasing : std::false_type {};

      template <>
      struct is_length_decreasing<ShortLexCompare> : std::true_type {};

      template <typename Thing>
      static constexpr bool is_length_decreasing_v
          = is_length_decreasing<Thing>::value;

      template <typename Thing>
      struct is_terminating : std::false_type {};

      template <>
      struct is_terminating<ShortLexCompare> : std::true_type {};

      template <>
      struct is_terminating<RecursivePathCompare> : std::true_type {};

      template <>
      struct is_terminating<WtShortLexCompare> : std::true_type {};

      template <>
      struct is_terminating<WtLexCompare> : std::true_type {};

      template <typename Thing>
      static constexpr bool is_terminating_v = is_terminating<Thing>::value;

    }  // namespace rewriting_system

    ////////////////////////////////////////////////////////////////////////
    // Rule
    ////////////////////////////////////////////////////////////////////////

    class Rule {
     public:
#ifdef LIBSEMIGROUPS_DEBUG
      enum class State : uint8_t { active = 0, inactive = 1, pending = 2 };
#endif

      using native_word_type = std::string;

     private:
      native_word_type _lhs;
      native_word_type _rhs;
#ifdef LIBSEMIGROUPS_DEBUG
      State _state;
#endif

     public:
      Rule()
          : _lhs(),
            _rhs()
#ifdef LIBSEMIGROUPS_DEBUG
            ,
            _state(Rule::State::inactive)
#endif
      {
      }

      Rule& operator=(Rule const& copy) = delete;
      Rule(Rule const& copy)            = delete;
      Rule(Rule&& copy)                 = delete;
      Rule& operator=(Rule&& copy)      = delete;

      ~Rule() = default;

      [[nodiscard]] native_word_type const& lhs() const noexcept {
        return _lhs;
      }

      [[nodiscard]] native_word_type const& rhs() const noexcept {
        return _rhs;
      }

      [[nodiscard]] native_word_type& lhs() noexcept {
        return _lhs;
      }

      [[nodiscard]] native_word_type& rhs() noexcept {
        return _rhs;
      }

#ifdef LIBSEMIGROUPS_DEBUG
      [[nodiscard]] State state() const noexcept {
        return _state;
      }

      Rule& state(State val) {
        _state = val;
        return *this;
      }
#endif
    };  // class Rule

    template <typename ReductionOrder>
    void reorder(Rule* rule) {
      if (ReductionOrder{}(rule->lhs(), rule->rhs())) {
        std::swap(rule->lhs(), rule->rhs());
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // RuleLookup
    ////////////////////////////////////////////////////////////////////////

    class RuleLookup {
     public:
      using native_word_type = Rule::native_word_type;

      RuleLookup() : _rule(nullptr) {}

      explicit RuleLookup(Rule* rule)
          : _first(rule->lhs().cbegin()),
            _last(rule->lhs().cend()),
            _rule(rule) {}

      RuleLookup& operator()(native_word_type::iterator first,
                             native_word_type::iterator last) {
        _first = first;
        _last  = last;
        return *this;
      }

      Rule const* rule() const {
        return _rule;
      }

      // This implements reverse lex comparison of this and that, which
      // satisfies the requirement of std::set that equivalent items be
      // incomparable, so, for example bcbc and abcbc are considered
      // equivalent, but abcba and bcbc are not.
      bool operator<(RuleLookup const& that) const;

     private:
      native_word_type::const_iterator _first;
      native_word_type::const_iterator _last;
      Rule const*                      _rule;
    };  // class RuleLookup

    ////////////////////////////////////////////////////////////////////////
    // Rules
    ////////////////////////////////////////////////////////////////////////

    class Rules {
     public:
      using iterator               = std::list<Rule*>::iterator;
      using const_iterator         = std::list<Rule*>::const_iterator;
      using const_reverse_iterator = std::list<Rule*>::const_reverse_iterator;

     private:
      struct Stats {
        Stats() noexcept;
        Stats& init() noexcept;

        Stats(Stats const&) noexcept            = default;
        Stats(Stats&&) noexcept                 = default;
        Stats& operator=(Stats const&) noexcept = default;
        Stats& operator=(Stats&&) noexcept      = default;

        size_t   max_active_rules;
        size_t   max_length_lhs_rule;
        size_t   max_pending_rules;  // TODO(1) rename
        size_t   min_length_lhs_rule;
        uint64_t total_rules;
      };

      std::list<Rule*>        _active_rules;
      std::array<iterator, 2> _cursors;  // TODO(1) rm?
      std::list<Rule*>        _inactive_rules;
      std::vector<Rule*>      _pending_rules;
      mutable Stats           _stats;

      // TODO(1) try maintaining pending_rules as a heap?

      void init_cursors();

     public:
      ////////////////////////////////////////////////////////////////////////
      // Constructors and initializers
      ////////////////////////////////////////////////////////////////////////

      Rules();
      Rules& init();

      // This is currently not used anywhere, because we go through the
      // copy/move assignment operators (so no RewritingSystem calls these
      // functions in their copy/move constructors).
      Rules(Rules const& that) : Rules() {
        *this = that;
      }

      // This is currently not used anywhere, because we go through the
      // copy/move assignment operators (so no RewritingSystem calls these
      // functions in their copy/move constructors).
      Rules(Rules&& that) : Rules() {
        *this = std::move(that);
      }

      Rules& operator=(Rules const&);
      Rules& operator=(Rules&& that);

      ~Rules();

      ////////////////////////////////////////////////////////////////////////
      // Adding/modifying rules
      ////////////////////////////////////////////////////////////////////////

      template <typename Iterator>
      Rule* add_pending_rule(Iterator first1,
                             Iterator last1,
                             Iterator first2,
                             Iterator last2) {
        return add_pending_rule(new_rule(first1, last1, first2, last2));
      }

      void add_active_rule(Rule* rule);

      void add_inactive_rule(Rule* rule) {
#ifdef LIBSEMIGROUPS_DEBUG
        rule->state(Rule::State::inactive);
#endif
        _inactive_rules.push_back(rule);
      }

      void sort_pending_rules();

      [[nodiscard]] iterator make_active_rule_pending(iterator it);

      ////////////////////////////////////////////////////////////////////////
      // Getting rules
      ////////////////////////////////////////////////////////////////////////

      [[nodiscard]] std::list<Rule*> const& active_rules() const noexcept {
        return _active_rules;
      }

      [[nodiscard]] std::list<Rule*>& active_rules() noexcept {
        return _active_rules;
      }

      [[nodiscard]] std::vector<Rule*> const& pending_rules() const noexcept {
        return _pending_rules;
      }

      [[nodiscard]] std::vector<Rule*>& pending_rules() noexcept {
        return _pending_rules;
      }

      [[nodiscard]] Rule* pop_pending_rule();

      // TODO(1) remove?
      [[nodiscard]] iterator& cursor(size_t index) {
        LIBSEMIGROUPS_ASSERT(index < _cursors.size());
        return _cursors[index];
      }

      ////////////////////////////////////////////////////////////////////////
      // Numbers of rules
      ////////////////////////////////////////////////////////////////////////

      [[nodiscard]] size_t number_of_active_rules() const noexcept {
        return _active_rules.size();
      }

      [[nodiscard]] size_t number_of_inactive_rules() const noexcept {
        return _inactive_rules.size();
      }

      [[nodiscard]] size_t number_of_pending_rules() const noexcept {
        return _pending_rules.size();
      }

      [[nodiscard]] Stats const& stats() const {
        return _stats;
      }

      // TODO helper
      [[nodiscard]] size_t max_length_lhs_active_rule() const;

     private:
      Rule* add_pending_rule(Rule* rule);

      [[nodiscard]] Rule* copy_rule(Rule const* rule);
      [[nodiscard]] Rule* new_rule();

      template <typename Iterator>
      [[nodiscard]] Rule* new_rule(Iterator first1,
                                   Iterator last1,
                                   Iterator first2,
                                   Iterator last2);
    };  // class Rules

    ////////////////////////////////////////////////////////////////////////
    // RewritingSystemBase
    ////////////////////////////////////////////////////////////////////////

    class RewritingSystemBase : protected Rules {
     private:
      mutable std::atomic<bool> _cached_confluent;
      mutable std::atomic<bool> _confluence_known;

     protected:
      enum class State : uint8_t {
        none,
        adding_pending_rules,  // TODO rm this?
        reducing_pending_rules,
        checking_confluence
      };

      struct Settings {
        size_t max_pending_rules = 512;
      };

      Settings _settings;
      State    _state;
      bool     _ticker_running;

     public:
      using native_word_type = Rule::native_word_type;
      using rule_const_reference
          = std::pair<native_word_type const&, native_word_type const&>;

      ////////////////////////////////////////////////////////////////////////
      // Constructors + inits
      ////////////////////////////////////////////////////////////////////////

      RewritingSystemBase();
      RewritingSystemBase& init();

      RewritingSystemBase(RewritingSystemBase const& that)
          : RewritingSystemBase() {
        *this = that;
      }

      RewritingSystemBase(RewritingSystemBase&& that) : RewritingSystemBase() {
        *this = std::move(that);
      }

      RewritingSystemBase& operator=(RewritingSystemBase const& that);
      RewritingSystemBase& operator=(RewritingSystemBase&& that);

      virtual ~RewritingSystemBase();

      using Rules::stats;

      ////////////////////////////////////////////////////////////////////////
      // Public mem fns
      ////////////////////////////////////////////////////////////////////////

      [[nodiscard]] size_t number_of_rules() const noexcept {
        return Rules::number_of_pending_rules()
               + Rules::number_of_active_rules();
      }

      [[nodiscard]] auto rules() const {
        // TODO use stringviews rather than references
        return chain(active_rules(), pending_rules())
               | rx::transform([](Rule const* rule) -> rule_const_reference {
                   return rule_const_reference(rule->lhs(), rule->rhs());
                 });
      }

      // Some rewriters require knowledge of the alphabet size, and some do
      // not. For those that do not we provide a default implementation that
      // does nothing.
      RewritingSystemBase& increase_alphabet_size_by(size_t) {
        return *this;
      }

      [[nodiscard]] bool confluent();

      bool cached_confluent() const noexcept {
        return _cached_confluent;
      }

      void set_cached_confluent(tril val) const;

      [[nodiscard]] bool confluent_known() const {
        return _confluence_known;
      }

      template <typename Subclass>
      [[nodiscard]] tril is_length_decreasing() const noexcept {
        if constexpr (rewriting_system::is_length_decreasing_v<
                          typename Subclass::reduction_order>) {
          return tril::TRUE;
        }

        for (Rule const* rule : active_rules()) {
          if (rule->lhs().size() <= rule->rhs().size()) {
            return tril::FALSE;
          }
        }

        return (number_of_pending_rules() == 0) ? tril::TRUE : tril::unknown;
      }

      template <typename Subclass>
      [[nodiscard]] tril is_terminating() const noexcept {
        if constexpr (rewriting_system::is_terminating_v<
                          typename Subclass::reduction_order>) {
          return tril::TRUE;
        }
        if (is_length_decreasing<Subclass>() == tril::TRUE) {
          return tril::TRUE;
        }
        return tril::unknown;
      }

     protected:
      ////////////////////////////////////////////////////////////////////////
      // Member functions - protected
      ////////////////////////////////////////////////////////////////////////

      void report_progress_from_thread(
          std::atomic_uint64_t const&                           seen,
          std::chrono::high_resolution_clock::time_point const& start_time);

      void report_progress_from_thread(
          std::chrono::high_resolution_clock::time_point const& start_time) {
        report_progress_from_thread(0, start_time);
      }

     private:
      [[nodiscard]] virtual bool confluent_impl(std::atomic_uint64_t& seen) = 0;

      virtual void report_checking_confluence(
          std::atomic_uint64_t const&                           seen,
          std::chrono::high_resolution_clock::time_point const& start_time)
          const
          = 0;

      virtual void report_reducing_rules(
          std::atomic_uint64_t const&,
          std::chrono::high_resolution_clock::time_point const&) const {}
    };  // class RewritingSystemBase

    ////////////////////////////////////////////////////////////////////////
    // RewritingSystemSet
    ////////////////////////////////////////////////////////////////////////

    // TODO remove default template param
    template <typename ReductionOrder = ShortLexCompare>
    class RewritingSystemSet : public RewritingSystemBase {
      ////////////////////////////////////////////////////////////////////////
      // Private aliases
      ////////////////////////////////////////////////////////////////////////
      using iterator = Rules::iterator;

      ////////////////////////////////////////////////////////////////////////
      // Private data
      ////////////////////////////////////////////////////////////////////////
      std::set<RuleLookup> _set_rules;

     public:
      ////////////////////////////////////////////////////////////////////////
      // Public aliases
      ////////////////////////////////////////////////////////////////////////

      using native_word_type     = Rule::native_word_type;
      using reduction_order      = ReductionOrder;
      using rule_const_reference = RewritingSystemBase::rule_const_reference;

      ////////////////////////////////////////////////////////////////////////
      // Constructors + initializers
      ////////////////////////////////////////////////////////////////////////

      RewritingSystemSet() = default;
      RewritingSystemSet& init();

      RewritingSystemSet(RewritingSystemSet const& that)
          : RewritingSystemSet() {
        *this = that;
      }
      RewritingSystemSet(RewritingSystemSet&&) = default;

      RewritingSystemSet& operator=(RewritingSystemSet const&);
      RewritingSystemSet& operator=(RewritingSystemSet&&) = default;

      ~RewritingSystemSet();

      ////////////////////////////////////////////////////////////////////////
      // Public member functions --- from RewritingSystemBase
      ////////////////////////////////////////////////////////////////////////

      using RewritingSystemBase::number_of_rules;

      ////////////////////////////////////////////////////////////////////////
      // Public member functions - alphabetical order
      ////////////////////////////////////////////////////////////////////////

      template <typename Iterator>
      RewritingSystemSet& add_rule(Iterator first1,
                                   Iterator last1,
                                   Iterator first2,
                                   Iterator last2);

      [[nodiscard]] tril is_length_decreasing() const noexcept {
        return RewritingSystemBase::is_length_decreasing<
            RewritingSystemSet<ReductionOrder>>();
      }

      [[nodiscard]] tril is_terminating() const noexcept {
        return RewritingSystemBase::is_terminating<
            RewritingSystemSet<ReductionOrder>>();
      }

      // TODO nodiscard or is the return value used for anything?
      bool reduce_system();

      // TODO it'd be possible to check if we encounter a cycle in rewriting,
      // which we could then use to say is_terminating is false
      void rewrite(native_word_type& u);
      void rewrite2(native_word_type& u);

      // TODO the next function shouldn't be necessary, i.e. make things
      // mutable
      void rewrite(native_word_type& u) const {
        const_cast<RewritingSystemSet*>(this)->rewrite(u);
      }

     private:
      ////////////////////////////////////////////////////////////////////////
      // Private member functions
      ////////////////////////////////////////////////////////////////////////

      void     add_active_rule(Rule* rule);
      iterator rm_active_rule(iterator it);

      void rewrite_no_reduce_system(native_word_type& u) const;

      ////////////////////////////////////////////////////////////////////////
      // Confluence
      ////////////////////////////////////////////////////////////////////////

      [[nodiscard]] bool confluent_impl(std::atomic_uint64_t&) override;

      ////////////////////////////////////////////////////////////////////////
      // Reporting
      ////////////////////////////////////////////////////////////////////////

      void report_checking_confluence(
          std::atomic_uint64_t const&,
          std::chrono::high_resolution_clock::time_point const&) const override;
    };  // RewritingSystemSet

    ////////////////////////////////////////////////////////////////////////
    // RewritingSystemTrie
    ////////////////////////////////////////////////////////////////////////

    // TODO remove first 2 default template param
    template <typename ReductionOrder = ShortLexCompare,
              typename Trie           = AhoCorasickImpl<Rule*>>
    class RewritingSystemTrie : public RewritingSystemBase {
      ////////////////////////////////////////////////////////////////////////
      // Private aliases
      ////////////////////////////////////////////////////////////////////////

      using iterator = Rules::iterator;
      // TODO
      using index_type = AhoCorasickImpl<Rule*>::index_type;

      ////////////////////////////////////////////////////////////////////////
      // Private data
      ////////////////////////////////////////////////////////////////////////

      Trie                            _new_rule_trie;
      Trie                            _rule_trie;
      bool                            _ticker_running;
      mutable std::vector<index_type> _trie_nodes_visited_indices;

     public:
      ////////////////////////////////////////////////////////////////////////
      // Public aliases
      ////////////////////////////////////////////////////////////////////////

      using native_word_type     = Rule::native_word_type;
      using rule_const_reference = RewritingSystemBase::rule_const_reference;
      using reduction_order      = ReductionOrder;

      ////////////////////////////////////////////////////////////////////////
      // Constructors + initializers
      ////////////////////////////////////////////////////////////////////////

      RewritingSystemTrie();
      RewritingSystemTrie& init();

      RewritingSystemTrie(RewritingSystemTrie const& that)
          : RewritingSystemTrie() {
        *this = that;
      }
      RewritingSystemTrie(RewritingSystemTrie&& that) = default;

      RewritingSystemTrie& operator=(RewritingSystemTrie const& that);
      RewritingSystemTrie& operator=(RewritingSystemTrie&& that) = default;

      ~RewritingSystemTrie();

      ////////////////////////////////////////////////////////////////////////
      // Public member functions --- from RewritingSystemBase
      ////////////////////////////////////////////////////////////////////////

      using RewritingSystemBase::number_of_rules;

      ////////////////////////////////////////////////////////////////////////
      // Public member functions - alphabetical order
      ////////////////////////////////////////////////////////////////////////

      template <typename Iterator>
      RewritingSystemTrie& add_rule(Iterator first1,
                                    Iterator last1,
                                    Iterator first2,
                                    Iterator last2);

      RewritingSystemTrie& increase_alphabet_size_by(size_t val) {
        _rule_trie.increase_alphabet_size_by(val);
        return *this;
      }

      [[nodiscard]] tril is_length_decreasing() const noexcept {
        return RewritingSystemBase::is_length_decreasing<
            RewritingSystemTrie<ReductionOrder>>();
      }

      [[nodiscard]] tril is_terminating() const noexcept {
        return RewritingSystemBase::is_terminating<
            RewritingSystemTrie<ReductionOrder>>();
      }

      // TODO nodiscard or is the return value used for anything?
      bool reduce_system();

      // TODO(1) iterators
      void rewrite(native_word_type& u);
      void rewrite2(native_word_type& u);

      // TODO shouldn't be necessary
      void rewrite(native_word_type& u) const {
        const_cast<RewritingSystemTrie*>(this)->rewrite(u);
      }

      [[nodiscard]] AhoCorasickImpl<Rule*> const& trie() const noexcept {
        return _rule_trie;
      }

     private:
      ////////////////////////////////////////////////////////////////////////
      // Private member functions
      ////////////////////////////////////////////////////////////////////////

      void     add_active_rule(Rule* new_rule);
      iterator rm_active_rule(iterator it);

      void rewrite_no_reduce_system(native_word_type& u) const;

      ////////////////////////////////////////////////////////////////////////
      // Confluence
      ////////////////////////////////////////////////////////////////////////

      [[nodiscard]] bool descendants_confluent(Rule const* rule1,
                                               index_type  current_node,
                                               size_t backtrack_depth) const;

      [[nodiscard]] bool confluent_impl(std::atomic_uint64_t&) override;

      ////////////////////////////////////////////////////////////////////////
      // Reporting
      ////////////////////////////////////////////////////////////////////////

      void report_checking_confluence(
          std::atomic_uint64_t const&,
          std::chrono::high_resolution_clock::time_point const&) const override;

      void report_reducing_rules(
          std::atomic_uint64_t const&,
          std::chrono::high_resolution_clock::time_point const&) const override;
    };

  }  // namespace detail
}  // namespace libsemigroups

#include "rewriters.tpp"
#endif  // LIBSEMIGROUPS_DETAIL_REWRITERS_HPP_
