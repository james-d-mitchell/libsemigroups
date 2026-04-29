//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2026 Joseph Edwards + James D. Mitchell
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

#ifndef LIBSEMIGROUPS_DETAIL_RULES_HPP_
#define LIBSEMIGROUPS_DETAIL_RULES_HPP_

#include <algorithm>  // for std::sort
#include <array>      // for array
#include <cstddef>    // for size_t
#include <cstdint>    // for uint64_t
#include <list>       // for list
#include <string>     // for std::string
#include <utility>    // for move
#include <vector>     // for vector

// TODO move these headers to the cpp file, when out of lining Overlaps
#include "libsemigroups/constants.hpp"  // for LIBSEMIGROUPS_ASSERT
#include "string.hpp"

#include "libsemigroups/debug.hpp"  // for LIBSEMIGROUPS_ASSERT

namespace libsemigroups {
  namespace detail {

    ////////////////////////////////////////////////////////////////////////
    // Rule
    ////////////////////////////////////////////////////////////////////////

    class Rule {
     public:
      enum class State : uint8_t { active = 0, inactive = 1, pending = 2 };

      using native_word_type = std::string;

     private:
      native_word_type _lhs;
      native_word_type _rhs;
      State            _state;

     public:
      Rule() : _lhs(), _rhs(), _state(Rule::State::inactive) {}

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

      [[nodiscard]] State state() const noexcept {
        return _state;
      }

      Rule& state(State val) {
        _state = val;
        return *this;
      }
    };  // class Rule

    template <typename ReductionOrder>
    void reorder(Rule* rule) {
      if (ReductionOrder{}(rule->lhs(), rule->rhs())) {
        std::swap(rule->lhs(), rule->rhs());
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // OverlapMeasure
    ////////////////////////////////////////////////////////////////////////

    struct OverlapMeasure {
      [[nodiscard]] virtual size_t
      operator()(Rule const*,
                 Rule const*,
                 std::string::const_iterator const&) const
          = 0;
      virtual ~OverlapMeasure() {}
    };

    struct ABC : OverlapMeasure {
      // TODO to cpp
      [[nodiscard]] size_t
      operator()(Rule const*                        AB,
                 Rule const*                        BC,
                 std::string::const_iterator const& it) const override {
        LIBSEMIGROUPS_ASSERT(AB->state() == Rule::State::active
                             && BC->state() == Rule::State::active);
        LIBSEMIGROUPS_ASSERT(AB->lhs().cbegin() <= it);
        LIBSEMIGROUPS_ASSERT(it < AB->lhs().cend());
        // |A| + |BC|
        return (it - AB->lhs().cbegin()) + BC->lhs().size();
      }
    };

    struct AB_BC : OverlapMeasure {
      // TODO to cpp
      [[nodiscard]] size_t
      operator()(Rule const*                        AB,
                 Rule const*                        BC,
                 std::string::const_iterator const& it) const override {
        LIBSEMIGROUPS_ASSERT(AB->state() == Rule::State::active
                             && BC->state() == Rule::State::active);
        LIBSEMIGROUPS_ASSERT(AB->lhs().cbegin() <= it);
        LIBSEMIGROUPS_ASSERT(it < AB->lhs().cend());
        (void) it;
        // |AB| + |BC|
        return AB->lhs().size() + BC->lhs().size();
      }
    };

    struct MAX_AB_BC : OverlapMeasure {
      // TODO to cpp
      [[nodiscard]] size_t
      operator()(Rule const*                        AB,
                 Rule const*                        BC,
                 std::string::const_iterator const& it) const override {
        LIBSEMIGROUPS_ASSERT(AB->state() == Rule::State::active
                             && BC->state() == Rule::State::active);
        LIBSEMIGROUPS_ASSERT(AB->lhs().cbegin() <= it);
        LIBSEMIGROUPS_ASSERT(it < AB->lhs().cend());
        (void) it;
        // max(|AB|, |BC|)
        return std::max(AB->lhs().size(), BC->lhs().size());
      }
    };

    ////////////////////////////////////////////////////////////////////////
    // Overlap
    ////////////////////////////////////////////////////////////////////////

    struct Overlap {
      // TODO make lhs + rhs actually be the cursors, meaning their type would
      // change to iterator (ask JE if this is okay).
      Rule const* lhs;
      Rule const* rhs;
      size_t      length;

      bool operator==(Overlap const& that) const {
        return lhs == that.lhs && rhs == that.rhs && length == that.length;
      }
    };

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
        size_t   max_pending_rules;
        size_t   min_length_lhs_rule;
        uint64_t total_rules;

        void update_after_active_rule_added(Rules const&);
      };

      // TODO was this a good place to put this:
      // PROS: this is the lowest level place it can be
      // CONS: the whole Overlaps apparatus will be copied in, e.g.,
      // RewritingSystemTrie but not used there, maybe better to be in
      // RewritingSystemSet?
      class Overlaps {
        friend class Rules;

       private:
        std::array<iterator, 2> _cursors;
        Overlap                 _current;
        // TODO this should probably be the only original OverlapMeasure
        size_t                _measure_limit;
        OverlapMeasure const* _measure;
        Rules*                _rules;
        bool                  _swap_current_pair_of_rules;

       public:
        Overlaps()                           = delete;
        Overlaps(Overlaps const&)            = delete;
        Overlaps(Overlaps&&)                 = delete;
        Overlaps& operator=(Overlaps const&) = delete;
        Overlaps& operator=(Overlaps&&)      = delete;
        ~Overlaps()                          = default;

        // TODO should be const*?
        // TODO to cpp
        Overlaps(Rules* rules)
            : _cursors(),
              _current(),
              _measure_limit(POSITIVE_INFINITY),
              _measure(nullptr),
              _rules(rules),
              _swap_current_pair_of_rules(false) {}

        // Uses the Range interface but should not be used as a Range
        [[nodiscard]] Overlap const& get() const noexcept {
          return _current;
        }

        // TODO to cpp
        Overlaps& next() {
          if (!at_end()) {
            if (!find_next_overlap_current_rules()) {
              find_next_pair_of_rules_overlap();
            }
          }
          return *this;
        }

        // TODO check for the other mem fns of Range objects
        [[nodiscard]] bool at_end() const noexcept {
          return _cursors[0] == _rules->active_rules().end();
        }

        ///////////////////////////////////////////////////////////////////////
        // Settings
        ///////////////////////////////////////////////////////////////////////

        [[nodiscard]] OverlapMeasure const& measure() const noexcept {
          return *_measure;
        }

        Overlaps& measure(OverlapMeasure& measure) {
          _measure = &measure;
          return *this;
        }

       private:
        Overlaps& reset() {
          _cursors[0]     = _rules->active_rules().begin();
          _cursors[1]     = _cursors[0];
          _current.lhs    = *_cursors[0];
          _current.rhs    = _current.lhs;
          _current.length = 0;
          next();
          return *this;
        }

        [[nodiscard]] bool
        check_overlap_length(Rule const*                 u,
                             Rule const*                 v,
                             std::string::const_iterator it) {
          return _measure == nullptr || _measure_limit == POSITIVE_INFINITY
                 || (*_measure)(u, v, it) <= _measure_limit;
        }

        // TODO out of line
        [[nodiscard]] bool find_next_overlap_current_rules() {
          constexpr const auto active = Rule::State::active;

          auto const& u = _current.lhs;
          auto const& v = _current.rhs;

          LIBSEMIGROUPS_ASSERT(u->state() == active);
          LIBSEMIGROUPS_ASSERT(v->state() == active);

          auto const& u_lhs = u->lhs();
          auto const& v_lhs = v->lhs();

          auto const lower_limit
              = u_lhs.cend() - std::min(u_lhs.size(), v_lhs.size());

          // TODO check correct
          auto it = _current.lhs->lhs().cend() - _current.length - 1;

          while (it > lower_limit && u->state() == active
                 && v->state() == active && check_overlap_length(u, v, it)) {
            if (is_prefix(v_lhs.cbegin(), v_lhs.cend(), it, u_lhs.cend())) {
              _current.length
                  = static_cast<size_t>(std::distance(it, u_lhs.cend()));
              return true;
            }
            --it;
          }
          return false;
        }

        // TODO out of line
        void find_next_pair_of_rules_overlap() {
          auto& first  = _cursors[0];
          auto& second = _cursors[1];
          if (_swap_current_pair_of_rules) {
            _swap_current_pair_of_rules = false;
            goto swap;
          }

          // TODO write comment about what is going on here
          while (first != _rules->active_rules().end()) {
            while (second != _rules->active_rules().begin()) {
              --second;
              _current.rhs    = *second;
              _current.length = 0;
              if (find_next_overlap_current_rules()) {
                _swap_current_pair_of_rules = true;
                return;
              }
            swap:
              std::swap(_current.lhs, _current.rhs);
              _current.length = 0;
              if (find_next_overlap_current_rules()) {
                return;
              }
            }
            first++;
            if (first != _rules->active_rules().end()) {
              second          = first;
              _current.lhs    = *first;
              _current.rhs    = *second;
              _current.length = 0;
              if (find_next_overlap_current_rules()) {
                return;
              }
            }
          }
        }
      };  // class Overlaps

      std::list<Rule*>   _active_rules;
      std::vector<Rule*> _inactive_rules;
      Overlaps           _overlaps;
      std::vector<Rule*> _pending_rules;
      mutable Stats      _stats;

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

      template <typename Order>
      void sort_pending_rules() {
        std::sort(_pending_rules.begin(),
                  _pending_rules.end(),
                  [](Rule const* x, Rule const* y) {
                    return Order()(x->lhs(), y->lhs());
                  });
      }

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

      // TODO delete
      [[nodiscard]] iterator& cursor(size_t index) {
        LIBSEMIGROUPS_ASSERT(index < _overlaps._cursors.size());
        return _overlaps._cursors[index];
      }

      ////////////////////////////////////////////////////////////////////////
      // Numbers of rules
      ////////////////////////////////////////////////////////////////////////

      [[nodiscard]] size_t number_of_inactive_rules() const noexcept {
        return _inactive_rules.size();
      }

      [[nodiscard]] Stats const& stats() const {
        return _stats;
      }

      ////////////////////////////////////////////////////////////////////////
      // Overlaps
      ////////////////////////////////////////////////////////////////////////

      [[nodiscard]] Overlaps& overlaps() {
        return _overlaps.reset();
      }

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

    template <typename Iterator>
    [[nodiscard]] Rule* Rules::new_rule(Iterator first1,
                                        Iterator last1,
                                        Iterator first2,
                                        Iterator last2) {
      Rule* rule = new_rule();
      rule->lhs().assign(first1, last1);
      rule->rhs().assign(first2, last2);
      return rule;
    }

  }  // namespace detail
}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_DETAIL_RULES_HPP_
