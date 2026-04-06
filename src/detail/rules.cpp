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
//

#include "libsemigroups/detail/rules.hpp"

#include <algorithm>  // for max, min, sort
#include <limits>     // for numeric_limits
#include <list>       // for list
#include <vector>     // for swap

namespace libsemigroups {
  namespace detail {

    ////////////////////////////////////////////////////////////////////////
    // Rules::Stats
    ////////////////////////////////////////////////////////////////////////

    Rules::Stats::Stats() noexcept {
      init();
    }

    Rules::Stats& Rules::Stats::init() noexcept {
      max_active_rules    = 0;
      max_length_lhs_rule = 0;
      max_pending_rules   = 0;
      min_length_lhs_rule = std::numeric_limits<size_t>::max();
      total_rules         = 0;
      return *this;
    }

    ////////////////////////////////////////////////////////////////////////
    // Rules - private
    ////////////////////////////////////////////////////////////////////////

    void Rules::init_cursors() {
      for (auto& it : _cursors) {
        it = _active_rules.end();
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // Rules - constructors + initializers
    ////////////////////////////////////////////////////////////////////////

    Rules::Rules()
        : _active_rules(),
          _cursors(),
          _inactive_rules(),
          _pending_rules(),
          _stats() {
      init_cursors();
    }

    Rules& Rules::init() {
      _stats.init();

      for (Rule* rule : _active_rules) {
        add_inactive_rule(rule);
      }
      _active_rules.clear();

      for (Rule* rule : _pending_rules) {
        add_inactive_rule(rule);
      }
      _pending_rules.clear();
      init_cursors();

      return *this;
    }

    Rules& Rules::operator=(Rules const& that) {
      init();
      for (Rule const* rule : that._active_rules) {
        add_active_rule(copy_rule(rule));
      }
      for (Rule const* rule : that._pending_rules) {
        add_pending_rule(copy_rule(rule));
      }
      // NOTE: copy the stats after calling add_active_rule and add_pending_rule
      // because they also set values in the stats, that we don't want to
      // retain. This does some unnecessary work, but we'll optimize that if it
      // is an issue later. A similar comment applies to _cursors.
      _stats = that._stats;
      // It seems to be too hard to keep the cursors alive across copy
      // construction, so we don't try.
      init_cursors();
      return *this;
    }

    Rules& Rules::operator=(Rules&& that) {
      // We swap to ensure that all rules are properly deleted
      std::swap(_active_rules, that._active_rules);
      std::swap(_inactive_rules, that._inactive_rules);
      std::swap(_pending_rules, that._pending_rules);
      // It seems to be too hard to keep the cursors alive across move
      // construction, so we don't try.
      init_cursors();
      _stats = std::move(that._stats);
      return *this;
    }

    Rules::~Rules() {
      for (Rule* rule : _active_rules) {
        delete rule;
      }
      for (Rule* rule : _inactive_rules) {
        delete rule;
      }
      for (Rule* rule : _pending_rules) {
        delete rule;
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // Rules - Adding/modifying rules - public
    ////////////////////////////////////////////////////////////////////////

    void Rules::add_active_rule(Rule* rule) {
      LIBSEMIGROUPS_ASSERT(rule->lhs() != rule->rhs());
      // Don't assert that rule isn't active, because it could be if we are
      // calling this in one of the copy constructors.

      // TODO next 6 lines -> Stats
      _stats.max_length_lhs_rule
          = std::max(_stats.max_length_lhs_rule, rule->lhs().size());
      _stats.max_active_rules
          = std::max(_stats.max_active_rules, active_rules().size());
      _stats.min_length_lhs_rule
          = std::min(_stats.min_length_lhs_rule, rule->lhs().size());

#ifdef LIBSEMIGROUPS_DEBUG
      rule->state(Rule::State::active);
#endif
      _active_rules.push_back(rule);
      for (auto& it : _cursors) {
        if (it == _active_rules.end()) {
          --it;
        }
      }
    }

    void Rules::sort_pending_rules() {
      std::sort(
          _pending_rules.begin(),
          _pending_rules.end(),
          [](Rule const* x, Rule const* y) { return x->lhs() > y->lhs(); });
    }

    Rules::iterator Rules::make_active_rule_pending(iterator it) {
      Rule* rule = *it;
      LIBSEMIGROUPS_ASSERT(rule->state() == Rule::State::active);
      add_pending_rule(rule);

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

    ////////////////////////////////////////////////////////////////////////
    // Rules - Getting rules - public
    ////////////////////////////////////////////////////////////////////////

    Rule* Rules::pop_pending_rule() {
      LIBSEMIGROUPS_ASSERT(_pending_rules.size() != 0);
      Rule* rule = _pending_rules.back();
      _pending_rules.pop_back();
      return rule;
    }

    ////////////////////////////////////////////////////////////////////////
    // Rules - mem fns - private
    ////////////////////////////////////////////////////////////////////////

    Rule* Rules::add_pending_rule(Rule* rule) {
      LIBSEMIGROUPS_ASSERT(rule->lhs() != rule->rhs());
#ifdef LIBSEMIGROUPS_DEBUG
      rule->state(Rule::State::pending);
#endif
      _pending_rules.push_back(rule);
      _stats.max_pending_rules
          = std::max(_stats.max_pending_rules, _pending_rules.size());
      return rule;
    }

    Rule* Rules::copy_rule(Rule const* rule) {
      return new_rule(rule->lhs().cbegin(),
                      rule->lhs().cend(),
                      rule->rhs().cbegin(),
                      rule->rhs().cend());
    }

    Rule* Rules::new_rule() {
      ++_stats.total_rules;
      Rule* rule;
      if (!_inactive_rules.empty()) {
        rule = _inactive_rules.front();
        _inactive_rules.erase(_inactive_rules.begin());
      } else {
        // TODO could add x2 new Rules
        rule = new Rule();
      }
      LIBSEMIGROUPS_ASSERT(rule->state() == Rule::State::inactive);
      return rule;
    }

  }  // namespace detail
}  // namespace libsemigroups
