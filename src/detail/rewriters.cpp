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
    // RuleLookup
    ////////////////////////////////////////////////////////////////////////

    // Reverse lex order
    bool RuleLookup::operator<(RuleLookup const& that) const {
      auto it_this = _last - 1;
      auto it_that = that._last - 1;
      while (it_this > _first && it_that > that._first
             && *it_this == *it_that) {
        --it_that;
        --it_this;
      }
      return *it_this < *it_that;
    }

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
    // Rules - constructors + initializers
    ////////////////////////////////////////////////////////////////////////

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

      for (auto& it : _cursors) {
        it = _active_rules.end();
      }
      return *this;
    }

    Rules& Rules::operator=(Rules const& that) {
      init();
      for (Rule const* rule : that._active_rules) {
        add_active_rule(copy_rule(rule));
      }
      for (auto const* rule : that._pending_rules) {
        add_pending_rule(copy_rule(rule));
      }
      // NOTE: copy the stats after calling add_active_rule and add_pending_rule
      // because they also set values in the stats, that we don't want to
      // retain. This does some unnecessary work, but we'll optimize that if it
      // is an issue later. A similar comment applies to _cursors.
      _stats = that._stats;
      for (size_t i = 0; i < _cursors.size(); ++i) {
        _cursors[i] = _active_rules.begin();
        std::advance(
            _cursors[i],
            std::distance(that.active_rules().begin(),
                          static_cast<const_iterator>(that._cursors[i])));
      }
      return *this;
    }

    Rules& Rules::operator=(Rules&& that) {
      // We swap to ensure that all rules are properly deleted
      std::swap(_active_rules, that._active_rules);
      std::swap(_inactive_rules, that._inactive_rules);
      std::swap(_pending_rules, that._pending_rules);
      _cursors = std::move(that._cursors);
      _stats   = std::move(that._stats);
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
    // Rules - get/set rules
    ////////////////////////////////////////////////////////////////////////

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

    Rule* Rules::copy_rule(Rule const* rule) {
      return new_rule(rule->lhs().cbegin(),
                      rule->lhs().cend(),
                      rule->rhs().cbegin(),
                      rule->rhs().cend());
    }

    void Rules::add_active_rule(Rule* rule) {
      LIBSEMIGROUPS_ASSERT(rule->lhs() != rule->rhs());
      // Don't assert that rule isn't active, because it could be if we are
      // calling this in one of the copy constructors.

      // TODO next 6 lines -> Stats
      _stats.max_length_lhs_rule
          = std::max(_stats.max_length_lhs_rule, rule->lhs().size());
      _stats.max_active_rules
          = std::max(_stats.max_active_rules, number_of_active_rules());
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

    size_t Rules::max_length_lhs_active_rule() const {
      size_t result = 0;
      for (Rule const* rule : _active_rules) {
        result = std::max(rule->lhs().size(), result);
      }
      return result;
    }

    Rule* Rules::pop_pending_rule() {
      LIBSEMIGROUPS_ASSERT(_pending_rules.size() != 0);
      Rule* rule = _pending_rules.back();
      _pending_rules.pop_back();
      return rule;
    }

    ////////////////////////////////////////////////////////////////////////
    // RewritingSystemBase - constructors + initializers
    ////////////////////////////////////////////////////////////////////////

    RewritingSystemBase::RewritingSystemBase()
        : Rules(), _cached_confluent(), _confluence_known(), _ticker_running() {
      init();
    }

    RewritingSystemBase& RewritingSystemBase::init() {
      Rules::init();
      _cached_confluent = false;
      _confluence_known = false;
      _ticker_running   = false;
      return *this;
    }

    RewritingSystemBase::RewritingSystemBase(RewritingSystemBase&& that)
        : Rules(std::move(that)),
          _cached_confluent(that._cached_confluent.load()),
          _confluence_known(that._confluence_known.load()),
          _ticker_running(std::move(that._ticker_running)) {}

    RewritingSystemBase&
    RewritingSystemBase::operator=(RewritingSystemBase const& that) {
      Rules::operator=(that);
      _cached_confluent = that._cached_confluent.load();
      _confluence_known = that._confluence_known.load();
      _ticker_running   = that._ticker_running;

      return *this;
    }

    RewritingSystemBase&
    RewritingSystemBase::operator=(RewritingSystemBase&& that) {
      Rules::operator=(std::move(that));
      _cached_confluent = that._cached_confluent.load();
      _confluence_known = that._confluence_known.load();
      _ticker_running   = std::move(that._ticker_running);
      return *this;
    }

    RewritingSystemBase::~RewritingSystemBase() = default;

    ////////////////////////////////////////////////////////////////////////
    // RewritingSystemBase - public mem fns
    ////////////////////////////////////////////////////////////////////////

    void RewritingSystemBase::set_cached_confluent(tril val) const {
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

    bool RewritingSystemBase::confluent() {
      using std::chrono::high_resolution_clock;
      using std::chrono::time_point;

      if (confluent_known()) {
        return RewritingSystemBase::cached_confluent();
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

    void RewritingSystemBase::report_progress_from_thread(
        std::atomic_uint64_t const&                           seen,
        std::chrono::high_resolution_clock::time_point const& start_time) {
      if (_state == State::none) {
        using detail::string_time;
        auto gd       = detail::group_digits;
        auto active   = gd(Rules::number_of_active_rules());
        auto inactive = gd(Rules::number_of_inactive_rules());
        auto pending  = gd(Rules::number_of_pending_rules());
        auto defined  = gd(Rules::stats().total_rules);

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

  }  // namespace detail
}  // namespace libsemigroups
