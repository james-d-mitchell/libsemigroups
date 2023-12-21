//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2023 James D. Mitchell
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

// This file contains a declaration of a class for performing the "low-index
// congruence" algorithm for semigroups and monoid.

#include "libsemigroups/sims2.hpp"

namespace libsemigroups {
  class Sims2::iterator_base::RuleContainer {
   private:
    std::vector<word_type> _words;
    // _used_slots[i] is the length of _words when we have i edges
    std::vector<size_t> _used_slots;

   public:
    RuleContainer()                                = default;
    RuleContainer(RuleContainer const&)            = default;
    RuleContainer(RuleContainer&&)                 = default;
    RuleContainer& operator=(RuleContainer const&) = default;
    RuleContainer& operator=(RuleContainer&&)      = default;

    ~RuleContainer() = default;

    void resize(size_t m) {
      // TODO should we use resize?
      _used_slots.assign(m, UNDEFINED);
      if (m > 0) {
        _used_slots[0] = 0;
      }
      _words.assign(m, word_type());
    }

    word_type& next_rule_word(size_t num_edges) {
      return _words[used_slots(num_edges)++];
    }

    auto begin(size_t) const noexcept {
      return _words.begin();
    }

    auto end(size_t num_edges) noexcept {
      return _words.begin() + used_slots(num_edges);
    }

    void backtrack(size_t num_edges) {
      std::fill(_used_slots.begin() + num_edges,
                _used_slots.end(),
                size_t(UNDEFINED));
      if (num_edges == 0) {
        _used_slots[0] = 0;
      }
    }

   private:
    size_t& used_slots(size_t num_edges) {
      LIBSEMIGROUPS_ASSERT(num_edges < _used_slots.size());
      if (_used_slots[0] == UNDEFINED) {
        _used_slots[0] = 0;
      }
      size_t i = num_edges;
      while (_used_slots[i] == UNDEFINED) {
        --i;
      }
      LIBSEMIGROUPS_ASSERT(i < _used_slots.size());
      LIBSEMIGROUPS_ASSERT(_used_slots[i] != UNDEFINED);
      for (size_t j = i + 1; j <= num_edges; ++j) {
        _used_slots[j] = _used_slots[i];
      }
      LIBSEMIGROUPS_ASSERT(_used_slots[num_edges] <= _words.size());
      return _used_slots[num_edges];
    }
  };

  ///////////////////////////////////////////////////////////////////////////////
  // iterator_base nested class
  ///////////////////////////////////////////////////////////////////////////////

  void
  Sims2::iterator_base::copy_felsch_graph(Sims2::iterator_base const& that) {
    SimsBase::IteratorBase::copy_felsch_graph(that);
    *_2_sided_include = *that._2_sided_include;
    _2_sided_words    = that._2_sided_words;
  }

  Sims2::iterator_base::iterator_base(Sims2 const* s, size_type n)
      : SimsBase::IteratorBase(s, n),
        // protected
        _2_sided_include(new RuleContainer()),
        _2_sided_words() {
    // TODO could be slightly less space allocated here
    size_t const m = SimsBase::IteratorBase::maximum_number_of_classes();
    Presentation<word_type> const& p = this->_felsch_graph.presentation();
    _2_sided_include->resize(2 * m * p.alphabet().size());
    _2_sided_words.assign(n, word_type());
  }

  Sims2::iterator_base::iterator_base(Sims2::iterator_base const& that)
      : SimsBase::IteratorBase(that),
        _2_sided_include(new RuleContainer(*that._2_sided_include)),
        _2_sided_words(that._2_sided_words) {}

  Sims2::iterator_base::iterator_base(Sims2::iterator_base&& that)
      : SimsBase::IteratorBase(std::move(that)),  // TODO std::move correct?
        _2_sided_include(std::move(that._2_sided_include)),
        _2_sided_words(std::move(that._2_sided_words)) {}

  typename Sims2::iterator_base&
  Sims2::iterator_base::operator=(Sims2::iterator_base const& that) {
    SimsBase::IteratorBase::operator=(that);
    *_2_sided_include = *that._2_sided_include;
    _2_sided_words    = that._2_sided_words;

    return *this;
  }

  typename Sims2::iterator_base&
  Sims2::iterator_base::operator=(Sims2::iterator_base&& that) {
    SimsBase::IteratorBase::operator=(std::move(that));  // TODO std::move ok?
    _2_sided_include = std::move(that._2_sided_include);
    _2_sided_words   = std::move(that._2_sided_words);
    return *this;
  }

  void Sims2::iterator_base::swap(Sims2::iterator_base& that) noexcept {
    SimsBase::IteratorBase::swap(that);
    std::swap(_2_sided_include, that._2_sided_include);
    std::swap(_2_sided_words, that._2_sided_words);
  }

  Sims2::iterator_base::~iterator_base() = default;

  bool Sims2::iterator_base::try_define(PendingDef const& current) {
    LIBSEMIGROUPS_ASSERT(current.target < current.num_nodes);
    LIBSEMIGROUPS_ASSERT(current.num_nodes <= maximum_number_of_classes());

    if (!SimsBase::IteratorBase::try_define(current)) {
      return false;
    }

    std::lock_guard lg(_mtx);
    _2_sided_include->backtrack(current.num_edges);

    if (current.target_is_new_node) {
      LIBSEMIGROUPS_ASSERT(current.target < _2_sided_words.size());
      LIBSEMIGROUPS_ASSERT(current.source < _2_sided_words.size());
      _2_sided_words[current.target] = _2_sided_words[current.source];
      _2_sided_words[current.target].push_back(current.generator);
    } else {
      auto const& e = _felsch_graph.definitions()[current.num_edges];
      word_type&  u = _2_sided_include->next_rule_word(current.num_edges);
      u.assign(_2_sided_words[e.first].cbegin(),
               _2_sided_words[e.first].cend());
      u.push_back(e.second);
      word_type&       v = _2_sided_include->next_rule_word(current.num_edges);
      word_type const& w
          = _2_sided_words[_felsch_graph.target_no_checks(e.first, e.second)];
      v.assign(w.begin(), w.end());
    }

    size_type start = current.num_edges;
    while (start < _felsch_graph.definitions().size()) {
      auto first = _2_sided_include->begin(current.num_edges);
      auto last  = _2_sided_include->end(current.num_edges);
      start      = _felsch_graph.definitions().size();
      if (!felsch_graph::make_compatible<RegisterDefs>(
              _felsch_graph,
              0,
              _felsch_graph.number_of_active_nodes(),
              first,
              last)
          || !_felsch_graph.process_definitions(start)) {
        return false;
      }
    }
    return true;
  }

}  // namespace libsemigroups