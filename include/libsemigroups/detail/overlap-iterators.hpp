//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2025 Joseph Edwards
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

#ifndef LIBSEMIGROUPS_DETAIL_OVERLAP_ITERATORS_HPP_
#define LIBSEMIGROUPS_DETAIL_OVERLAP_ITERATORS_HPP_

#include <cstddef>   // for size_t
#include <iterator>  // for forward_iterator_tag
#include <vector>    // for vector

#include "aho-corasick-impl.hpp"  // for AhoCorasickImpl
#include "rules.hpp"              // for Rules

namespace libsemigroups::detail {

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

  struct Overlap {
    Rule const* lhs;
    Rule const* rhs;
    size_t      length;

    bool operator==(Overlap const& that) const {
      return lhs == that.lhs && rhs == that.rhs && length == that.length;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // OverlapIteratorTrie
  ////////////////////////////////////////////////////////////////////////

  class OverlapIteratorTrie {
   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type        = Overlap;
    using difference_type   = std::ptrdiff_t;
    using pointer           = value_type const*;
    using reference         = value_type const&;

   private:
    using Trie                 = AhoCorasickImpl;
    using index_type           = typename Trie::index_type;
    using index_const_iterator = typename Trie::terminal_node_const_iterator;

    index_const_iterator    _current_word_iterator;
    index_const_iterator    _last_word_iterator;
    std::vector<index_type> _index_stack;
    value_type              _overlap;
    index_type              _suffix_index;
    index_type              _suffix_descendent_index;
    Trie const*             _trie;
    index_type              _word_index;

   public:
    OverlapIteratorTrie();

    OverlapIteratorTrie(OverlapIteratorTrie const&)            = default;
    OverlapIteratorTrie(OverlapIteratorTrie&&)                 = default;
    OverlapIteratorTrie& operator=(OverlapIteratorTrie const&) = default;
    OverlapIteratorTrie& operator=(OverlapIteratorTrie&&)      = default;

    // TODO(1) init?

    OverlapIteratorTrie(Trie const& trie);

    ~OverlapIteratorTrie() = default;

    pointer operator->() const {
      return &_overlap;
    }

    reference operator*() const {
      return _overlap;
    }

    // Pre-increment
    OverlapIteratorTrie& operator++();

    // Post-increment
    OverlapIteratorTrie operator++(int) {
      OverlapIteratorTrie tmp = *this;
      ++(*this);
      return tmp;
    }

    // TODO(1) This is definitely insufficient for proper comparison, but is
    // enough to tell whether or not we are at the end.
    bool operator==(OverlapIteratorTrie const& that) const {
      return _word_index == that._word_index;
    }

    bool operator!=(OverlapIteratorTrie const& that) const {
      return !(*this == that);
    }

   private:
    // TODO(1) better name
    [[nodiscard]] bool traverse_to_root();

    // Returns true if any descendent, and hence critical pair, is found.
    bool find_next_descendent();

    // A trie is initialised with generation = 0. Each time a batch of nodes is
    // added to the trie, the generation of the trie may be incremented. When a
    // node, n, is added to a trie, the generation of every node from the root
    // to n is set to be the generation of the trie. As a result, the sequence
    // of generations along a path from the root to any node is non-strictly
    // decreasing.
    //
    // When trying to find critical pairs of nodes, we only want to consider
    // pairs where at least one of the nodes is in the most recent generation
    // (i.e. the generation of the trie). This function returns true if:
    // - the generation of the node corresponding to the left-hand side of the
    //   critical pair is equal to the generation of the trie; or
    // - the generation of the node with index <index> is equal to the
    //   generation of the trie.
    // In the latter case, this means that descendants of the node with index
    // <index> may also have the generation equal to that of the trie.
    bool should_check_descendants(size_t index);
  };  // class OverlapIteratorTrie

  ////////////////////////////////////////////////////////////////////////
  // OverlapIteratorRules
  ////////////////////////////////////////////////////////////////////////

  class OverlapIteratorRules {
   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type        = Overlap;
    using difference_type   = std::ptrdiff_t;
    using pointer           = value_type const*;
    using reference         = value_type const&;

   private:
    Rules::iterator*      _first;
    size_t                _max_overlap_measure;
    value_type            _overlap;
    OverlapMeasure const* _overlap_measure;
    Rules*                _rules;
    Rules::iterator*      _second;
    bool                  _swap_current_pair_of_rules;

   public:
    ////////////////////////////////////////////////////////////////////////
    // Constructors
    ////////////////////////////////////////////////////////////////////////

    OverlapIteratorRules()
        : _first(nullptr),
          _max_overlap_measure(),
          _overlap(),
          _overlap_measure(nullptr),
          _rules(nullptr),
          _second(nullptr),
          _swap_current_pair_of_rules() {}

    OverlapIteratorRules(OverlapIteratorRules const&)            = default;
    OverlapIteratorRules(OverlapIteratorRules&&)                 = default;
    OverlapIteratorRules& operator=(OverlapIteratorRules const&) = default;
    OverlapIteratorRules& operator=(OverlapIteratorRules&&)      = default;

    ~OverlapIteratorRules() = default;

    OverlapIteratorRules(Rules& rules, OverlapMeasure const& measure)
        : _first(&rules.cursor(0)),
          _max_overlap_measure(POSITIVE_INFINITY),
          _overlap(),
          _overlap_measure(&measure),
          _rules(&rules),
          _second(&rules.cursor(1)),
          _swap_current_pair_of_rules(false) {
      // _first being _rules->active_rules().end() means that this iterator is
      // at the end
      *_first         = _rules->active_rules().begin();
      _overlap.lhs    = **_first;
      _overlap.rhs    = **_first;
      _overlap.length = 0;
      operator++();
    }

    ////////////////////////////////////////////////////////////////////////
    // Iterator stuff
    ////////////////////////////////////////////////////////////////////////

    [[nodiscard]] pointer operator->() const {
      return &_overlap;
    }

    [[nodiscard]] reference operator*() const {
      return _overlap;
    }

    // Pre-increment
    OverlapIteratorRules& operator++() {
      if (*_first != _rules->active_rules().end()) {
        if (!find_next_overlap_current_rules()) {
          find_next_pair_of_rules_overlap();
        }
      }
      return *this;
    }

    // Post-increment
    OverlapIteratorRules operator++(int) {
      OverlapIteratorRules tmp = *this;
      ++(*this);
      return tmp;
    }

    // TODO(1) This is definitely insufficient for proper comparison, but is
    // enough to tell whether or not we are at the end.
    [[nodiscard]] bool operator==(OverlapIteratorRules const& that) const {
      if (that._first == nullptr && _first == nullptr) {
        return true;
      } else if (that._first == nullptr) {
        return *_first == _rules->active_rules().end();
      } else if (_first == nullptr) {
        return *that._first == that._rules->active_rules().end();
      }
      return _first == that._first;
    }

    [[nodiscard]] bool operator!=(OverlapIteratorRules const& that) const {
      return !(*this == that);
    }

    ////////////////////////////////////////////////////////////////////////
    // Settings
    ////////////////////////////////////////////////////////////////////////

    [[nodiscard]] Rules const& rules() const noexcept {
      return *_rules;
    }

    OverlapIteratorRules& rules(Rules& rules) {
      _rules = &rules;

      _first                      = &rules.cursor(0);
      _overlap.lhs                = **_first;
      _overlap.rhs                = **_first;
      _overlap.length             = 0;
      _second                     = &rules.cursor(1);
      _swap_current_pair_of_rules = false;
      return *this;
    }

    [[nodiscard]] OverlapMeasure const& measure() const noexcept {
      return *_overlap_measure;
    }

    OverlapIteratorRules& measure(OverlapMeasure& measure) {
      _overlap_measure = &measure;
      return *this;
    }

    [[nodiscard]] size_t max_measure() const noexcept {
      return _max_overlap_measure;
    }

    OverlapIteratorRules& max_measure(size_t val) {
      _max_overlap_measure = val;
      return *this;
    }

   private:
    [[nodiscard]] bool check_overlap_length(Rule const*                 u,
                                            Rule const*                 v,
                                            std::string::const_iterator it) {
      // TODO add asserts
      return _max_overlap_measure == POSITIVE_INFINITY
             || (*_overlap_measure)(u, v, it) <= _max_overlap_measure;
    }

    [[nodiscard]] bool find_next_overlap_current_rules() {
      constexpr const auto active = Rule::State::active;

      auto const& u = _overlap.lhs;
      auto const& v = _overlap.rhs;

      LIBSEMIGROUPS_ASSERT(u->state() == active);
      LIBSEMIGROUPS_ASSERT(v->state() == active);

      auto const& u_lhs = u->lhs();
      auto const& v_lhs = v->lhs();

      auto const lower_limit
          = u_lhs.cend() - std::min(u_lhs.size(), v_lhs.size());

      // TODO check correct
      auto it = _overlap.lhs->lhs().cend() - _overlap.length - 1;

      while (it > lower_limit && u->state() == active && v->state() == active
             && check_overlap_length(u, v, it)) {
        if (is_prefix(v_lhs.cbegin(), v_lhs.cend(), it, u_lhs.cend())) {
          _overlap.length
              = static_cast<size_t>(std::distance(it, u_lhs.cend()));
          return true;
        }
        --it;
      }
      return false;
    }

    void find_next_pair_of_rules_overlap() {
      auto& first  = *_first;
      auto& second = *_second;
      if (_swap_current_pair_of_rules) {
        _swap_current_pair_of_rules = false;
        goto swap;
      }

      // TODO write comment about what is going on here
      while (first != _rules->active_rules().end()) {
        while (second != _rules->active_rules().begin()) {
          --second;
          _overlap.rhs    = *second;
          _overlap.length = 0;
          if (find_next_overlap_current_rules()) {
            _swap_current_pair_of_rules = true;
            return;
          }
        swap:
          std::swap(_overlap.lhs, _overlap.rhs);
          _overlap.length = 0;
          if (find_next_overlap_current_rules()) {
            return;
          }
        }
        first++;
        if (first != _rules->active_rules().end()) {
          second          = first;
          _overlap.lhs    = *first;
          _overlap.rhs    = *second;
          _overlap.length = 0;
          if (find_next_overlap_current_rules()) {
            return;
          }
        }
      }
    }
  };  // class OverlapIteratorTrie
}  // namespace libsemigroups::detail

#endif  // LIBSEMIGROUPS_DETAIL_OVERLAP_ITERATORS_HPP_
