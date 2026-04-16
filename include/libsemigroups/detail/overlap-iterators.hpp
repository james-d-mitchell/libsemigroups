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

namespace libsemigroups::detail {

  // Forward decl
  class Rule;

  ////////////////////////////////////////////////////////////////////////
  // OverlapIteratorTrie
  ////////////////////////////////////////////////////////////////////////

  class OverlapIteratorTrie {
   public:
    struct Overlap {
      Rule const* lhs;
      Rule const* rhs;
      size_t      length;

      bool operator==(Overlap const& that) const {
        return lhs == that.lhs && rhs == that.rhs && length == that.length;
      }
    };

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
  };  // class OverlapIteratorTrie
}  // namespace libsemigroups::detail

#endif  // LIBSEMIGROUPS_DETAIL_OVERLAP_ITERATORS_HPP_
