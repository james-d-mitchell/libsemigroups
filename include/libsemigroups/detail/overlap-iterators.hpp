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

#include <string_view>    // for string_view
#include <unordered_map>  // for unordered_map

#include "libsemigroups/config.hpp"  // for LIBSEMIGROUPS_DEBUG
#include "libsemigroups/debug.hpp"   // for LIBSEMIGROUPS_ASSERT

#include "aho-corasick-impl.hpp"  // for AhoCorasickImpl
#include "multi-view.hpp"         // for MultiView

namespace libsemigroups::detail {

  ////////////////////////////////////////////////////////////////////////
  // Overlap
  ////////////////////////////////////////////////////////////////////////
  // TODO make this a template rather than only Rule*?
  struct Overlap {
    Rule*  lhs;
    Rule*  rhs;
    size_t length;

    bool operator==(Overlap const& that) const {
      return lhs == that.lhs && rhs == that.rhs && length == that.length;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // OverlapIteratorTrie
  ////////////////////////////////////////////////////////////////////////

  // TODO rm default param
  template <typename Trie = AhoCorasickImpl<Rule*>>
  class OverlapIteratorTrie {
    template <typename OtherTrie>
    friend class OverlapIteratorTrie;

   public:
    using iterator_category = std::input_iterator_tag;
    using value_type        = Overlap;
    using difference_type   = std::ptrdiff_t;
    using pointer           = value_type const*;
    using reference         = value_type const&;

   private:
    using index_type           = typename Trie::index_type;
    using index_const_iterator = typename Trie::terminal_node_const_iterator;

    index_const_iterator _current_word_iterator;
    index_const_iterator _last_word_iterator;

    index_type _word_index;
    index_type _suffix_index;
    index_type _suffix_descendent_index;

    value_type _overlap;

    Trie const* _trie;

    std::vector<index_type> _index_stack;

   public:
    OverlapIteratorTrie()
        : _current_word_iterator(),
          _last_word_iterator(),
          _word_index(UNDEFINED),
          _suffix_index(),
          _suffix_descendent_index(),
          _overlap(),
          _trie(nullptr),
          _index_stack() {};

    // TODO: Use an init rather than setting default values?
    OverlapIteratorTrie(Trie const& trie)
        : _current_word_iterator(trie.cbegin_terminal_nodes()),
          _last_word_iterator(trie.cend_terminal_nodes()),
          _word_index(Trie::root),
          _suffix_index(Trie::root),
          _suffix_descendent_index(Trie::root),
          _overlap(),
          _trie(&trie),
          _index_stack() {
      _index_stack.reserve(trie.number_of_nodes());
      operator++();
    }

    pointer operator->() const {
      return &_overlap;
    }

    reference operator*() const {
      return _overlap;
    }

    // Pre-increment
    // Each value in the range [_first, _last) points to a pair <index, rule>.
    // For each of these pairs, we iteratively follow the suffix link, and
    // then explore all of the descendants of that suffix link using DFS. We
    // keep doing this until the suffix link is the root of the trie. Each
    // descendant of each suffix link will correspond to a critical pair.
    OverlapIteratorTrie& operator++() {
      // Resume any partially-complete dfs
      if (!_index_stack.empty()) {
        if (find_next_descendent()) {
          return *this;
        }
      }

      // Resume any partially-complete travels to the root,
      if (_suffix_index != Trie::root) {
        _suffix_index = _trie->suffix_link_no_checks(_suffix_index);
        if (traverse_to_root()) {
          return *this;
        }
      }

      // Start again with a new rule
      while (_current_word_iterator != _last_word_iterator) {
        _word_index = *_current_word_iterator;
        ++_current_word_iterator;

        _overlap.lhs  = _trie->node_no_checks(_word_index).value.value();
        _suffix_index = _trie->suffix_link_no_checks(_word_index);
        LIBSEMIGROUPS_ASSERT(_trie->terminal(_word_index));

        if (traverse_to_root()) {
          return *this;
        }
      }

      // Indicates that we are finished.
      _word_index = UNDEFINED;
      return *this;
    }

    // Post-increment
    OverlapIteratorTrie operator++(int) {
      OverlapIteratorTrie tmp = *this;
      ++(*this);
      return tmp;
    }

    template <typename OtherRange>
    // TODO: This is definitely insufficient for proper comparison, but is
    // enough to tell whether or not we are at the end.
    bool operator==(OverlapIteratorTrie<OtherRange> const& that) const {
      return _word_index == that._word_index;
    }

    template <typename OtherRange>
    bool operator!=(OverlapIteratorTrie<OtherRange> const& that) const {
      return !(*this == that);
    }

   private:
    // TODO better name
    bool traverse_to_root() {
      while (_suffix_index != Trie::root) {
        _index_stack.emplace_back(_suffix_index);
        if (find_next_descendent()) {
          return true;
        }
        _suffix_index = _trie->suffix_link_no_checks(_suffix_index);
      }
      return false;
    }

    // Returns true if any descendent, and hence critical pair, is found.
    bool find_next_descendent() {
      while (!_index_stack.empty()) {
        _suffix_descendent_index = _index_stack.back();
        _index_stack.pop_back();

        // Construct the critical pair
        if (_trie->terminal_no_checks(_suffix_descendent_index)) {
          _overlap.rhs
              = _trie->node_no_checks(_suffix_descendent_index).value.value();
          _overlap.length = _trie->height_no_checks(_suffix_index);
          return true;
        }

        // Explore all children
        for (letter_type x = 0; x < _trie->alphabet_size(); ++x) {
          index_type child_index
              = _trie->child_no_checks(_suffix_descendent_index, x);
          if (child_index != UNDEFINED) {
            _index_stack.emplace_back(child_index);
          }
        }
      }
      return false;
    }
  };  // class OverlapIteratorTrie
}  // namespace libsemigroups::detail

#endif
