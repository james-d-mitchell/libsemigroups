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

// This file contains the implementation of OverlapIteratorTrie.

#include "libsemigroups/detail/overlap-iterators.hpp"

#include "libsemigroups/constants.hpp"  // for UNDEFINED, operator!=
#include "libsemigroups/debug.hpp"      // for LIBSEMIGROUPS_ASSERT
#include "libsemigroups/types.hpp"      // for letter_type

namespace libsemigroups::detail {

  OverlapIteratorTrie::OverlapIteratorTrie()
      : _current_word_iterator(),
        _last_word_iterator(),
        _index_stack(),
        _overlap(),
        _suffix_index(),
        _suffix_descendent_index(),
        _trie(nullptr),
        _word_index(UNDEFINED) {}

  OverlapIteratorTrie::OverlapIteratorTrie(Trie const& trie)
      : _current_word_iterator(trie.cbegin_terminal_nodes()),
        _last_word_iterator(trie.cend_terminal_nodes()),
        _index_stack(),
        _overlap(),
        _suffix_index(Trie::root),
        _suffix_descendent_index(Trie::root),
        _trie(&trie),
        _word_index(Trie::root) {
    _index_stack.reserve(trie.number_of_nodes());
    operator++();
  }

  // Each value in the range [_first, _last) points to a pair <index, rule>.
  // For each of these pairs, we iteratively follow the suffix link, and
  // then explore all of the descendants of that suffix link using DFS. We
  // keep doing this until the suffix link is the root of the trie. Each
  // descendant of each suffix link will correspond to a critical pair.
  OverlapIteratorTrie& OverlapIteratorTrie::operator++() {
    // Resume any partially-complete dfs
    if (!_index_stack.empty()) {
      if (find_next_descendent()) {
        return *this;
      }
    }

    // Resume any partially-complete travels to the root,
    if (_suffix_index != Trie::root) {
      _suffix_index = _trie->node_no_checks(_suffix_index).suffix_link();
      if (traverse_to_root()) {
        return *this;
      }
    }

    // Start again with a new rule
    while (_current_word_iterator != _last_word_iterator) {
      _word_index = *_current_word_iterator;
      ++_current_word_iterator;

      auto const& node = _trie->node_no_checks(_word_index);

      _overlap.lhs  = node.value();
      _suffix_index = node.suffix_link();
      LIBSEMIGROUPS_ASSERT(node.terminal());

      if (traverse_to_root()) {
        return *this;
      }
    }

    // Indicates that we are finished.
    _word_index = UNDEFINED;
    return *this;
  }
  bool OverlapIteratorTrie::traverse_to_root() {
    while (_suffix_index != Trie::root) {
      if (should_check_descendants(_suffix_index)) {
        _index_stack.emplace_back(_suffix_index);
        if (find_next_descendent()) {
          return true;
        }
      }
      _suffix_index = _trie->node_no_checks(_suffix_index).suffix_link();
    }
    return false;
  }

  // Returns true if any descendent, and hence critical pair, is found.
  bool OverlapIteratorTrie::find_next_descendent() {
    while (!_index_stack.empty()) {
      _suffix_descendent_index = _index_stack.back();
      _index_stack.pop_back();

      // Construct the critical pair
      if (_trie->node_no_checks(_suffix_descendent_index).terminal()) {
        _overlap.rhs = _trie->node_no_checks(_suffix_descendent_index).value();
        _overlap.length = _trie->node_no_checks(_suffix_index).height();
        return true;
      }

      // Explore all children
      for (letter_type x = 0; x < _trie->alphabet_size(); ++x) {
        index_type child_index
            = _trie->child_no_checks(_suffix_descendent_index, x);
        if (child_index != UNDEFINED && should_check_descendants(child_index)) {
          _index_stack.emplace_back(child_index);
        }
      }
    }
    return false;
  }

  bool OverlapIteratorTrie::should_check_descendants(size_t index) {
    return _trie->node_no_checks(_word_index).generation()
               == _trie->generation()
           || _trie->node_no_checks(index).generation() == _trie->generation();
  }
}  // namespace libsemigroups::detail
