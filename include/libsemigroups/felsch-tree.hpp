//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2022 James D. Mitchell
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

#ifndef LIBSEMIGROUPS_FELSCH_TREE_HPP_
#define LIBSEMIGROUPS_FELSCH_TREE_HPP_

#include <cstddef>
#include <vector>

#include "constants.hpp"
#include "containers.hpp"
#include "debug.hpp"
#include "types.hpp"

namespace libsemigroups {

  // TODO template of word type

  class FelschTree {
   public:
    using index_type     = size_t;
    using state_type     = size_t;
    using const_iterator = std::vector<index_type>::const_iterator;
    static constexpr state_type initial_state = 0;
    static constexpr state_type final_state   = UNDEFINED;

    explicit FelschTree(size_t n)
        : _automata(n, 1, final_state),
          _index(1, std::vector<index_type>({})),
          _parent(1, state_type(UNDEFINED)),
          _length(0) {}

    FelschTree(FelschTree const&) = default;

    using word_iterator = typename std::vector<word_type>::const_iterator;

    void add_relations(word_iterator first, word_iterator last) {
      size_t number_of_words = 0;
      LIBSEMIGROUPS_ASSERT(rels.size() % 2 == 0);
      for (auto wit = first; wit != last; ++wit) {
        // For every prefix [wit->cbegin(), last)
        for (auto last = wit->cend(); last > wit->cbegin(); --last) {
          // For every suffix [first, last) of the prefix [wit->cbegin(), last)
          for (auto first = wit->cbegin(); first < last; ++first) {
            // Find the maximal suffix of [first, last) that corresponds to
            // an existing state . . .
            auto       it = last - 1;
            state_type s  = initial_state;
            while (_automata.get(s, *it) != final_state && it > first) {
              s = _automata.get(s, *it);
              --it;
            }
            if (_automata.get(s, *it) == final_state) {
              // [it + 1, last) is the maximal suffix of [first, last) that
              // corresponds to the existing state s
              size_t number_of_states = _automata.number_of_rows();
              _automata.add_rows((it + 1) - first);
              _index.resize(_index.size() + ((it + 1) - first), {});
              _parent.resize(_parent.size() + ((it + 1) - first), UNDEFINED);
              while (it >= first) {
                // Add [it, last) as a new state
                _automata.set(s, *it, number_of_states);
                _parent[number_of_states] = s;
                s                         = number_of_states;
                number_of_states++;
                it--;
              }
            }
          }
          // Find the state corresponding to the prefix [wit->cbegin(), last)
          auto       it = last - 1;
          state_type s  = initial_state;
          while (it >= wit->cbegin()) {
            s = _automata.get(s, *it);
            LIBSEMIGROUPS_ASSERT(s != final_state);
            --it;
          }
          index_type m = ((number_of_words % 2) == 0 ? number_of_words
                                                     : number_of_words - 1);
          // The index corresponding to the side of the relation
          // corresponding to the prefix is what's pushed into _index[s], so
          // some care is required when using the return value of this.
          if (!std::binary_search(_index[s].cbegin(), _index[s].cend(), m)) {
            _index[s].push_back(number_of_words);
          }
        }
        number_of_words++;
      }
    }

    void push_back(letter_type x) {
      _length        = 1;
      _current_state = _automata.get(initial_state, x);
    }

    bool push_front(letter_type x) {
      LIBSEMIGROUPS_ASSERT(x < _automata.number_of_cols());
      auto y = _automata.get(_current_state, x);
      if (y != final_state) {
        _length++;
        _current_state = y;
        return true;
      } else {
        return false;
      }
    }

    void pop_front() {
      _length--;
      _current_state = _parent[_current_state];
    }

    const_iterator cbegin() const {
      LIBSEMIGROUPS_ASSERT(_current_state != final_state);
      return _index[_current_state].cbegin();
    }

    const_iterator cend() const {
      LIBSEMIGROUPS_ASSERT(_current_state != final_state);
      return _index[_current_state].cend();
    }

    size_t length() const noexcept {
      return _length;
    }

    size_t number_of_nodes() const noexcept {
      return _parent.size();
    }

    size_t height() const noexcept {
      size_t result = 0;
      for (state_type s = 1; s < _parent.size(); ++s) {
        size_t     h = 0;
        state_type t = s;
        while (t != final_state) {
          h++;
          t = _parent[t];
        }
        result = std::max(h, result);
      }
      return result;
    }

   private:
    using StateTable = detail::DynamicArray2<state_type>;
    StateTable                           _automata;
    state_type                           _current_state;
    std::vector<std::vector<index_type>> _index;
    std::vector<state_type>              _parent;
    size_t                               _length;
  };

}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_FELSCH_TREE_HPP_
