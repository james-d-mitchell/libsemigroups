//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2026 James D. Mitchell
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

// This file implements TODO(JE)

#include <cstddef>        // for size_t
#include <unordered_set>  // for unordered_set

#include "debug.hpp"
#include "presentation.hpp"  // for Presentation

#include "detail/containers.hpp"  // for DynamicArray2

namespace libsemigroups {
  // Return the next letter in p.alphabet() with index >= index that is not in
  // result.
  template <typename Word>
  auto next_letter_not_in(Presentation<Word> const& p,
                          size_t                    index,
                          Word const&               result) {
    return std::find_if(p.alphabet().begin() + index,
                        p.alphabet().end(),
                        [&result](auto letter) {
                          return std::find(result.begin(), result.end(), letter)
                                 != result.end();
                        });
  }

  // This function returns the alphabet of p ordered so that the rules of p
  // satisfy x_i -> y_i and x_i >_rpo y_i with respect to the returned
  // alphabet order. The returned alphabet is empty if this fails.
  template <typename Word>
  Word du_narendran_rusinowitch(Presentation<Word> const& p) {
    // TODO static assert this is the same as Presentation<Word>::letter_type
    p.throw_if_bad_alphabet_or_rules();

    size_t const R = p.alphabet().size() + 1;
    size_t const C = p.rules.size();

    detail::DynamicArray2<size_t> suffix_index(C, R);

    std::stack<size_t, std::vector<size_t>> stack;
    stack.push(0);

    Word result;

    while (result.size() < R - 1) {
    start:
      auto r     = result.size();
      auto index = stack.top();
      stack.pop();
      auto it     = next_letter_not_in(p, index, result);
      auto letter = p.letter_no_checks(index);
      for (size_t c = 0; c < C; c += 2) {
        auto   lhs = p.rules[c], rhs = p.rules[c + 1];
        size_t lhs_pos = suffix_index.get(r, c);
        if (lhs_pos == lhs.size() + 1) {
          // This rule is already correctly oriented by the alphabet order in
          // "result".
          LIBSEMIGROUPS_ASSERT(suffix_index.get(r, c + 1) == rhs.size() + 1);
          continue;
        }
        auto   lhs_count = std::count(lhs.begin() + lhs_pos, lhs.end(), letter);
        size_t rhs_pos   = suffix_index.get(r, c + 1);
        auto   rhs_count = std::count(rhs.begin() + rhs_pos, rhs.end(), letter);
        if (lhs_count > rhs_count) {
          // Indicate success
          suffix_index.set(r + 1, c, lhs.size() + 1);
          suffix_index.set(r + 1, c + 1, rhs.size() + 1);
        } else if (lhs_count < rhs_count) {
          ++index;
          auto it = next_letter_not_in(p, index, result);
          if (it == p.alphabet().end()) {
            // Backtrack
            if (r == 0) {
              result.clear();
              return result;
            }
            --r;
            result.pop_back();
            stack.push(index);
          }
          goto start;
        } else {
          auto lhs_it = std::find(lhs.rbegin(), lhs.rend() - lhs_pos, letter);
          suffix_index.set(
              r + 1, c, lhs.size() - std::distance(lhs.rbegin(), lhs_it));
          auto rhs_it = std::find(rhs.rbegin(), rhs.rend() - rhs_pos, letter);
          suffix_index.set(
              r + 1, c + 1, rhs.size() - std::distance(rhs.rbegin(), rhs_it));
        }
      }
      result.push_back(letter);
      stack.push(0);
    }
    return result;
  }

}  // namespace libsemigroups
