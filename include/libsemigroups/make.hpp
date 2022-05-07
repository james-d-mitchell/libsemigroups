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

#ifndef LIBSEMIGROUPS_MAKE_HPP_
#define LIBSEMIGROUPS_MAKE_HPP_

#include "froidure-pin-base.hpp"
#include "present.hpp"

namespace libsemigroups {
  template <typename T,
            typename = std::enable_if_t<
                std::is_base_of<PresentationPolymorphicBase, T>::value>>
  T make(FroidurePinBase& fp) {
    using empty_word = typename PresentationPolymorphicBase::empty_word;
    T p(empty_word::no);
    p.alphabet(fp.number_of_generators());
    for (auto it = fp.cbegin_rules(); it != fp.cend_rules(); ++it) {
      p.add_rule(it->first.cbegin(),
                 it->first.cend(),
                 it->second.cbegin(),
                 it->second.cend());
    }

    return p;
  }

  template <typename S,
            typename T,
            typename = std::enable_if_t<
                std::is_base_of<PresentationPolymorphicBase, S>::value
                && std::is_base_of<PresentationPolymorphicBase, T>::value>>
  S make(T const& p) {
    using empty_word = typename PresentationPolymorphicBase::empty_word;
    using word_type  = typename S::word_type;

    S result(p.contains_empty_word() ? empty_word::yes : empty_word::no);
    result.alphabet(p.alphabet().size());
    word_type lhs = {}, rhs = {};
    for (auto it = p.cbegin(); it != p.cend(); ++it) {
      auto to_letter = [&p](auto val) { return p.letter_index(val); };
      lhs.resize(it->size());
      std::transform(it->cbegin(), it->cend(), lhs.begin(), to_letter);
      ++it;
      rhs.resize(it->size());
      std::transform(it->cbegin(), it->cend(), rhs.begin(), to_letter);
      presentation::add_rule(result, lhs, rhs);
      lhs.clear();
      rhs.clear();
    }
    return result;
  }

}  // namespace libsemigroups

#endif  // LIBSEMIGROUPS_MAKE_HPP_
