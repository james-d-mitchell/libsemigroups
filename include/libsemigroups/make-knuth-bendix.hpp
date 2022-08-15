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

#ifndef LIBSEMIGROUPS_MAKE_KNUTH_BENDIX_HPP_
#define LIBSEMIGROUPS_MAKE_KNUTH_BENDIX_HPP_

#include "knuth-bendix.hpp"  // for KnuthBendix
#include "make-present.hpp"  // for make
#include "present.hpp"       // for Presentation

namespace libsemigroups {
  template <typename T,
            typename = std::enable_if_t<
                std::is_same<fpsemigroup::KnuthBendix, T>::value>>
  T make(Presentation<std::string> const& p) {
    fpsemigroup::KnuthBendix kb;
    kb.set_alphabet(p.alphabet());
    for (auto it = p.rules.cbegin(); it != p.rules.cend(); it += 2) {
      kb.add_rule(*it, *(it + 1));
    }

    return kb;
  }

  template <typename T,
            typename = std::enable_if_t<
                std::is_same<fpsemigroup::KnuthBendix, T>::value>>
  T make(Presentation<word_type> const& p) {
    std::string alphabet(p.alphabet().size(), 0);
    std::iota(alphabet.begin(), alphabet.end(), 97);
    auto pp = make(p, alphabet);
    return make<fpsemigroup::KnuthBendix>(pp);
  }
}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_MAKE_KNUTH_BENDIX_HPP_
