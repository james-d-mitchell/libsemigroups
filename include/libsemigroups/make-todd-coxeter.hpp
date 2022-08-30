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

#ifndef LIBSEMIGROUPS_MAKE_TODD_COXETER_HPP_
#define LIBSEMIGROUPS_MAKE_TODD_COXETER_HPP_

#include "make-present.hpp"  // for make
#include "present.hpp"       // for Presentation
#include "todd-coxeter.hpp"  // for ToddCoxeter

namespace libsemigroups {
  // This is not optimal, the move constructors etc of ToddCoxeter are deleted
  template <typename T,
            typename
            = std::enable_if_t<std::is_same<congruence::ToddCoxeter, T>::value>>
  void make(congruence::ToddCoxeter& tc, Presentation<word_type> const& p) {
    Presentation<word_type> pp(p);
    presentation::normalize_alphabet(pp);
    tc.set_number_of_generators(pp.alphabet().size());
    for (auto it = pp.rules.cbegin(); it != pp.rules.cend(); it += 2) {
      tc.add_pair(*it, *(it + 1));
    }
  }
}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_MAKE_TODD_COXETER_HPP_
