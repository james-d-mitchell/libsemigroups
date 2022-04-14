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
  // TODO make return type T so that we can see it in the call to make<T>
  template <typename T>
  Presentation<T> make(FroidurePinBase const& fp) {
    Presentation<T> p;
    p.alphabet(fp.number_of_generators());
    for (auto it = fp.cbegin_rules(); it != fp.cend_rules(); ++it) {
      p.add_rule(it->first.cbegin(),
                 it->first.cend(),
                 it->second.cbegin(),
                 it->second.cend());
    }
    return p;
  }

}  // namespace libsemigroups

#endif
