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

#ifndef LIBSEMIGROUPS_MAKE_FROIDURE_PIN_HPP_
#define LIBSEMIGROUPS_MAKE_FROIDURE_PIN_HPP_

#include "digraph.hpp"
#include "froidure-pin.hpp"
#include "transf.hpp"
#include "types.hpp"

namespace libsemigroups {

  template <typename S,
            typename T,
            typename
            = std::enable_if_t<std::is_base_of<FroidurePinBase, S>::value>>
  S make(ActionDigraph<T> const& ad) {
    return make<S>(ad, 0, ad.number_of_nodes());
  }

  template <typename S,
            typename T,
            typename
            = std::enable_if_t<std::is_base_of<FroidurePinBase, S>::value>>
  S make(ActionDigraph<T> const& ad, size_t first, size_t last) {
    using node_type    = typename ActionDigraph<T>::node_type;
    using element_type = typename S::element_type;

    LIBSEMIGROUPS_ASSERT(ad.out_degree() > 0);
    S            result;
    element_type x(last);
    for (node_type lbl = 0; lbl < ad.out_degree(); ++lbl) {
      for (size_t i = 0; i < first; ++i) {
        x[i] = i;  // TODO(Sims1) don't do this, make the transfs act on [first,
                   // last)
      }
      for (size_t i = first; i < last; ++i) {
        x[i] = ad.neighbor(i, lbl);
      }
      validate(x);
      result.add_generator(x);
    }
    return result;
  }

}  // namespace libsemigroups
#endif