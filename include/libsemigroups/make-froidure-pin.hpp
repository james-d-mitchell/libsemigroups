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

// TODO(Sims1):
// * iwyu
// * code coverage
// * doc

#ifndef LIBSEMIGROUPS_MAKE_FROIDURE_PIN_HPP_
#define LIBSEMIGROUPS_MAKE_FROIDURE_PIN_HPP_

#include "digraph.hpp"
#include "exception.hpp"
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

  // TODO(Sims1): add test for when first = last
  template <typename S,
            typename T,
            typename
            = std::enable_if_t<std::is_base_of<FroidurePinBase, S>::value>>
  S make(ActionDigraph<T> const& ad, size_t first, size_t last) {
    using node_type    = typename ActionDigraph<T>::node_type;
    using element_type = typename S::element_type;

    if (first > last) {
      LIBSEMIGROUPS_EXCEPTION("the 2nd argument (size_t) must be at most the"
                              " 3rd argument (size_t), found %llu > %llu",
                              first,
                              last);
    } else if (first > ad.number_of_nodes()) {
      LIBSEMIGROUPS_EXCEPTION("the 2nd argument (size_t) must be at most the "
                              "out-degree of the 1st argument (ActionDigraph), "
                              "found %llu > %llu",
                              first,
                              ad.out_degree());
    } else if (last > ad.number_of_nodes()) {
      LIBSEMIGROUPS_EXCEPTION("the 3rd argument (size_t) must be at most the "
                              "out-degree of the 1st argument (ActionDigraph), "
                              "found %llu > %llu",
                              last,
                              ad.out_degree());
    }

    LIBSEMIGROUPS_ASSERT(ad.out_degree() > 0);
    S            result;
    element_type x(last - first);
    // Each label corresponds to a generator of S
    for (node_type lbl = 0; lbl < ad.out_degree(); ++lbl) {
      for (size_t n = first; n < last; ++n) {
        x[n - first] = ad.neighbor(n, lbl) - first;
      }
      // The next loop is required because if element_type is a fixed degree
      // type, such as Transf<5> for example, but first = last = 0, then the
      // degree of x is still 5 not last - first = 0.
      for (size_t n = last - first; n < x.degree(); ++n) {
        x[n] = n;
      }

      validate(x);
      result.add_generator(x);
    }
    return result;
  }

}  // namespace libsemigroups
#endif
