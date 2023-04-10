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

#include <cstddef>      // for size_t
#include <type_traits>  // for enable_if_t, is_base_of

#include "debug.hpp"      // for LIBSEMIGROUPS_ASSERT
#include "digraph.hpp"    // for ActionDigraph
#include "exception.hpp"  // for LIBSEMIGROUPS_EXCEPTION
#include "kambites.hpp"   // for KE
#include "kbe-new.hpp"    // for KBE
#include "tce.hpp"        // for TCE

namespace libsemigroups {
  class FroidurePinBase;  // forward decl
  class ToddCoxeter;
  class KnuthBendix;

  //! Make a FroidurePin object from an ActionDigraph.
  //!
  //! If \f$m\f$ is the number of nodes in an ActionDigraph,
  //! \f$0 \leq a,  b< m\f$, and \f$n\f$ is an edge label, then we define
  //! \f$f: \{a, \ldots, b - 1\} \to \{0, \ldots, n - 1\}\f$ so that \f$(x)f\f$
  //! equals the target of the edge starting at node \f$x\f$ with label \f$n\f$.
  //! In this way, every edge label in an ActionDigraph corresponds to a
  //! transformation of the nodes of the digraph. If \f$\{a, \ldots, b - 1\}f
  //! \subseteq \{a, \ldots, b - 1\}\f$, then \f$f\f$ is a transformation in the
  //! sense of Transf. Assuming that for every edge label of the ActionDigraph
  //! the corresponding \f$f\f$ satisfies \f$\{a, \ldots, b - 1\}f \subseteq
  //! \{a, \ldots, b - 1\}\f$, then this function returns the FroidurePin object
  //! corresponding to the semigroup generated by the set of all such
  //! transformations.
  //!
  //! \tparam S the type of the FroidurePin object being constructed (must be
  //! derived from FroidurePinBase).
  //! \tparam T the type of the nodes of the digraph.
  //!
  //! \param ad the ActionDigraph being used to construct the FroidurePin
  //! object.
  //! \param first the value of \f$a\f$ in the preceding discussion
  //! \param last the value of \f$b\f$ in the preceding discussion
  //!
  //! \returns The constructed FroidurePin object, a value of type \p S.
  //!
  //! \throws LibsemigroupsException if \ref validate(Transf<N, Scalar> const&)
  //! throws for any of the constructed transformations. This can happen if, for
  //! example, the ActionDigraph is not complete (i.e. there exists an edge
  //! label and node for which there is no edge with the given label and given
  //! source) or if there is an edge label such that \f$\{a, \ldots, b - 1\}f
  //! \not\subseteq \{a, \ldots, b - 1\}\f$ for the corresponding \f$f\f$.
  template <typename Element, typename Node>
  FroidurePin<Element> to_froidure_pin(ActionDigraph<Node> const& ad,
                                       size_t                     first,
                                       size_t                     last) {
    using node_type = typename ActionDigraph<Node>::node_type;

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
    FroidurePin<Element> result;
    Element              x(last - first);
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

  //! Make a FroidurePin object from an ActionDigraph.
  //!
  //! Calls `make(ad, 0, ad.number_of_nodes())`; see above.
  template <typename Element, typename Node>
  FroidurePin<Element> to_froidure_pin(ActionDigraph<Node> const& ad) {
    return to_froidure_pin<Element>(ad, 0, ad.number_of_nodes());
  }

  FroidurePin<v3::detail::TCE> to_froidure_pin(ToddCoxeter& tc);
  FroidurePin<v3::detail::KBE> to_froidure_pin(KnuthBendix& tc);

  template <typename String>
  auto to_froidure_pin(Kambites<String>& k) {
    if (k.small_overlap_class() < 4) {
      LIBSEMIGROUPS_EXCEPTION_V3(
          "the small overlap class of the argument must be >= 4, found {}",
          k.small_overlap_class());
    }

    FroidurePin<detail::KE<String>> result(k);

    size_t const n = k.presentation().alphabet().size();
    for (size_t i = 0; i < n; ++i) {
      result.add_generator(detail::KE<String>(k, i));
    }
    return result;
  }

}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_MAKE_FROIDURE_PIN_HPP_