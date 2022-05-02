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

// This file contains a declaration of a class for performing the "low-index
// congruence" algorithm for semigroups and monoid.

namespace libsemigroups {
  template <typename T>
  void DigraphWithSources<T>::remove_source(node_type   cx,
                                            letter_type x,
                                            node_type   d) {
    node_type e = _preim_init.get(cx, x);
    if (e == d) {
      _preim_init.set(cx, x, _preim_next.get(d, x));
    } else {
      while (_preim_next.get(e, x) != d) {
        e = _preim_next.get(e, x);
      }
      LIBSEMIGROUPS_ASSERT(_preim_next.get(e, x) == d);
      _preim_next.set(e, x, _preim_next.get(d, x));
    }
  }

  template <typename T>
  void DigraphWithSources<T>::clear_sources_and_targets(node_type c) {
    for (letter_type i = 0; i < this->out_degree(); i++) {
      ActionDigraph<T>::add_edge_nc(c, UNDEFINED, i);
      _preim_init.set(c, i, UNDEFINED);
    }
  }

  template <typename T>
  void DigraphWithSources<T>::clear_sources(node_type c) {
    for (letter_type i = 0; i < this->out_degree(); i++) {
      _preim_init.set(c, i, UNDEFINED);
    }
  }

  // All edges of the form e - x -> c are replaced with e - x -> d,
  template <typename T>
  void DigraphWithSources<T>::replace_target(node_type c,
                                             node_type d,
                                             size_t    x) {
    if (is_active_coset(c)) {
      node_type e = _preim_init.get(c, x);
      while (e != UNDEFINED) {
        LIBSEMIGROUPS_ASSERT(unsafe_neighbor(e, x) == c);
        ActionDigraph<T>::add_edge_nc(e, d, x);
        e = _preim_next.get(e, x);
      }
    }
  }

  template <typename T>
  void DigraphWithSources<T>::replace_source(node_type c,
                                             node_type d,
                                             size_t    x,
                                             node_type cx) {
    if (is_active_coset(c) && cx != UNDEFINED) {
      // Replace c <-- d in preimages of cx, and d is not a preimage of cx
      // under x
      node_type e = _preim_init.get(cx, x);
      if (e == c) {
        _preim_init.set(cx, x, d);
        return;
      }
      while (e != UNDEFINED) {
        node_type f = _preim_next.get(e, x);
        if (f == c) {
          _preim_next.set(e, x, d);
          return;
        }
        e = f;
      }
    }
  }
}  // namespace libsemigroups
