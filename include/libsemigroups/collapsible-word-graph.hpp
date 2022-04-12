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

#ifndef LIBSEMIGROUPS_WORD_GRAPH_HPP_
#define LIBSEMIGROUPS_WORD_GRAPH_HPP_

#include "digraph.hpp"  // for ActionDigraph

namespace libsemigroups {
  template <typename T>
  class CollapsibleWordGraph : public ActionDigraph<T> {
   public:
    using node_type  = T;
    using size_type  = node_type;
    using table_type = detail::DynamicArray2<node_type>;

    using Coincidence  = std::pair<node_type, node_type>;
    using Coincidences = std::stack<Coincidence>;

    class Deductions;  // Forward declaration

   private:
    table_type _preim_init;
    table_type _preim_next;

   public:
    using ActionDigraph<T>::ActionDigraph;

    explicit CollapsibleWordGraph()
        : ActionDigraph<node_type>(0, 0),
          _preim_init(0, 0, UNDEFINED),
          _preim_next(0, 0, UNDEFINED) {}

    CollapsibleWordGraph(CollapsibleWordGraph&&)      = default;
    CollapsibleWordGraph(CollapsibleWordGraph const&) = default;
    CollapsibleWordGraph& operator=(CollapsibleWordGraph const&) = default;
    CollapsibleWordGraph& operator=(CollapsibleWordGraph&&) = default;

    void add_edge_nc(node_type c, node_type d, letter_type x) noexcept {
      ActionDigraph<node_type>::add_edge_nc(c, d, x);
      add_source(d, x, c);
    }

    void remove_edge_nc(node_type c, letter_type x) noexcept {
      remove_source(this->unsafe_neighbor(c, x), x, c);
      ActionDigraph<node_type>::remove_edge_nc(c, x);
    }

    void add_nodes(size_type m) {
      ActionDigraph<node_type>::add_nodes(m);
      _preim_init.add_rows(m);
      _preim_next.add_rows(m);
    }

    void add_to_out_degree(size_type m) {
      _preim_init.add_cols(m);
      _preim_next.add_cols(m);
      ActionDigraph<node_type>::add_to_out_degree(m);
    }

    void shrink_to_fit(size_type m) {
      restrict(m);
      _preim_init.shrink_rows_to(m);
      _preim_next.shrink_rows_to(m);
    }

    node_type first_source(node_type c, letter_type x) const noexcept {
      return _preim_init.get(c, x);
    }

    node_type next_source(node_type c, letter_type x) const noexcept {
      return _preim_next.get(c, x);
    }

    template <typename TStackDeduct>
    void merge_nodes(Coincidences& coinc,
                     Deductions&   deduct,
                     node_type     min,
                     node_type     max) {
      LIBSEMIGROUPS_ASSERT(min < max);
      for (letter_type i = 0; i < this->out_degree(); ++i) {
        // v -> max is an edge
        node_type v = first_source(max, i);
        while (v != UNDEFINED) {
          auto w = next_source(v, i);
          add_edge_nc(v, min, i);
          TStackDeduct()(&deduct, v, i);
          v = w;
        }

        // Now let <v> be the IMAGE of <max>
        v = unsafe_neighbor(max, i);
        if (v != UNDEFINED) {
          remove_source(v, i, max);
          // Let <u> be the image of <min>, and ensure <u> = <v>
          node_type u = unsafe_neighbor(min, i);
          if (u == UNDEFINED) {
            add_edge_nc(min, v, i);
            TStackDeduct()(&deduct, min, i);
          } else if (u != v) {
            // Add (u,v) to the stack of pairs to be identified
            coinc.emplace(u, v);
          }
        }
      }
    }

#ifdef LIBSEMIGROUPS_DEBUG
    // Is d a source of c under x?
    bool is_source(node_type c, node_type d, letter_type x) const {
      c = first_source(c, x);
      while (c != d && c != UNDEFINED) {
        c = next_source(c, x);
      }
      return c == d;
    }
#endif
    void clear_sources_and_targets(node_type c);

   private:
    // Add d to the list of preimages of c under x, i.e.
    // _word_graph.target(d, x) = c
    void add_source(node_type c, letter_type x, node_type d) noexcept {
      LIBSEMIGROUPS_ASSERT(x < out_degree());
      // c -> e -> ... -->  c -> d -> e -> ..
      _preim_next.set(d, x, _preim_init.get(c, x));
      _preim_init.set(c, x, d);
    }

    void remove_source(node_type cx, letter_type x, node_type d);
    void clear_sources(node_type c);
    void replace_target(node_type c, node_type d, size_t x);
    void replace_source(node_type c, node_type d, size_t x, node_type cx);
  };

  template <typename T>
  void CollapsibleWordGraph<T>::remove_source(node_type   cx,
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
  void CollapsibleWordGraph<T>::clear_sources_and_targets(node_type c) {
    for (letter_type i = 0; i < this->out_degree(); i++) {
      ActionDigraph<T>::add_edge_nc(c, UNDEFINED, i);
      _preim_init.set(c, i, UNDEFINED);
    }
  }

  template <typename T>
  void CollapsibleWordGraph<T>::clear_sources(node_type c) {
    for (letter_type i = 0; i < this->out_degree(); i++) {
      _preim_init.set(c, i, UNDEFINED);
    }
  }

  // All edges of the form e - x -> c are replaced with e - x -> d,
  template <typename T>
  void CollapsibleWordGraph<T>::replace_target(node_type c,
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
  void CollapsibleWordGraph<T>::replace_source(node_type c,
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
#endif  // LIBSEMIGROUPS_WORD_GRAPH_HPP_
