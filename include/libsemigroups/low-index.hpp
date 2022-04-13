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

#ifndef LIBSEMIGROUPS_LOW_INDEX_HPP_
#define LIBSEMIGROUPS_LOW_INDEX_HPP_

#include <cstddef>

#include "collapsible-word-graph.hpp"
#include "coset.hpp"
#include "digraph.hpp"
#include "felsch-tree.hpp"
#include "present.hpp"

// * have an object that can take a presentation (like CongruenceInterface
// or FpSemigroupInterface);
// * the object has cbegin(size_t n), cend(size_t n) mem fns that allow
// iteration through the congruences with at most n classes;
// * these will use some of the code from ToddCoxeter (mostly
// push_definition, and process_deductions (these parts of ToddCoxeter
// should then be refactored out into a separate base class for ToddCoxeter
// + LowIndexCongruences);
// * they perform a DFS trying to fill in the "graph" such that it is
// compatible with the relations. We backtrack when two paths labelled by
// relation words lead to different places. Dereferencing the iterator just
// points to the reference for the "graph", and incrementing continues the
// search for the next "graph"

namespace libsemigroups {
  namespace {

    template <typename T>
    void check_compatibility(ActionDigraph<T> const&        d,
                             Presentation<word_type> const& p) {
      for (size_t i = 0; i < d.number_of_nodes(); ++i) {
        for (auto it = p.cbegin(); it != p.cend(); it += 2) {
          if (action_digraph_helper::follow_path_nc(d, i, *it)
              != action_digraph_helper::follow_path_nc(d, i, *(it + 1))) {
            LIBSEMIGROUPS_EXCEPTION("incompatible digraph!")
          }
        }
      }
    }
  }  // namespace

  class LowIndexCongruences : public detail::CosetManager {
   public:
    using Deduction = std::pair<coset_type, letter_type>;
    struct Edge {
      Edge(coset_type s, letter_type g, coset_type t, size_t e, size_t n)
          : source(s), generator(g), target(t), num_edges(e), num_nodes(n) {}
      coset_type  source;
      letter_type generator;
      coset_type  target;
      size_t num_edges;  // Number of edges in the graph when *this was added to
                         // the stack
      size_t num_nodes;  // Same as above but for nodes
    };
    using PendingDefs = std::vector<Edge>;
    using Deductions  = std::vector<Deduction>;

   private:
    Deductions                     _deduct;
    FelschTree                     _felsch_tree;
    CollapsibleWordGraph<uint32_t> _word_graph;
    Presentation<word_type>        _presentation;
    // TODO stats?

   public:
    LowIndexCongruences(Presentation<word_type> const& p)
        : _deduct(),
          _felsch_tree(p.alphabet().size()),
          _word_graph(),
          _presentation(p) {
      _felsch_tree.add_relations(_presentation.cbegin(), _presentation.cend());
      _word_graph.add_nodes(1);
      _word_graph.add_to_out_degree(number_of_generators());
    }

    size_t number_of_generators() const noexcept {
      return _presentation.alphabet().size();
    }

    CollapsibleWordGraph<uint32_t> const& word_graph() const {
      return _word_graph;
    }

    void reserve(size_t n) {
      size_t m = coset_capacity();
      if (n > m) {
        m = n - m;
        _word_graph.add_nodes(m);
        add_free_cosets(m);
      }
    }

    inline bool push_definition_felsch(coset_type const& c, size_t i) noexcept {
      auto j = (i % 2 == 0 ? i + 1 : i - 1);
      return push_definition_felsch(
          c, *(_presentation.cbegin() + i), *(_presentation.cbegin() + j));
    }

    bool push_definition_felsch(coset_type const& c,
                                word_type const&  u,
                                word_type const&  v) noexcept {
      LIBSEMIGROUPS_ASSERT(is_active_coset(c));
      LIBSEMIGROUPS_ASSERT(!u.empty());
      LIBSEMIGROUPS_ASSERT(!v.empty());
      coset_type x = action_digraph_helper::follow_path_nc(
          _word_graph, c, u.cbegin(), u.cend() - 1);
      if (x == UNDEFINED) {
        return true;
      }
      coset_type y = action_digraph_helper::follow_path_nc(
          _word_graph, c, v.cbegin(), v.cend() - 1);
      if (y == UNDEFINED) {
        return true;
      }
      return push_definition(x, u.back(), y, v.back());
    }

    bool
    push_definition(coset_type x, letter_type a, coset_type y, letter_type b) {
      LIBSEMIGROUPS_ASSERT(is_valid_coset(x));
      LIBSEMIGROUPS_ASSERT(is_valid_coset(y));
      LIBSEMIGROUPS_ASSERT(a < number_of_generators());
      LIBSEMIGROUPS_ASSERT(b < number_of_generators());

      coset_type const xa = _word_graph.unsafe_neighbor(x, a);
      coset_type const yb = _word_graph.unsafe_neighbor(y, b);

      if (xa == UNDEFINED && yb != UNDEFINED) {
        def_edge(x, a, yb);
      } else if (xa != UNDEFINED && yb == UNDEFINED) {
        def_edge(y, b, xa);
      } else if (xa != UNDEFINED && yb != UNDEFINED && xa != yb) {
        return false;
      }
      return true;
    }

   public:
    Presentation<word_type> const& presentation() const noexcept {
      return _presentation;
    }

    coset_type new_coset() {
      if (has_free_cosets()) {
        coset_type const c = new_active_coset();
        // Clear the new coset's row in each table
        _word_graph.clear_sources_and_targets(c);
        return c;
      } else {
        reserve(2 * coset_capacity());
        return new_active_coset();
      }
    }

    bool process_deductions(size_t start) {
      for (size_t i = start; i < _deduct.size(); ++i) {
        auto const& d = _deduct[i];
        if (is_active_coset(d.first)) {
          _felsch_tree.push_back(d.second);
          if (!process_deductions_dfs_v1(d.first)) {
            return false;
          }
        }
      }
      return true;
    }

    bool process_deductions_dfs_v1(coset_type c) {
      for (auto it = _felsch_tree.cbegin(); it < _felsch_tree.cend(); ++it) {
        if (!push_definition_felsch(c, *it)) {
          return false;
        }
      }

      size_t const n = number_of_generators();
      for (size_t x = 0; x < n; ++x) {
        if (_felsch_tree.push_front(x)) {
          coset_type e = _word_graph.first_source(c, x);
          while (e != UNDEFINED) {
            if (!process_deductions_dfs_v1(e)) {
              return false;
            }
            e = _word_graph.next_source(e, x);
          }
          _felsch_tree.pop_front();
        }
      }
      return true;
    }

    inline void def_edge(coset_type c, letter_type x, coset_type d) noexcept {
      LIBSEMIGROUPS_ASSERT(is_valid_coset(c));
      LIBSEMIGROUPS_ASSERT(x < number_of_generators());
      LIBSEMIGROUPS_ASSERT(is_valid_coset(d));
      _deduct.emplace_back(c, x);
      _word_graph.add_edge_nc(c, d, x);
    }

    // Returns the number of right congruences with up to n (inclusive)
    // classes.
    size_t number_of_congruences(size_t n) {
      size_t      nr = 0;
      PendingDefs pending;
      pending.push_back(Edge(0, 0, UNDEFINED, 0, 1));
      pending.push_back(Edge(0, 0, 0, 0, 1));
      while (!pending.empty()) {
      dive:
        auto current = pending.back();
        pending.pop_back();

        // Backtrack if necessary
        while (_deduct.size() > current.num_edges) {
          auto const& p = _deduct.back();
          _word_graph.remove_edge_nc(p.first, p.second);
          _deduct.pop_back();
        }
        while (number_of_cosets_active() > current.num_nodes) {
          free_coset(number_of_cosets_active() - 1);
        }

        LIBSEMIGROUPS_ASSERT(
            _word_graph.unsafe_neighbor(current.source, current.generator)
            == UNDEFINED);
        {
          size_t start = _deduct.size();

          if (current.target != UNDEFINED) {
            def_edge(current.source, current.generator, current.target);
          } else {
            if (number_of_cosets_active() == n) {
              continue;
            }
            def_edge(current.source, current.generator, new_coset());
          }

          if (process_deductions(start)) {
            coset_type  next = current.source;
            letter_type a    = current.generator + 1;
            while (next != first_free_coset()) {
              for (; a < number_of_generators(); ++a) {
                if (_word_graph.unsafe_neighbor(next, a) == UNDEFINED) {
                  pending.emplace_back(next,
                                       a,
                                       UNDEFINED,
                                       _deduct.size(),
                                       number_of_cosets_active());
                  for (coset_type b = _id_coset; b != first_free_coset();
                       b            = next_active_coset(b)) {
                    pending.emplace_back(
                        next, a, b, _deduct.size(), number_of_cosets_active());
                  }
                  goto dive;
                }
              }
              next = next_active_coset(next);
              a    = 0;
            }
            // No undefined edges, word graph is complete
            // check_compatibility(_word_graph, _presentation);
            nr++;
          }
        }
      }
      return nr;
    }
  };

}  // namespace libsemigroups

#endif  // LIBSEMIGROUPS_LOW_INDEX_HPP_
