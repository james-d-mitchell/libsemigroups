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
#include "digraph.hpp"
#include "felsch-tree.hpp"
#include "present.hpp"

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

  class LowIndexCongruences {
    using node_type   = uint32_t;
    using letter_type = uint16_t;
    using size_type   = size_t;  // TODO use WordGraph::size_type instead

   private:
    struct Edge {
      Edge(node_type s, letter_type g, node_type t, size_t e, size_t n)
          : source(s), generator(g), target(t), num_edges(e), num_nodes(n) {}
      node_type   source;
      letter_type generator;
      node_type   target;
      size_t num_edges;  // Number of edges in the graph when *this was added to
                         // the stack
      size_t num_nodes;  // Same as above but for nodes
    };

    using Definition         = std::pair<node_type, letter_type>;
    using Definitions        = std::vector<Definition>;
    using PendingDefinitions = std::vector<Edge>;

    Definitions                    _definitions;
    FelschTree                     _felsch_tree;
    size_type                      _num_active_nodes;
    PendingDefinitions             _pending;
    Presentation<word_type>        _presentation;
    CollapsibleWordGraph<uint32_t> _word_graph;
    // TODO stats?

   public:
    LowIndexCongruences(Presentation<word_type> const& p)
        : _definitions(),
          _felsch_tree(p.alphabet().size()),
          _num_active_nodes(1),
          _pending(),
          _presentation(p),
          _word_graph() {
      _felsch_tree.add_relations(_presentation.cbegin(), _presentation.cend());
      _word_graph.add_nodes(1);
      _word_graph.add_to_out_degree(_presentation.alphabet().size());
    }

    CollapsibleWordGraph<uint32_t> const& word_graph() const {
      return _word_graph;
    }

    Presentation<word_type> const& presentation() const noexcept {
      return _presentation;
    }

   private:
    inline void def_edge(node_type c, letter_type x, node_type d) noexcept {
      LIBSEMIGROUPS_ASSERT(c < _num_active_nodes);
      LIBSEMIGROUPS_ASSERT(x < _presentation.alphabet().size());
      LIBSEMIGROUPS_ASSERT(d < _num_active_nodes);
      LIBSEMIGROUPS_ASSERT(_word_graph.unsafe_neighbor(c, x) == UNDEFINED);
      _definitions.emplace_back(c, x);
      _word_graph.add_edge_nc(c, d, x);
    }

    inline bool push_definition_felsch(node_type const& c, size_t i) noexcept {
      auto j = (i % 2 == 0 ? i + 1 : i - 1);
      return push_definition_felsch(
          c, *(_presentation.cbegin() + i), *(_presentation.cbegin() + j));
    }

    bool push_definition_felsch(node_type        c,
                                word_type const& u,
                                word_type const& v) noexcept {
      LIBSEMIGROUPS_ASSERT(c < _num_active_nodes);
      LIBSEMIGROUPS_ASSERT(!u.empty());
      LIBSEMIGROUPS_ASSERT(!v.empty());
      node_type x = action_digraph_helper::follow_path_nc(
          _word_graph, c, u.cbegin(), u.cend() - 1);
      if (x == UNDEFINED) {
        return true;
      }
      node_type y = action_digraph_helper::follow_path_nc(
          _word_graph, c, v.cbegin(), v.cend() - 1);
      if (y == UNDEFINED) {
        return true;
      }
      LIBSEMIGROUPS_ASSERT(x < _num_active_nodes);
      LIBSEMIGROUPS_ASSERT(y < _num_active_nodes);
      LIBSEMIGROUPS_ASSERT(u.back() < _presentation.alphabet().size());
      LIBSEMIGROUPS_ASSERT(v.back() < _presentation.alphabet().size());
      node_type const xa = _word_graph.unsafe_neighbor(x, u.back());
      node_type const yb = _word_graph.unsafe_neighbor(y, v.back());

      if (xa == UNDEFINED && yb != UNDEFINED) {
        def_edge(x, u.back(), yb);
      } else if (xa != UNDEFINED && yb == UNDEFINED) {
        def_edge(y, v.back(), xa);
      } else if (xa != UNDEFINED && yb != UNDEFINED && xa != yb) {
        return false;
      }
      return true;
    }

    bool process_definitions(size_t start) {
      for (size_t i = start; i < _definitions.size(); ++i) {
        auto const& d = _definitions[i];
        if (d.first
            < _num_active_nodes) {  // TODO try removing this check, think it
                                    // always has to be the case
          _felsch_tree.push_back(d.second);
          if (!process_definitions_dfs_v1(d.first)) {
            return false;
          }
        }
      }
      return true;
    }

    bool process_definitions_dfs_v1(node_type c) {
      for (auto it = _felsch_tree.cbegin(); it < _felsch_tree.cend(); ++it) {
        if (!push_definition_felsch(c, *it)) {
          return false;
        }
      }

      size_t const n = _presentation.alphabet().size();
      for (size_t x = 0; x < n; ++x) {
        if (_felsch_tree.push_front(x)) {
          node_type e = _word_graph.first_source(c, x);
          while (e != UNDEFINED) {
            if (!process_definitions_dfs_v1(e)) {
              return false;
            }
            e = _word_graph.next_source(e, x);
          }
          _felsch_tree.pop_front();
        }
      }
      return true;
    }

   public:
    void next(size_t n) {}

    // Returns the number of right congruences with up to n (inclusive)
    // classes.
    size_t number_of_congruences(size_t n) {
      if (_word_graph.number_of_nodes() < n) {
        _word_graph.add_nodes(n - _word_graph.number_of_nodes());
      }

      size_t nr = 0;
      _pending.emplace_back(0, 0, UNDEFINED, 0, 1);
      _pending.emplace_back(0, 0, 0, 0, 1);

      while (!_pending.empty()) {
      dive:
        auto current = _pending.back();
        _pending.pop_back();

        // Backtrack if necessary
        while (_definitions.size() > current.num_edges) {
          auto const& p = _definitions.back();
          _word_graph.remove_edge_nc(p.first, p.second);
          _definitions.pop_back();
        }

        _num_active_nodes = current.num_nodes;

        LIBSEMIGROUPS_ASSERT(
            _word_graph.unsafe_neighbor(current.source, current.generator)
            == UNDEFINED);
        {
          size_t start = _definitions.size();

          if (current.target != UNDEFINED) {
            def_edge(current.source, current.generator, current.target);
          } else {
            if (_num_active_nodes == n) {
              continue;
            }
            def_edge(current.source, current.generator, _num_active_nodes++);
          }

          if (process_definitions(start)) {
            letter_type a = current.generator + 1;
            for (node_type next = current.source; next < _num_active_nodes;
                 ++next) {
              for (; a < _presentation.alphabet().size(); ++a) {
                if (_word_graph.unsafe_neighbor(next, a) == UNDEFINED) {
                  _pending.emplace_back(next,
                                        a,
                                        UNDEFINED,
                                        _definitions.size(),
                                        _num_active_nodes);
                  for (node_type b = 0; b < _num_active_nodes; ++b) {
                    _pending.emplace_back(
                        next, a, b, _definitions.size(), _num_active_nodes);
                  }
                  goto dive;
                }
              }
              a = 0;
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
