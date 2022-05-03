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

// This file contains a declaration of a class called FelschDigraph which is
// used by the classes Sims1, Sims2, and ToddCoxeter.
//

#ifndef LIBSEMIGROUPS_FELSCH_DIGRAPH_HPP_
#define LIBSEMIGROUPS_FELSCH_DIGRAPH_HPP_

#include <cstddef>

#include "digraph-with-sources.hpp"
#include "digraph.hpp"
#include "felsch-tree.hpp"
#include "present.hpp"
#include "types.hpp"  // for word_type, relation_type, letter_type, tril

namespace libsemigroups {
  class FelschDigraph : public DigraphWithSources<uint32_t> {
   public:
    using node_type       = uint32_t;
    using letter_type     = uint16_t;
    using size_type       = size_t;  // TODO use WordGraph::size_type instead
    using word_graph_type = DigraphWithSources<node_type>;

   private:
    using Definition  = std::pair<node_type, letter_type>;
    using Definitions = std::vector<Definition>;

    // TODO definitions could move to DigraphWithSources
    Definitions             _definitions;
    FelschTree              _felsch_tree;
    Presentation<word_type> _presentation;

   public:
    using DigraphWithSources<node_type>::DigraphWithSources;

    FelschDigraph(Presentation<word_type> const &p, size_type n)
        : DigraphWithSources(p.contains_empty_word() ? n : n + 1,
                             p.alphabet().size()),
          _definitions(),
          _felsch_tree(p.alphabet().size()),
          _presentation(p) {
      _felsch_tree.add_relations(_presentation.cbegin(), _presentation.cend());
    }

    inline bool def_edge(node_type c, letter_type x, node_type d) noexcept {
      // TODO more assertions
      auto cx = unsafe_neighbor(c, x);
      if (cx == UNDEFINED) {
        _definitions.emplace_back(c, x);
        add_edge_nc(c, d, x);
        return true;
      } else {
        return cx == d;
      }
    }

    bool process_definitions(size_t start) {
      for (size_t i = start; i < _definitions.size(); ++i) {
        auto const &d = _definitions[i];
        _felsch_tree.push_back(d.second);
        if (!process_definitions_dfs_v1(d.first)) {
          return false;
        }
      }
      return true;
    }

    size_type number_of_edges() const noexcept {
      return _definitions.size();
    }

    void reduce_number_of_edges_to(size_type n) {
      while (_definitions.size() > n) {
        auto const &p = _definitions.back();
        remove_edge_nc(p.first, p.second);
        _definitions.pop_back();
      }
    }

    Definition first_undefined_edge() const {
      for (auto n = cbegin_nodes(); n != cend_nodes(); ++n) {
        for (auto e = cbegin_edges(*n); e != cend_edges(*n); ++e) {
          if (*e == UNDEFINED) {
            return std::make_pair(n - cbegin_nodes(), e - cbegin_edges(*n));
          }
        }
      }
      return std::make_pair(UNDEFINED, UNDEFINED);
    }

    Definition last_defined_edge() const {
      if (_definitions.empty()) {
        return std::make_pair(UNDEFINED, UNDEFINED);
      }
      return _definitions.back();
    }

    Definitions const &definitions() const noexcept {
      return _definitions;
    }

   private:
    inline bool push_definition_felsch(node_type const &c, size_t i) noexcept {
      auto j = (i % 2 == 0 ? i + 1 : i - 1);
      return push_definition_felsch(
          c, *(_presentation.cbegin() + i), *(_presentation.cbegin() + j));
    }

    bool push_definition_felsch(node_type        c,
                                word_type const &u,
                                word_type const &v) noexcept {
      // LIBSEMIGROUPS_ASSERT(c < _num_active_nodes);
      LIBSEMIGROUPS_ASSERT(!u.empty());
      LIBSEMIGROUPS_ASSERT(!v.empty());
      node_type x = action_digraph_helper::follow_path_nc(
          *this, c, u.cbegin(), u.cend() - 1);
      if (x == UNDEFINED) {
        return true;
      }
      node_type y = action_digraph_helper::follow_path_nc(
          *this, c, v.cbegin(), v.cend() - 1);
      if (y == UNDEFINED) {
        return true;
      }
      // LIBSEMIGROUPS_ASSERT(x < _num_active_nodes);
      // LIBSEMIGROUPS_ASSERT(y < _num_active_nodes);
      LIBSEMIGROUPS_ASSERT(u.back() < _presentation.alphabet().size());
      LIBSEMIGROUPS_ASSERT(v.back() < _presentation.alphabet().size());
      node_type const xa = unsafe_neighbor(x, u.back());
      node_type const yb = unsafe_neighbor(y, v.back());

      if (xa == UNDEFINED && yb != UNDEFINED) {
        return def_edge(x, u.back(), yb);
      } else if (xa != UNDEFINED && yb == UNDEFINED) {
        return def_edge(y, v.back(), xa);
      } else if (xa != UNDEFINED && yb != UNDEFINED && xa != yb) {
        return false;
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
          node_type e = first_source(c, x);
          while (e != UNDEFINED) {
            if (!process_definitions_dfs_v1(e)) {
              return false;
            }
            e = next_source(e, x);
          }
          _felsch_tree.pop_front();
        }
      }
      return true;
    }
  };
}  // namespace libsemigroups

#endif  // LIBSEMIGROUPS_FELSCH_DIGRAPH_HPP_
