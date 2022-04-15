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
// TODO:
// * Implement left and two-sided versions [DONE, sort of]
// * Fix issue with adjoined identity
// * add option for "only those congruences containing a given set of pairs"
// * Rename to Sims or SimsLIC
// * Templatize for "node_type"
// * Stats and reporting
// * Split into two hpp and tpp files
// * const + noexcept
// * iwyu
// * parallelise?
// * use the separated out FelschTree in ToddCoxeter
// * use standardization to get "isomorphic" actions
// * doc + code coverage
//
// TODO(maths):
// * containment of congruences defined by "action digraph"
// * generating pairs for congruences defined by "action digraph"
// * minimum degree transformation representations of semigroups/monoids

#ifndef LIBSEMIGROUPS_LOW_INDEX_HPP_
#define LIBSEMIGROUPS_LOW_INDEX_HPP_

#include <cstddef>

#include "collapsible-word-graph.hpp"
#include "digraph.hpp"
#include "felsch-tree.hpp"
#include "present.hpp"
#include "report.hpp"
#include "types.hpp"  // for word_type, relation_type, letter_type, tril

namespace libsemigroups {
  namespace {

    template <typename T>
    void check_compatibility(ActionDigraph<T> const &       d,
                             Presentation<word_type> const &p) {
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
   public:
    using node_type       = uint32_t;
    using letter_type     = uint16_t;
    using size_type       = size_t;  // TODO use WordGraph::size_type instead
    using word_graph_type = CollapsibleWordGraph<node_type>;

   private:
    Presentation<word_type> _presentation;
    // TODO stats
    // TODO reporting

   public:
    LowIndexCongruences(Presentation<word_type> const &p,
                        congruence_kind ck = congruence_kind::right)
        : _presentation() {
      if (ck == congruence_kind::right || ck == congruence_kind::twosided) {
        _presentation = p;
      } else {
        _presentation.alphabet(p.alphabet());
      }
      if (ck == congruence_kind::left || ck == congruence_kind::twosided) {
        for (auto it = p.cbegin(); it != p.cend(); it += 2) {
          _presentation.add_rule(it->crbegin(),
                                 it->crend(),
                                 (it + 1)->crbegin(),
                                 (it + 1)->crend());
        }
        // TODO if ck == twosided, then avoid adding duplicate relations
      }
    }

    Presentation<word_type> const &presentation() const noexcept {
      return _presentation;
    }
    //! No doc
    class const_iterator {
     public:
      //! No doc
      using size_type =
          typename std::vector<CollapsibleWordGraph<uint32_t>>::size_type;
      //! No doc
      using difference_type =
          typename std::vector<CollapsibleWordGraph<uint32_t>>::difference_type;
      //! No doc
      using const_pointer =
          typename std::vector<CollapsibleWordGraph<uint32_t>>::const_pointer;
      //! No doc
      using pointer =
          typename std::vector<CollapsibleWordGraph<uint32_t>>::pointer;
      //! No doc
      using const_reference =
          typename std::vector<CollapsibleWordGraph<uint32_t>>::const_reference;
      //! No doc
      using reference =
          typename std::vector<CollapsibleWordGraph<uint32_t>>::reference;
      //! No doc
      using value_type = CollapsibleWordGraph<uint32_t>;
      //! No doc
      using iterator_category = std::forward_iterator_tag;

     private:
      struct Edge {
        Edge(node_type s, letter_type g, node_type t, size_t e, size_t n)
            : source(s), generator(g), target(t), num_edges(e), num_nodes(n) {}
        node_type   source;
        letter_type generator;
        node_type   target;
        size_t      num_edges;  // Number of edges in the graph when *this was
                                // added to the stack
        size_t num_nodes;       // Same as above but for nodes
      };
      using Definition         = std::pair<node_type, letter_type>;
      using Definitions        = std::vector<Definition>;
      using PendingDefinitions = std::vector<Edge>;

      Definitions                    _definitions;
      FelschTree                     _felsch_tree;
      size_type                      _max_num_classes;
      size_type                      _min_target_node;
      size_type                      _num_active_nodes;
      PendingDefinitions             _pending;
      Presentation<word_type>        _presentation;
      CollapsibleWordGraph<uint32_t> _word_graph;

     public:
      // None of the constructors are noexcept because the corresponding
      // constructors for std::vector aren't (until C++17).
      //! No doc
      const_iterator() = delete;
      //! No doc
      const_iterator(const_iterator const &) = default;
      //! No doc
      const_iterator(const_iterator &&) = default;
      //! No doc
      const_iterator &operator=(const_iterator const &) = default;
      //! No doc
      const_iterator &operator=(const_iterator &&) = default;

      //! No doc
      const_iterator(Presentation<word_type> const &p, size_type n)
          : _definitions(),
            _felsch_tree(p.alphabet().size()),
            _max_num_classes(n),
            _min_target_node(),
            _num_active_nodes(n == 0 ? 0
                                     : 1),  // = 0 indicates iterator is done
            _pending(),
            _presentation(p),
            _word_graph(n, _presentation.alphabet().size()) {
        if (_num_active_nodes == 0) {
          return;
        }
        _felsch_tree.add_relations(_presentation.cbegin(),
                                   _presentation.cend());
        _pending.emplace_back(0, 0, 1, 0, 1);
        if (_presentation.contains_empty_word()) {
          _pending.emplace_back(0, 0, 0, 0, 1);
          _min_target_node = 0;
        } else {
          _word_graph.add_nodes(1);
          _max_num_classes++;
          _min_target_node = 1;
        }
        if (n != 0) {
          ++(*this);
        }
        // The increment above is required so that when dereferencing any
        // pointer of this type we obtain a valid word graph (o/w the value
        // pointed to here is empty).
      }

      //! No doc
      ~const_iterator() = default;

      //! No doc
      bool operator==(const_iterator const &that) const noexcept {
        if (_num_active_nodes == 0 && that._num_active_nodes == 0) {
          return true;
        }
        return _num_active_nodes == that._num_active_nodes
               && _word_graph == that._word_graph;
      }

      //! No doc
      bool operator!=(const_iterator const &that) const noexcept {
        return !(this->operator==(that));
      }

      //! No doc
      const_reference operator*() const noexcept {
        return _word_graph;
      }

      //! No doc
      const_pointer operator->() const noexcept {
        return &_word_graph;
      }

      // prefix
      //! No doc
      const_iterator const &operator++() noexcept {
        while (!_pending.empty()) {
        dive:
          auto current = _pending.back();
          _pending.pop_back();

          // Backtrack if necessary
          while (_definitions.size() > current.num_edges) {
            auto const &p = _definitions.back();
            _word_graph.remove_edge_nc(p.first, p.second);
            _definitions.pop_back();
          }

          _num_active_nodes = current.num_nodes;

          LIBSEMIGROUPS_ASSERT(
              _word_graph.unsafe_neighbor(current.source, current.generator)
              == UNDEFINED);
          {
            size_t start = _definitions.size();

            if (current.target < _num_active_nodes) {
              def_edge(current.source, current.generator, current.target);
            } else {
              if (_num_active_nodes == _max_num_classes) {
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
                    for (node_type b = _min_target_node; b <= _num_active_nodes;
                         ++b) {
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
              return *this;
            }
          }
        }
        _num_active_nodes = 0;  // indicates that the iterator is done
        _word_graph.restrict(0);
        return *this;
      }

      //! No doc
      // postfix
      const_iterator operator++(int) noexcept {
        const_iterator copy(*this);
        ++(*this);
        return copy;
      }

      //! No doc
      void swap(const_iterator &that) noexcept {
        std::swap(_definitions, that._definitions);
        std::swap(_num_active_nodes, that._num_active_nodes);
        std::swap(_pending, that._pending);
        std::swap(_word_graph, that._word_graph);
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

      inline bool push_definition_felsch(node_type const &c,
                                         size_t           i) noexcept {
        auto j = (i % 2 == 0 ? i + 1 : i - 1);
        return push_definition_felsch(
            c, *(_presentation.cbegin() + i), *(_presentation.cbegin() + j));
      }

      bool push_definition_felsch(node_type        c,
                                  word_type const &u,
                                  word_type const &v) noexcept {
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
          auto const &d = _definitions[i];
          _felsch_tree.push_back(d.second);
          if (!process_definitions_dfs_v1(d.first)) {
            return false;
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
    };

   public:
    const_iterator cbegin(size_type n) const {
      return const_iterator(presentation(), n);
    }

    const_iterator cend(size_type) const {
      return const_iterator(presentation(), 0);
    }

    // Returns the number of right congruences with up to n (inclusive)
    // classes.
    size_t number_of_congruences(size_t n) {
      // return std::distance(cbegin(n), cend(n));

      size_t                                         result = 0;
      std::chrono::high_resolution_clock::time_point last_report
          = std::chrono::high_resolution_clock::now();
      auto const last = cend(n);
      for (auto it = cbegin(n); it != last; ++it) {
        ++result;
        auto now     = std::chrono::high_resolution_clock::now();
        auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
            now - last_report);
        if (elapsed > std::chrono::duration_cast<std::chrono::nanoseconds>(
                std::chrono::seconds(1))) {
          std::swap(now, last_report);
          REPORT_DEFAULT("found %llu congruences so far!\n", uint64_t(result));
        }
      }
      return result;
    }
  };

}  // namespace libsemigroups

#endif  // LIBSEMIGROUPS_LOW_INDEX_HPP_
