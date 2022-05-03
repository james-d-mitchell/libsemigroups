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
// * add option for "only those congruences containing a given set of pairs"
// * use standardization to get "isomorphic" actions (this is "conjugation" in
// Sims)
// * Templatize for "node_type"
// * use the separated out FelschTree in ToddCoxeter
// * Stats and reporting
// * Split into two hpp and tpp files
// * const + noexcept
// * doc
// * code coverage
// * iwyu
// * parallelise?
//
// TODO(maths):
// * containment of congruences defined by "action digraph"
// * generating pairs for congruences defined by "action digraph"
// * minimum degree transformation representations of semigroups/monoids
// * Meets and joins of congruences represented by action digraphs?

#ifndef LIBSEMIGROUPS_SIMS1_HPP_
#define LIBSEMIGROUPS_SIMS1_HPP_

#include <cstddef>

#include "digraph-with-sources.hpp"
#include "digraph.hpp"
#include "felsch-digraph.hpp"
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

  class Sims1 {
   public:
    using node_type       = uint32_t;
    using letter_type     = uint16_t;
    using size_type       = size_t;  // TODO use WordGraph::size_type instead
    using word_graph_type = DigraphWithSources<node_type>;

   private:
    Presentation<word_type> _presentation;
    // TODO stats
    // TODO reporting

   public:
    Sims1(Presentation<word_type> const &p,
          congruence_kind                ck = congruence_kind::right)
        : _presentation() {
      using empty_word = typename Presentation<word_type>::empty_word;
      if (ck == congruence_kind::twosided) {
        LIBSEMIGROUPS_EXCEPTION(
            "expected congruence_kind::right or congruence_kind::left");
      }
      if (ck == congruence_kind::right) {
        _presentation = p;
      } else {
        _presentation.alphabet(p.alphabet());
        for (auto it = p.cbegin(); it != p.cend(); it += 2) {
          _presentation.add_rule(it->crbegin(),
                                 it->crend(),
                                 (it + 1)->crbegin(),
                                 (it + 1)->crend());
        }
        _presentation.contains_empty_word(
            p.contains_empty_word() ? empty_word::yes : empty_word::no);
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
          typename std::vector<DigraphWithSources<uint32_t>>::size_type;
      //! No doc
      using difference_type =
          typename std::vector<DigraphWithSources<uint32_t>>::difference_type;
      //! No doc
      using const_pointer =
          typename std::vector<DigraphWithSources<uint32_t>>::const_pointer;
      //! No doc
      using pointer =
          typename std::vector<DigraphWithSources<uint32_t>>::pointer;
      //! No doc
      using const_reference =
          typename std::vector<DigraphWithSources<uint32_t>>::const_reference;
      //! No doc
      using reference =
          typename std::vector<DigraphWithSources<uint32_t>>::reference;
      //! No doc
      using value_type = DigraphWithSources<uint32_t>;
      //! No doc
      using iterator_category = std::forward_iterator_tag;

     private:
      struct PendingDef {
        PendingDef(node_type s, letter_type g, node_type t, size_t e, size_t n)
            : source(s), generator(g), target(t), num_edges(e), num_nodes(n) {}
        node_type   source;
        letter_type generator;
        node_type   target;
        size_t      num_edges;  // Number of edges in the graph when *this was
                                // added to the stack
        size_t num_nodes;       // Same as above but for nodes
      };

      size_type               _max_num_classes;
      size_type               _min_target_node;
      size_type               _num_active_nodes;
      std::vector<PendingDef> _pending;
      Presentation<word_type>
          _presentation;  // TODO maybe only require the number of generators
      FelschDigraph _felsch_graph;  // This is not in alphabetical order because
                                    // it depends on _max_num_classes

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
          : _max_num_classes(p.contains_empty_word() ? n : n + 1),
            _min_target_node(p.contains_empty_word() ? 0 : 1),
            _num_active_nodes(n == 0 ? 0
                                     : 1),  // = 0 indicates iterator is done
            _pending(),
            _presentation(p),
            _felsch_graph(_presentation, _max_num_classes) {
        if (_num_active_nodes == 0) {
          return;
        }
        _pending.emplace_back(0, 0, 1, 0, 1);
        if (_min_target_node == 0) {
          _pending.emplace_back(0, 0, 0, 0, 1);
        }
        ++(*this);
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
               && _felsch_graph == that._felsch_graph;
      }

      //! No doc
      bool operator!=(const_iterator const &that) const noexcept {
        return !(this->operator==(that));
      }

      //! No doc
      const_reference operator*() const noexcept {
        return _felsch_graph;
      }

      //! No doc
      const_pointer operator->() const noexcept {
        return &_felsch_graph;
      }

      // prefix
      //! No doc
      const_iterator const &operator++() noexcept {
        while (!_pending.empty()) {
        dive:
          auto current = _pending.back();
          _pending.pop_back();

          // Backtrack if necessary
          _felsch_graph.reduce_number_of_edges_to(current.num_edges);
          _num_active_nodes = current.num_nodes;

          LIBSEMIGROUPS_ASSERT(
              _felsch_graph.unsafe_neighbor(current.source, current.generator)
              == UNDEFINED);
          {
            size_t start = _felsch_graph.number_of_edges();

            if (current.target < _num_active_nodes) {
              // TODO move the current.target < _num_active_nodes below and
              // never put them in the stack in the first place
              _felsch_graph.def_edge(
                  current.source, current.generator, current.target);
            } else {
              if (_num_active_nodes == _max_num_classes) {
                continue;
              }
              _felsch_graph.def_edge(
                  current.source, current.generator, _num_active_nodes++);
            }

            if (_felsch_graph.process_definitions(start)) {
              letter_type a = current.generator + 1;
              for (node_type next = current.source; next < _num_active_nodes;
                   ++next) {
                for (; a < _presentation.alphabet().size(); ++a) {
                  if (_felsch_graph.unsafe_neighbor(next, a) == UNDEFINED) {
                    for (node_type b = _min_target_node; b <= _num_active_nodes;
                         ++b) {
                      _pending.emplace_back(next,
                                            a,
                                            b,
                                            _felsch_graph.number_of_edges(),
                                            _num_active_nodes);
                    }
                    goto dive;
                  }
                }
                a = 0;
              }
              // No undefined edges, word graph is complete
              return *this;
            }
          }
        }
        _num_active_nodes = 0;  // indicates that the iterator is done
        _felsch_graph.restrict(0);
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
        std::swap(_max_num_classes, that._max_num_classes);
        std::swap(_min_target_node, that._min_target_node);
        std::swap(_num_active_nodes, that._num_active_nodes);
        std::swap(_pending, that._pending);
        std::swap(_presentation, that._presentation);
        std::swap(_felsch_graph, that._felsch_graph);
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

#endif  // LIBSEMIGROUPS_SIMS1_HPP_
