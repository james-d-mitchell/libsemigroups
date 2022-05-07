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
// * Templatize for "node_type"
// * add option for "only those congruences containing a given set of pairs"
// * use standardization to get "isomorphic" actions (this is "conjugation" in
// Sims)
// * use the separated out FelschTree in ToddCoxeter
// * Stats and reporting
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
    // TODO remove or move this
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

  template <typename T>
  class Sims1 {
   public:
    using node_type    = T;
    using letter_type  = typename word_type::value_type;
    using size_type    = typename DigraphWithSources<node_type>::size_type;
    using digraph_type = DigraphWithSources<node_type>;

   private:
    Presentation<word_type> _presentation;
    // TODO stats
    // TODO reporting

   public:
    Sims1(Presentation<word_type> const &p, congruence_kind ck);

    template <typename U>
    Sims1(U const &p, congruence_kind ck) : Sims1(make(p), ck) {
      static_assert(std::is_base_of<PresentationPolymorphicBase, U>::value,
                    "the template parameter U must be derived from "
                    "PresentationPolymorphicBase");
    }

    Sims1()              = default;
    Sims1(Sims1 const &) = default;
    Sims1(Sims1 &)       = default;
    Sims1 &operator=(Sims1 const &) = default;
    Sims1 &operator=(Sims1 &&) = default;

    ~Sims1();

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
        PendingDef(node_type   s,
                   letter_type g,
                   node_type   t,
                   size_type   e,
                   size_type   n) noexcept
            : source(s), generator(g), target(t), num_edges(e), num_nodes(n) {}
        node_type   source;
        letter_type generator;
        node_type   target;
        size_type   num_edges;  // Number of edges in the graph when *this was
                                // added to the stack
        size_type num_nodes;    // Same as above but for nodes
      };

      size_type               _max_num_classes;
      size_type               _min_target_node;
      size_type               _num_active_nodes;
      size_type               _num_gens;
      std::vector<PendingDef> _pending;
      FelschDigraph<word_type, node_type>
          _felsch_graph;  // This is not in alphabetical order because
                          // it depends on _max_num_classes

     public:
      //! No doc
      const_iterator(Presentation<word_type> const &p, size_type n);

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
      const_iterator const &operator++();

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
        std::swap(_num_gens, that._num_gens);
        std::swap(_pending, that._pending);
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
    uint64_t number_of_congruences(size_type n);
  };

}  // namespace libsemigroups

#include "sims1.tpp"

#endif  // LIBSEMIGROUPS_SIMS1_HPP_
