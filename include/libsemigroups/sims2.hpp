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
// 2-sided congruence" algorithm for semigroups and monoid.
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

#ifndef LIBSEMIGROUPS_SIMS2_HPP_
#define LIBSEMIGROUPS_SIMS2_HPP_

#include <cstddef>

#include "collapsible-word-graph.hpp"
#include "digraph.hpp"
#include "felsch-tree.hpp"
#include "present.hpp"
#include "report.hpp"
#include "types.hpp"  // for word_type, relation_type, letter_type, tril

namespace libsemigroups {
  class SimsGraph1 : public CollapsibleWordGraph<uint32_t> {
   public:
    using node_type       = uint32_t;
    using letter_type     = uint16_t;
    using size_type       = size_t;  // TODO use WordGraph::size_type instead
    using word_graph_type = CollapsibleWordGraph<node_type>;

   private:
    using Definition  = std::pair<node_type, letter_type>;
    using Definitions = std::vector<Definition>;

    Definitions             _definitions;
    FelschTree              _felsch_tree;
    Presentation<word_type> _presentation;

   public:
    SimsGraph1(Presentation<word_type> const &p, size_type n)
        : CollapsibleWordGraph(p.contains_empty_word() ? n : n + 1,
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

  class SimsGraph2 {
   public:
    using node_type       = uint32_t;
    using letter_type     = uint16_t;
    using size_type       = size_t;  // TODO use WordGraph::size_type instead
    using word_graph_type = CollapsibleWordGraph<node_type>;

   private:
    struct FroidurePinNode {
      FroidurePinNode(letter_type frst,
                      letter_type lst,
                      node_type   prfx,
                      node_type   sffx)
          : first(frst), last(lst), prefix(prfx), suffix(sffx) {}
      letter_type first;
      letter_type last;
      node_type   prefix;
      node_type   suffix;
    };

    SimsGraph1                   _left;
    std::vector<size_type>       _lenindex;
    std::vector<FroidurePinNode> _nodes;
    detail::DynamicArray2<bool>  _reduced;
    SimsGraph1                   _right;
    size_type                    _wordlen;

   public:
    SimsGraph2(Presentation<word_type> const &left,
               Presentation<word_type> const &right,
               size_t                         n)
        : _left(left, n),
          _lenindex({0, 1}),
          _nodes(),
          _reduced(left.alphabet().size(), n),
          _right(right, n),
          _wordlen(0) {
      // node corresponding to the identity
      _nodes.emplace_back(UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED);
    }

    SimsGraph1 &left() {
      return _left;
    }

    SimsGraph1 &right() {
      return _right;
    }

    size_type number_of_nodes() const noexcept {
      return _nodes.size();
    }

    bool def_edge(node_type c, letter_type x, node_type d) noexcept {
      LIBSEMIGROUPS_ASSERT(c < _nodes.size());
      LIBSEMIGROUPS_ASSERT(x < _right.out_degree());
      LIBSEMIGROUPS_ASSERT(d <= _nodes.size());
      LIBSEMIGROUPS_ASSERT(_lenindex[_wordlen] <= c);
      LIBSEMIGROUPS_ASSERT(_lenindex[_wordlen + 1] > c);

      // TODO assertions
      size_t start = _right.number_of_edges();
      if (!_right.def_edge(c, x, d) || !_right.process_definitions(start)) {
        return false;
      }

      auto const &node = _nodes[c];

      letter_type b = node.first;
      node_type   s = node.suffix;
      if (s == UNDEFINED) {
        if (d >= _nodes.size()) {
          LIBSEMIGROUPS_ASSERT(c == 0);
          _nodes.emplace_back(x, x, c, c);
          _reduced.set(c, x, true);
        }
      } else if (_reduced.get(s, x) && d == _nodes.size()) {
        // TODO could check if the definition required by FroidurePin is the
        // same as the one we are trying to make, and return false if it is
        // not.
        // first, last, prefix, suffix
        _nodes.emplace_back(b, x, c, _right.unsafe_neighbor(s, x));
        _reduced.set(c, x, true);
      }

      bool install_left = true;
      for (node_type v = _lenindex[_wordlen]; v < _lenindex[_wordlen + 1];
           ++v) {
        if (!std::all_of(_right.cbegin_edges(v),
                         _right.cend_edges(v),
                         [](auto val) { return val != UNDEFINED; })) {
          install_left = false;
          break;
        }
      }
      if (install_left) {
        // Finished multiplying all words of current length by all generators
        size_type start = _left.number_of_edges();
        if (_wordlen == 0) {
          // TODO can we remove this special case?
          for (letter_type j = 0; j != _left.out_degree(); ++j) {
            if (!_left.def_edge(0, j, _right.unsafe_neighbor(0, j))) {
              return false;
            }
          }
        } else {
          for (size_type i = _lenindex[_wordlen]; i != _lenindex[_wordlen + 1];
               ++i) {
            auto p = _nodes[i].prefix;
            auto b = _nodes[i].last;
            for (letter_type j = 0; j != _left.out_degree(); ++j) {
              // TODO check that _left(i, j) isn't already set to a different
              // value, return false if it is!
              if (!_left.def_edge(
                      i,
                      j,
                      _right.unsafe_neighbor(_left.unsafe_neighbor(p, j), b))) {
                return false;
              }
            }
          }
        }
        if (_nodes.size() > _lenindex.back()) {
          _wordlen++;
          _lenindex.push_back(_nodes.size());
        }
        return _left.process_definitions(start);
        // TODO _left can fail to be good in other ways (like not every node is
        // reachable from the first node etc)
      }
      return true;
    }

    bool process_definitions(size_t start) {
      return _right.process_definitions(start);
    }

    void reduce_number_of_edges_to(size_type r, size_type l) {
      if (r < _right.number_of_edges()) {
        for (auto it = _right.definitions().crbegin();
             it != _right.definitions().crbegin() + r;
             ++it) {
          _reduced.set(it->first, it->second, false);
        }
      }
      _right.reduce_number_of_edges_to(r);
      _left.reduce_number_of_edges_to(l);
    }

    void reduce_number_of_nodes_to(size_type n) {
      LIBSEMIGROUPS_ASSERT(n >= 1);
      if (n >= _nodes.size()) {
        return;
      }

      _nodes.erase(_nodes.begin() + n, _nodes.end());

      while (_lenindex.size() > 2 && _lenindex[_lenindex.size() - 1] > n) {
        _lenindex.pop_back();
        --_wordlen;
      }
      LIBSEMIGROUPS_ASSERT(number_of_nodes() == n);
    }

    bool operator==(SimsGraph2 const &that) const noexcept {
      return _right == that._right;
    }

    // TODO remove this one
    void restrict(size_type n) {
      _left.restrict(n);
      _right.restrict(n);
    }
  };

  class Sims2 {
   public:
    using node_type       = uint32_t;
    using letter_type     = uint16_t;
    using size_type       = size_t;  // TODO use WordGraph::size_type instead
    using word_graph_type = SimsGraph1;

   private:
    Presentation<word_type> _left_presentation;
    Presentation<word_type> _right_presentation;
    // TODO stats
    // TODO reporting

   public:
    Sims2(Presentation<word_type> const &p)
        : _left_presentation(), _right_presentation() {
      using empty_word    = typename Presentation<word_type>::empty_word;
      _right_presentation = p;
      _left_presentation.alphabet(p.alphabet());
      for (auto it = p.cbegin(); it != p.cend(); it += 2) {
        _left_presentation.add_rule(
            it->crbegin(), it->crend(), (it + 1)->crbegin(), (it + 1)->crend());
      }
      _left_presentation.contains_empty_word(
          p.contains_empty_word() ? empty_word::yes : empty_word::no);
    }

    //! No doc
    class const_iterator {
     public:
      //! No doc
      using size_type = typename std::vector<SimsGraph2>::size_type;
      //! No doc
      using difference_type = typename std::vector<SimsGraph2>::difference_type;
      //! No doc
      using const_pointer = typename std::vector<SimsGraph2>::const_pointer;
      //! No doc
      using pointer = typename std::vector<SimsGraph2>::pointer;
      //! No doc
      using const_reference = typename std::vector<SimsGraph2>::const_reference;
      //! No doc
      using reference = typename std::vector<SimsGraph2>::reference;
      //! No doc
      using value_type = SimsGraph2;
      //! No doc
      using iterator_category = std::forward_iterator_tag;

     private:
      struct Edge {
        Edge(node_type   s,
             letter_type g,
             node_type   t,
             size_t      el,
             size_t      er,
             size_t      n)
            : source(s),
              generator(g),
              target(t),
              num_edges_left(el),
              num_edges_right(er),
              num_nodes(n) {}
        node_type   source;
        letter_type generator;
        node_type   target;
        size_t num_edges_left;   // Number of edges in the graph when *this was
                                 // added to the stack
        size_t num_edges_right;  // Number of edges in the graph when *this was
                                 // added to the stack
        size_t num_nodes;        // Same as above but for nodes
      };

      using PendingDefinitions = std::vector<Edge>;
      size_type          _max_num_classes;
      size_type          _min_target_node;
      size_type          _num_active_nodes;
      PendingDefinitions _pending;
      SimsGraph2         _word_graphs;

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
      const_iterator(Presentation<word_type> const &left,
                     Presentation<word_type> const &right,
                     size_type                      n)
          : _max_num_classes(left.contains_empty_word() ? n : n + 1),
            _min_target_node(left.contains_empty_word() ? 0 : 1),
            _num_active_nodes(n == 0 ? 0
                                     : 1),  // = 0 indicates iterator is done
            _pending(),
            _word_graphs(left, right, n) {
        if (_num_active_nodes == 0) {
          return;
        }
        _pending.emplace_back(0, 0, 1, 0, 0, 1);
        if (_min_target_node == 0) {
          _pending.emplace_back(0, 0, 0, 0, 0, 1);
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
               && _word_graphs == that._word_graphs;
      }

      //! No doc
      bool operator!=(const_iterator const &that) const noexcept {
        return !(this->operator==(that));
      }

      //! No doc
      const_reference operator*() const noexcept {
        return _word_graphs;
      }

      //! No doc
      const_pointer operator->() const noexcept {
        return &_word_graphs;
      }

      // prefix
      //! No doc
      const_iterator const &operator++() noexcept {
        while (!_pending.empty()) {
        dive:
          auto current = _pending.back();
          _pending.pop_back();

          // Backtrack if necessary
          _word_graphs.reduce_number_of_edges_to(current.num_edges_right,
                                                 current.num_edges_left);
          _word_graphs.reduce_number_of_nodes_to(current.num_nodes);

          LIBSEMIGROUPS_ASSERT(_word_graphs.right().unsafe_neighbor(
                                   current.source, current.generator)
                               == UNDEFINED);
          LIBSEMIGROUPS_ASSERT(_word_graphs.number_of_nodes()
                               == current.num_nodes);

          _num_active_nodes = current.num_nodes;

          if (current.target >= _num_active_nodes) {
            if (_num_active_nodes == _max_num_classes) {
              continue;
            }
            // TODO don't think the next line is required
            current.target = _num_active_nodes++;
          }
          if (!_word_graphs.def_edge(
                  current.source, current.generator, current.target)) {
            continue;
          }

          letter_type a = current.generator + 1;
          for (node_type next = current.source; next < _num_active_nodes;
               ++next) {
            for (; a < _word_graphs.right().out_degree(); ++a) {
              if (_word_graphs.right().unsafe_neighbor(next, a) == UNDEFINED) {
                LIBSEMIGROUPS_ASSERT(_pending.empty()
                                     || _num_active_nodes
                                            >= _pending.back().num_nodes);
                for (node_type b = _min_target_node; b <= _num_active_nodes;
                     ++b) {
                  _pending.emplace_back(next,
                                        a,
                                        b,
                                        _word_graphs.left().number_of_edges(),
                                        _word_graphs.right().number_of_edges(),
                                        _num_active_nodes);
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
        _num_active_nodes = 0;  // indicates that the iterator is done
        _word_graphs.restrict(0);
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
        // TODO
      }
    };

   public:
    const_iterator cbegin(size_type n) const {
      return const_iterator(_left_presentation, _right_presentation, n);
    }

    const_iterator cend(size_type) const {
      return const_iterator(_left_presentation, _right_presentation, 0);
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
