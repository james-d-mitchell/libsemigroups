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
#include <stack>

#include "digraph-with-sources.hpp"
#include "digraph.hpp"
#include "felsch-digraph.hpp"
#include "felsch-tree.hpp"
#include "present.hpp"
#include "report.hpp"
#include "types.hpp"  // for word_type, relation_type, letter_type, tril
#include "uf.hpp"

namespace libsemigroups {

  class Sims2Graph {
   public:
    using node_type       = uint32_t;
    using letter_type     = uint16_t;
    using size_type       = size_t;  // TODO use WordGraph::size_type instead
    using word_graph_type = DigraphWithSources<node_type>;

   private:
    struct FroidurePinNode {
      FroidurePinNode(letter_type frst,
                      letter_type lst,
                      node_type   prfx,
                      node_type   sffx,
                      size_type   lngth)
          : first(frst), last(lst), prefix(prfx), suffix(sffx), length(lngth) {}
      letter_type first;
      letter_type last;
      node_type   prefix;
      node_type   suffix;
      size_type   length;
    };

    FelschDigraph                _left;
    std::vector<size_type>       _lenindex;
    std::vector<FroidurePinNode> _nodes;
    detail::DynamicArray2<bool>  _reduced;
    FelschDigraph                _right;
    size_type                    _wordlen_left;
    size_type                    _wordlen_right;

   public:
    Sims2Graph(Presentation<word_type> const &left,
               Presentation<word_type> const &right,
               size_t                         n)
        : _left(left, n),
          _lenindex({0, 1}),  // _lenindex[i] is the position in _nodes of the
                              // first word of length i
          _nodes(),
          _reduced(left.alphabet().size(),
                   left.contains_empty_word() ? n : n + 1),
          _right(right, n),
          _wordlen_left(
              UNDEFINED),    // is the maximum length of a word that has
                             // all of its left and right multiples installed
          _wordlen_right(0)  // the minimum length of a word that does not have
                             // at least one right multiple (only) installed
    {
      // node corresponding to the identity
      _nodes.emplace_back(UNDEFINED, 0, 0, UNDEFINED, 0);
    }

    FelschDigraph &left() {
      return _left;
    }

    FelschDigraph &right() {
      return _right;
    }

    FelschDigraph const &left() const {
      return _left;
    }

    FelschDigraph const &right() const {
      return _right;
    }

    size_type number_of_nodes() const noexcept {
      return _nodes.size();
    }

    bool def_edge(node_type c, letter_type x, node_type d) noexcept {
      LIBSEMIGROUPS_ASSERT(c < _nodes.size());
      LIBSEMIGROUPS_ASSERT(x < _right.out_degree());
      LIBSEMIGROUPS_ASSERT(d <= _nodes.size());

      // TODO assertions
      size_type start = _right.number_of_edges();
      if (!_right.def_edge(c, x, d) || !_right.process_definitions(start)) {
        return false;
      }

      bool current_wordlen_right_done = false;
      // LIBSEMIGROUPS_ASSERT(_wordlen_right + 1 < _lenindex.size());
      if (_wordlen_right + 1 < _lenindex.size()
          && c > _lenindex[_wordlen_right + 1]) {
        LIBSEMIGROUPS_ASSERT(_wordlen_right == length(c));
        _wordlen_right++;  // = length(c);
        _lenindex.push_back(_nodes.size());
        current_wordlen_right_done = true;
      }

      auto const &node = _nodes[c];

      letter_type b = node.first;
      node_type   s = node.suffix;
      if (s == UNDEFINED) {
        if (d >= _nodes.size()) {
          LIBSEMIGROUPS_ASSERT(c == 0);
          // first, last, prefix, suffix, length
          _nodes.emplace_back(x, x, c, c, 1);
          _reduced.set(c, x, true);
        }
      } else if (d == _nodes.size()) {
        if (_reduced.get(s, x)) {
          // TODO could check if the definition required by FroidurePin is the
          // same as the one we are trying to make, and return false if it is
          // not.
          // first, last, prefix, suffix, length
          _nodes.emplace_back(
              b, x, c, _right.unsafe_neighbor(s, x), node.length + 1);
          _reduced.set(c, x, true);
        } else {
          // It should be the case that d being a new value is reduced, but
          // because its suffix times x is not reduced, d is not reduced, which
          // is a contradiction.
          return false;
        }
      }

      LIBSEMIGROUPS_ASSERT(d != _nodes.size());

      if (_wordlen_right + 1 < _lenindex.size()
          && c == _lenindex[_wordlen_right + 1] - 1
          && x == _right.out_degree() - 1) {
        // LIBSEMIGROUPS_ASSERT(_wordlen_right == length(c));
        _wordlen_right++;
        _lenindex.push_back(_nodes.size());
        current_wordlen_right_done = true;
      } else if (_right.number_of_edges()
                 == number_of_nodes() * _right.out_degree()) {
        // LIBSEMIGROUPS_ASSERT(_wordlen_right == length(c));
        _wordlen_right++;
        _lenindex.push_back(_nodes.size());
        current_wordlen_right_done = true;
      }

      // Every value in _right before the one in position (c, x) is defined, so
      // we check if (c is the last node corresponding to a word of current
      // length, and x is the last generator) or (the length of word
      // corresponding to c is longer than the current _wordlen). The latter
      // can happen when, for example, if we have two letters/generators and x
      // = 0, and (c, 1) is defined when we do process_definitions in _right at
      // the start of this function, then the first check fails, but the next
      // time we define an edge we will know that the row of the current value
      // of c is complete, because the next value will be at least
      // _lenindex.back().

      LIBSEMIGROUPS_ASSERT(_wordlen_left + 1 < _lenindex.size());
      if (current_wordlen_right_done) {
        return install_left();
      }
      return true;
    }

    bool install_left() {
      // Finished multiplying all words of current length by all generators
      // on the right
      size_type start = _left.number_of_edges();
      if (_wordlen_left == UNDEFINED) {
        LIBSEMIGROUPS_ASSERT(_wordlen_left + 1 < _wordlen_right);
        // TODO can we remove this special case?
        for (letter_type j = 0; j != _left.out_degree(); ++j) {
          if (!_left.def_edge(0, j, _right.unsafe_neighbor(0, j))) {
            return false;
          }
        }
        _wordlen_left++;
      }
      LIBSEMIGROUPS_ASSERT(_wordlen_left < _lenindex.size());
      for (size_type i = _lenindex[_wordlen_left + 1];
           i < _lenindex[_wordlen_right];
           ++i) {
        auto p = _nodes[i].prefix;
        auto b = _nodes[i].last;
        for (letter_type j = 0; j != _left.out_degree(); ++j) {
          if (!_left.def_edge(
                  i,
                  j,
                  _right.unsafe_neighbor(_left.unsafe_neighbor(p, j), b))) {
            return false;
          }
        }
      }
      _wordlen_left = _wordlen_right - 1;
      // TODO can _left fail to be good in other ways (like not every node
      // is reachable from the first node etc)?
      return _left.process_definitions(start);
    }

    // TODO remove this
    bool process_definitions(size_t start) {
      return _right.process_definitions(start);
    }

    void reduce_number_of_edges_to(size_type r, size_type l) {
      if (r < _right.number_of_edges()) {
        for (auto it = _right.definitions().cbegin() + r;
             it != _right.definitions().cend();
             ++it) {
          _reduced.set(it->first, it->second, false);
        }
      }
      _right.reduce_number_of_edges_to(r);
      _left.reduce_number_of_edges_to(l);
    }

    // FIXME Combine with reduce_number_of_edges_to since this must be called
    // before calling reduce_number_of_nodes_to
    void reduce_number_of_nodes_to(size_type n) {
      LIBSEMIGROUPS_ASSERT(n >= 1);
      LIBSEMIGROUPS_ASSERT(n <= _nodes.size());
      _nodes.erase(_nodes.begin() + n, _nodes.end());
      LIBSEMIGROUPS_ASSERT(_nodes.size() == n);

      auto le = _left.first_undefined_edge();

      // Reset _wordlen and _lenindex to reflect that we have left multiplied
      // every word of length ?? by every generator

      LIBSEMIGROUPS_ASSERT(le.first != UNDEFINED);
      LIBSEMIGROUPS_ASSERT(le.second != UNDEFINED);
      // Every row before le.first is complete
      _wordlen_left  = length(le.first) - 1;
      _wordlen_right = length(_right.first_undefined_edge().first);
      _lenindex.erase(_lenindex.begin()
                          + std::max(_wordlen_right + 1, size_type(2)),
                      _lenindex.end());
      // LIBSEMIGROUPS_ASSERT(le.first <= _lenindex.back());
      LIBSEMIGROUPS_ASSERT(number_of_nodes() == n);
      validate();
    }

    bool operator==(Sims2Graph const &that) const noexcept {
      return _right == that._right;
    }

    // TODO remove this one
    void restrict(size_type n) {
      _left.restrict(n);
      _right.restrict(n);
    }

    size_type length(node_type c) const noexcept {
      if (c >= number_of_nodes()) {
        return UNDEFINED;
      }
      return *std::find_if(_lenindex.crbegin(),
                           _lenindex.crend(),
                           [&c](auto val) { return val <= c; });
    }

    // Should only be invoked on a complete instance.
    bool check_froidure_pin() {
      for (size_t i = 0; i < number_of_nodes(); ++i) {
        auto const &node = _nodes[i];
        auto        b    = node.first;
        auto        s    = node.suffix;
        if (s != UNDEFINED) {
          LIBSEMIGROUPS_ASSERT(b != UNDEFINED);
          for (letter_type j = 0; j != _right.out_degree(); ++j) {
            if (!_reduced.get(s, j)) {
              auto r = _right.unsafe_neighbor(s, j);
              if (_right.unsafe_neighbor(i, j)
                  != _right.unsafe_neighbor(
                      _left.unsafe_neighbor(_nodes[r].prefix, b),
                      _nodes[r].last)) {
                return false;
              }
            }
          }
        }
      }
      return true;
    }

    bool hopcroft_karp() {
      detail::Duf<>                               uf(number_of_nodes());
      std::stack<std::pair<node_type, node_type>> stck;
      stck.emplace(0, 0);
      while (!stck.empty()) {
        auto q = stck.top();
        stck.pop();
        for (letter_type a = 0; a < _right.out_degree(); ++a) {
          auto r1 = uf.find(_right.unsafe_neighbor(q.first, a));
          auto r2 = uf.find(_left.unsafe_neighbor(q.second, a));
          if (r1 != r2) {
            uf.unite(r1, r2);
            stck.emplace(r1, r2);
          }
        }
      }
      return uf.number_of_blocks() == uf.size();
    }

    bool alt() {
      size_type N = _right.out_degree();
      for (node_type n = 0; n < number_of_nodes(); ++n) {
        for (letter_type a = 0; a < N; ++a) {
          for (letter_type b = 0; b < N; ++b) {
            if (_left.unsafe_neighbor(_right.unsafe_neighbor(n, a), b)
                != _right.unsafe_neighbor(_left.unsafe_neighbor(n, b), a)) {
              return false;
            }
          }
        }
      }
      return true;
    }

#ifdef LIBSEMIGROUPS_DEBUG
    void validate() const noexcept {
      size_type num_sources = 1;
      size_type num_targets = 0;
      if (!_right.definitions().empty()) {
        num_sources = std::max_element(_right.definitions().cbegin(),
                                       _right.definitions().cend(),
                                       [](auto lhop, auto rhop) {
                                         return lhop.first < rhop.first;
                                       })
                          ->first
                      + 1;
        for (auto const &e : _right.definitions()) {
          auto t = _right.unsafe_neighbor(e.first, e.second);
          if (t != UNDEFINED && t > num_targets) {
            num_targets = t;
          }
        }
      }
      num_targets++;
      LIBSEMIGROUPS_ASSERT(
          _left.first_undefined_edge().first == UNDEFINED
          || length(_left.first_undefined_edge().first) == UNDEFINED
          // The previous happens if the graph is complete, then the
          // first undefined edge can be for incident to a larger
          // node, whose length isn't defined
          || _wordlen_left == length(_left.first_undefined_edge().first) - 1);
      LIBSEMIGROUPS_ASSERT(
          _right.first_undefined_edge().first == UNDEFINED
          || length(_right.first_undefined_edge().first) == UNDEFINED
          || _wordlen_right == length(_right.first_undefined_edge().first));
      LIBSEMIGROUPS_ASSERT(num_sources <= _nodes.size());
      LIBSEMIGROUPS_ASSERT(num_targets == _nodes.size());
      LIBSEMIGROUPS_ASSERT(_wordlen_right + 1 <= _lenindex.size());
      LIBSEMIGROUPS_ASSERT(_lenindex.size() <= _wordlen_right + 2);
      LIBSEMIGROUPS_ASSERT(std::count(_reduced.cbegin(), _reduced.cend(), true)
                           == _nodes.size() - 1);
#else
    void validate() const noexcept {}
#endif
    }
  };

  class Sims2 {
   public:
    using node_type       = uint32_t;
    using letter_type     = uint16_t;
    using size_type       = size_t;  // TODO use WordGraph::size_type instead
    using word_graph_type = FelschDigraph;

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

    Presentation<word_type> const &left_presentation() const noexcept {
      return _left_presentation;
    }
    Presentation<word_type> const &right_presentation() const noexcept {
      return _right_presentation;
    }

    //! No doc
    class const_iterator {
     public:
      //! No doc
      using size_type = typename std::vector<Sims2Graph>::size_type;
      //! No doc
      using difference_type = typename std::vector<Sims2Graph>::difference_type;
      //! No doc
      using const_pointer = typename std::vector<Sims2Graph>::const_pointer;
      //! No doc
      using pointer = typename std::vector<Sims2Graph>::pointer;
      //! No doc
      using const_reference = typename std::vector<Sims2Graph>::const_reference;
      //! No doc
      using reference = typename std::vector<Sims2Graph>::reference;
      //! No doc
      using value_type = Sims2Graph;
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
        size_t      num_edges_left;  // Number of edges in the graph when
                                     // *this was added to the stack
        size_t num_edges_right;      // Number of edges in the graph when
                                     // *this was added to the stack
        size_t num_nodes;            // Same as above but for nodes
      };

      using PendingDefinitions = std::vector<Edge>;
      size_type          _max_num_classes;
      size_type          _min_target_node;
      size_type          _num_active_nodes;
      PendingDefinitions _pending;
      Sims2Graph         _word_graphs;

     public:
      // None of the constructors are noexcept because the
      // corresponding constructors for std::vector aren't (until
      // C++17).
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
        // The increment above is required so that when dereferencing
        // any pointer of this type we obtain a valid word graph (o/w
        // the value pointed to here is empty).
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
          LIBSEMIGROUPS_ASSERT(std::all_of(
              _pending.cbegin(), _pending.cend(), [this](auto const &val) {
                return val.num_nodes <= this->_num_active_nodes;
              }));
          auto current = _pending.back();
          _pending.pop_back();

          // Backtrack if necessary
          _word_graphs.reduce_number_of_edges_to(current.num_edges_right,
                                                 current.num_edges_left);
          _word_graphs.reduce_number_of_nodes_to(current.num_nodes);
          LIBSEMIGROUPS_ASSERT(_word_graphs.number_of_nodes()
                                   == current.num_nodes
                               || current.num_nodes == _max_num_classes);
          LIBSEMIGROUPS_ASSERT(_word_graphs.right().number_of_edges()
                               == current.num_edges_right);
          LIBSEMIGROUPS_ASSERT(_word_graphs.left().number_of_edges()
                               == current.num_edges_left);
          LIBSEMIGROUPS_ASSERT(_word_graphs.right().unsafe_neighbor(
                                   current.source, current.generator)
                               == UNDEFINED);

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
          // _word_graphs.validate();
          if (!_word_graphs.alt()) {
            continue;
          }

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

    // Returns the number of right congruences with up to n
    // (inclusive) classes.
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
