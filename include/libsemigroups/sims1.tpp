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
  Sims1<T>::~Sims1() = default;

  template <typename T>
  Sims1<T>::Sims1(Presentation<word_type> const &p, congruence_kind ck)
      : _presentation() {
    if (ck == congruence_kind::twosided) {
      LIBSEMIGROUPS_EXCEPTION(
          "expected congruence_kind::right or congruence_kind::left");
    }
    if (ck == congruence_kind::right) {
      _presentation = p;
    } else {
      _presentation.alphabet(p.alphabet());
      for (auto it = p.cbegin(); it != p.cend(); it += 2) {
        _presentation.add_rule(
            it->crbegin(), it->crend(), (it + 1)->crbegin(), (it + 1)->crend());
      }
      using empty_word = typename Presentation<word_type>::empty_word;
      _presentation.contains_empty_word(
          p.contains_empty_word() ? empty_word::yes : empty_word::no);
    }
  }

  template <typename T>
  uint64_t Sims1<T>::number_of_congruences(size_type n) {
    // return std::distance(cbegin(n), cend(n));

    u_int64_t                                      result = 0;
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

  template <typename T>
  Sims1<T>::const_iterator::const_iterator(Presentation<word_type> const &p,
                                           size_type                      n)
      : _max_num_classes(p.contains_empty_word() ? n : n + 1),
        _min_target_node(p.contains_empty_word() ? 0 : 1),
        _num_active_nodes(n == 0 ? 0 : 1),  // = 0 indicates iterator is done
        // TODO sink _num_active_nodes into DigraphWithSources or
        // FelschDigraph
        _num_gens(p.alphabet().size()),
        _pending(),
        _felsch_graph(p, _max_num_classes) {
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

  template <typename T>
  typename Sims1<T>::const_iterator const &
  Sims1<T>::const_iterator::operator++() {
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
        size_type start = _felsch_graph.number_of_edges();

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
            for (; a < _num_gens; ++a) {
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
}  // namespace libsemigroups
