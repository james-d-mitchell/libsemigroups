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

// This file contains some of the implementation of the Stephen class.

namespace libsemigroups {
  namespace v3 {
    template <typename PresentationType>
    Stephen<PresentationType>::Stephen()
        : _finished(false),
          _accept_state(UNDEFINED),
          _presentation(),
          _word(),
          _word_graph() {}

    template <typename PresentationType>
    template <typename P, typename>
    Stephen<PresentationType>::Stephen(P&& p) : Stephen() {
      // static_assert(
      //     std::is_base_of<PresentationBase, std::decay_t<P>>::value ||,
      //    "the template parameter P must be derived from PresentationBase");
      // TODO(Cutting) static assert that P is dervied from PresentationBase or
      // that it's a unique_ptr

      init_impl(std::forward<P>(p), std::is_lvalue_reference<P>());
    }

    template <typename PresentationType>
    template <typename P>
    Stephen<PresentationType>& Stephen<PresentationType>::init(P&& p) {
      static_assert(
          std::is_base_of<PresentationBase, std::decay_t<P>>::value,
          "the template parameter P must be derived from PresentationBase");
      p.validate();
      init_impl(std::forward<P>(p), std::is_lvalue_reference<P>());
      return *this;
    }

    // TODO only enable this function if presentation_type is a shared_ptr
    // template <>
    //
    // Stephen& Stephen::init(std::shared_ptr<presentation_type>&& p) {
    //   p->validate();
    //   init_impl(std::move(p), non_lvalue_tag());
    //   return *this;
    // }
    //
    template <typename PresentationType>
    template <typename P>
    void Stephen<PresentationType>::init_impl(P&& p, lvalue_tag) {
      init_impl(std::move(make<presentation_type>(p)), non_lvalue_tag());
    }

    template <typename PresentationType>
    void Stephen<PresentationType>::init_impl(PresentationType&& p,
                                              non_lvalue_tag) {
      if (p.alphabet().empty()) {
        LIBSEMIGROUPS_EXCEPTION(
            "the argument (Presentation) must not have 0 generators");
      }
      reset();
      _presentation = std::move(p);
      presentation::normalize_alphabet(_presentation);
      _word_graph.init(_presentation);
      _word.clear();
    }

    // template <
    //           typename PresentationType>
    // void Stephen<
    // PresentationType>::init_impl(std::unique_ptr<Presentation<word_type>>&&
    // p,
    //                         non_lvalue_tag) {
    //   if (p->alphabet().empty()) {
    //     LIBSEMIGROUPS_EXCEPTION(
    //         "the argument (Presentation) must not have 0 generators");
    //   }
    //   reset();
    //   _presentation = std::move(p);
    //   presentation::normalize_alphabet(*_presentation);
    //   _word_graph.init(*_presentation);
    //   _word.clear();
    //   // TODO version of this for a Presentation<word_type>&& which just
    //   moves
    //   // the argument into *_presentation.
    // }

    ////////////////////////////////////////////////////////////////////////
    // Public
    ////////////////////////////////////////////////////////////////////////

    template <typename PresentationType>
    Stephen<PresentationType>&
    Stephen<PresentationType>::set_word(word_type const& w) {
      presentation().validate_word(w.cbegin(), w.cend());
      reset();
      _word = w;
      return *this;
    }

    template <typename PresentationType>
    Stephen<PresentationType>&
    Stephen<PresentationType>::set_word(word_type&& w) {
      presentation().validate_word(w.cbegin(), w.cend());
      reset();
      _word = std::move(w);
      return *this;
    }

    template <typename PresentationType>
    typename Stephen<PresentationType>::node_type
    Stephen<PresentationType>::accept_state() {
      if (_accept_state == UNDEFINED) {
        using action_digraph_helper::last_node_on_path_nc;
        run();
        _accept_state
            = last_node_on_path_nc(_word_graph, 0, _word.cbegin(), _word.cend())
                  .first;
      }
      return _accept_state;
    }

    ////////////////////////////////////////////////////////////////////////
    // Private Member Functions
    ////////////////////////////////////////////////////////////////////////

    template <typename PresentationType>
    void Stephen<PresentationType>::report_status(
        std::chrono::high_resolution_clock::time_point const& start_time) {
      if (!report()) {
        return;
      }
      using std::chrono::duration_cast;
      using std::chrono::seconds;
      auto now        = std::chrono::high_resolution_clock::now();
      auto total_time = duration_cast<seconds>(now - start_time);

      auto&   stats = _word_graph.stats();
      int64_t diff  = int64_t(_word_graph.number_of_nodes_active()
                             - stats.prev_active_nodes);

      // TODO(v3) use fmtlib
      static bool first_call = true;
      if (first_call) {
        first_call = false;
        REPORT_DEFAULT_V3("Stephen: " + std::string(60, '-') + "\n");
        REPORT_DEFAULT_V3("Stephen: %11s | %11s | %11s | %11s |\n",
                          "nodes",
                          "defined",
                          "killed",
                          "diff");
        REPORT_DEFAULT_V3("Stephen: " + std::string(60, '-') + "\n");
      }
      REPORT_DEFAULT_V3(
          "Stephen: %11s | %11s | %11s | %11s | "
          "(%llus)\n",
          detail::group_digits(_word_graph.number_of_nodes_active()).c_str(),
          ("+"
           + detail::group_digits(int64_t(_word_graph.number_of_nodes_defined()
                                          - stats.prev_nodes_defined)))
              .c_str(),
          ("-"
           + detail::group_digits(int64_t(_word_graph.number_of_nodes_killed()
                                          - stats.prev_nodes_killed)))
              .c_str(),
          ((diff < 0 ? "" : "+") + detail::group_digits(diff)).c_str(),
          total_time.count());
      _word_graph.stats_check_point();
    }

    template <typename PresentationType>
    void Stephen<PresentationType>::reset() noexcept {
      _finished     = false;
      _accept_state = UNDEFINED;
    }

    template <typename PresentationType>
    void Stephen<PresentationType>::standardize() {
      digraph_with_sources::standardize(_word_graph);
      _word_graph.shrink_to_fit(_word_graph.number_of_nodes_active());
    }

    template <typename PresentationType>
    void Stephen<PresentationType>::validate() const {
      if (presentation().alphabet().empty()) {
        LIBSEMIGROUPS_EXCEPTION("no presentation defined, use Stephen::init to "
                                "set the presentation");
      }
    }

    template <typename PresentationType>
    void Stephen<PresentationType>::run_impl() {
      auto start_time = std::chrono::high_resolution_clock::now();
      validate();  // throws if no presentation is defined
      _word_graph.init(presentation());
      complete_path<EdgeDefiner>(_word_graph, 0, _word.cbegin(), _word.cend());
      node_type& current     = _word_graph.cursor();
      auto const rules_begin = presentation().rules.cbegin();
      auto const rules_end   = presentation().rules.cend();
      bool       did_change  = true;
      auto       def_edge    = EdgeDefiner();

      do {
        current    = 0;
        did_change = false;
        while (current != _word_graph.first_free_node() && !stopped()) {
          for (auto it = rules_begin; it < rules_end; it += 2) {
            node_type                 u_end;
            word_type::const_iterator rit;
            bool                      did_def = false;
            std::tie(u_end, rit) = action_digraph_helper::last_node_on_path_nc(
                _word_graph, current, it->cbegin(), it->cend());
            node_type c, v_end;
            if (rit == it->cend()) {
              ++it;
              if (it->empty()) {
                did_def = false;
                c       = current;
                v_end   = c;
              } else {
                std::tie(did_def, c) = complete_path<EdgeDefiner>(
                    _word_graph, current, it->cbegin(), it->cend() - 1);
                v_end = _word_graph.unsafe_neighbor(c, it->back());
              }
              if (v_end == UNDEFINED) {
                LIBSEMIGROUPS_ASSERT(!it->empty());
                did_def = true;
                def_edge(_word_graph, c, u_end, it->back(), presentation());
              } else if (u_end != v_end) {
                did_def = true;
                _word_graph.coincide_nodes(u_end, v_end);
                _word_graph.process_coincidences();
              }
              --it;
            } else {
              ++it;
              std::tie(v_end, rit)
                  = action_digraph_helper::last_node_on_path_nc(
                      _word_graph, current, it->cbegin(), it->cend());
              if (rit == it->cend()) {
                --it;
                if (it->empty()) {
                  did_def = false;
                  c       = current;
                  u_end   = c;
                } else {
                  std::tie(did_def, c) = complete_path<EdgeDefiner>(
                      _word_graph, current, it->cbegin(), it->cend() - 1);
                  u_end = _word_graph.unsafe_neighbor(c, it->back());
                }
                if (u_end == UNDEFINED) {
                  LIBSEMIGROUPS_ASSERT(!it->empty());
                  did_def = true;
                  def_edge(_word_graph, c, v_end, it->back(), presentation());
                } else if (u_end != v_end) {
                  did_def = true;
                  _word_graph.coincide_nodes(u_end, v_end);
                  _word_graph.process_coincidences();
                }
              } else {
                --it;
              }
            }
            did_change |= did_def;
          }
          did_change |= _word_graph.process_coincidences();
          report_status(start_time);
          current = _word_graph.next_active_node(current);
        }
      } while (did_change && !stopped());
      if (!stopped()) {
        _finished = true;
        standardize();
      }
    }

    namespace stephen {

      template <typename PresentationType>
      bool accepts(Stephen<PresentationType>& s, word_type const& w) {
        using action_digraph_helper::follow_path;
        s.run();
        LIBSEMIGROUPS_ASSERT(s.accept_state() != UNDEFINED);
        return s.accept_state() == follow_path(s.word_graph(), 0, w);
      }

      template <typename PresentationType>
      bool is_left_factor(Stephen<PresentationType>& s, word_type const& w) {
        using action_digraph_helper::last_node_on_path;
        s.run();
        return last_node_on_path(s.word_graph(), 0, w.cbegin(), w.cend()).second
               == w.cend();
      }
    }  // namespace stephen
  }    // namespace v3
}  // namespace libsemigroups
