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

#include <cstddef>        // for size_t
#include <stdexcept>      // for number_of_congruencestime_error
#include <unordered_set>  // for unordered_set
#include <vector>         // for vector

#include <iostream>

#include "catch.hpp"  // for REQUIRE, REQUIRE_THROWS_AS, REQUI...
#include "fpsemi-examples.hpp"
#include "test-main.hpp"  // for LIBSEMIGROUPS_TEST_CASE

#include "libsemigroups/bipart.hpp"
#include "libsemigroups/digraph-helper.hpp"
#include "libsemigroups/froidure-pin.hpp"
#include "libsemigroups/make.hpp"
#include "libsemigroups/sims2.hpp"  // for Sims2
#include "libsemigroups/transf.hpp"
#include "libsemigroups/types.hpp"  // for word_type

namespace libsemigroups {
  using empty_word = Presentation<word_type>::empty_word;

  /*namespace {

    void check_compatibility(ActionDigraph<size_t> const&   d,
                             Presentation<word_type> const& p) {
      for (size_t i = 0; i < d.number_of_nodes(); ++i) {
        for (auto it = p.cbegin(); it != p.cend(); it += 2) {
          std::cout << " i = " << i << std::endl;
          std::cout << " it = " << *it << std::endl;
          std::cout << " it + 1 = " << *(it + 1) << std::endl;
          REQUIRE(action_digraph_helper::follow_path_nc(d, i, *it)
                  == action_digraph_helper::follow_path_nc(d, i, *(it + 1)));
        }
      }
    }
  }  // namespace */

  LIBSEMIGROUPS_TEST_CASE("Sims2",
                          "000",
                          "fp example 1",
                          "[quick][presentation]") {
    auto rg         = ReportGuard(false);
    using WordGraph = typename Sims2::word_graph_type;
    using node_type = typename WordGraph::node_type;

    Presentation<word_type> p(empty_word::yes);
    p.alphabet({0, 1});
    presentation::add_rule_and_check(p, {0, 0, 0}, {0});
    presentation::add_rule_and_check(p, {1, 1}, {1});
    presentation::add_rule_and_check(p, {0, 1, 0, 1}, {0});

    Sims2 s(p);
    // REQUIRE(s.number_of_congruences(2) == 3);
    {
      auto it = s.cbegin(3);
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(3, {{0, 0}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(3, {{0, 0}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 2}, {1, 2}, {1, 2}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 2}, {1, 1}, {2, 2}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 2}, {1, 1}, {1, 2}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 2}, {1, 1}, {1, 2}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(3, {{1, 1}, {1, 1}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(3, {{1, 1}, {1, 1}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(3, {{1, 0}, {1, 1}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(3, {{1, 0}, {1, 1}}));

      ++it;
      REQUIRE(it == s.cend(3));
      REQUIRE(s.number_of_congruences(3) == 5);
    }

    {
      auto it = s.cbegin(4);
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(4, {{0, 0}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(4, {{0, 0}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 2}, {1, 2}, {1, 2}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 2}, {1, 1}, {2, 2}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 2}, {1, 1}, {1, 2}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 2}, {1, 1}, {1, 2}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(3, {{1, 1}, {1, 1}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(3, {{1, 1}, {1, 1}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(3, {{1, 0}, {1, 1}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(3, {{1, 0}, {1, 1}}));

      // REQUIRE(s.number_of_congruences(5) == 6);
      // REQUIRE(s.number_of_congruences(6) == 6);
    }
  }
}  // namespace libsemigroups

// [ [ [ [ 1, 2 ], [ 1, 1 ], [ 3, 2 ], [ 3, 3 ] ],
//     [ [ 1, 2 ], [ 1, 3 ], [ 1, 2 ], [ 1, 3 ] ] ],
//
//   [ [ [ 0, 0 ] ], [ [ 0, 0 ] ] ],
//
//   [ [ [ 1, 0 ], [ 1, 1 ] ], [ [ 1, 0 ], [ 1, 1 ] ] ],
//
//   [ [ [ 1, 1 ], [ 1, 1 ] ], [ [ 1, 1 ], [ 1, 1 ] ] ],
//
//   [ [ [ 1, 2 ], [ 1, 1 ], [ 1, 2 ] ],
//     [ [ 1, 2 ], [ 1, 1 ], [ 1, 2 ] ] ],
//
//   [ [ [ 1, 2 ], [ 1, 1 ], [ 2, 2 ] ],
//     [ [ 1, 2 ], [ 1, 2 ], [ 1, 2 ] ] ] ]
