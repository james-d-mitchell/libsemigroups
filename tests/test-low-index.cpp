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
#include <stdexcept>      // for runtime_error
#include <unordered_set>  // for unordered_set
#include <vector>         // for vector

#include <iostream>

#include "catch.hpp"  // for REQUIRE, REQUIRE_THROWS_AS, REQUI...
#include "libsemigroups/low-index.hpp"  // for Presentation
#include "libsemigroups/types.hpp"      // for word_type
#include "test-main.hpp"                // for LIBSEMIGROUPS_TEST_CASE

namespace libsemigroups {

  namespace {

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
  }  // namespace

  LIBSEMIGROUPS_TEST_CASE("LowIndexCongruences",
                          "000",
                          "TODO",
                          "[quick][presentation]") {
    Presentation<word_type> p;
    p.alphabet({0, 1});
    presentation::add_pair(p, {0, 0, 0}, {0});
    presentation::add_pair(p, {1, 1}, {1});
    presentation::add_pair(p, {0, 1, 0, 1}, {0});

    LowIndexCongruences lic(p);
    REQUIRE(lic.run(4) == 6);
    /*REQUIRE(lic.number_of_cosets_active() == 1);
    REQUIRE(lic.word_graph().neighbor(0, 0) == 0);
    REQUIRE(lic.word_graph().neighbor(0, 1) == 0);

    ActionDigraph<size_t> ad(2, 2);
    ad.add_edge(0, 1, 0);
    ad.add_edge(0, 0, 1);
    ad.add_edge(1, 1, 0);
    ad.add_edge(1, 1, 1);
    check_compatibility(ad, p);

    REQUIRE(lic.run(4) == 0);
    REQUIRE(lic.number_of_cosets_active() == 2);
    REQUIRE(lic.word_graph().neighbor(0, 0) == 1);
    REQUIRE(lic.word_graph().neighbor(0, 1) == 0);
    REQUIRE(lic.word_graph().neighbor(1, 0) == 1);
    REQUIRE(lic.word_graph().neighbor(1, 1) == 1); */
    // check_compatibility(lic);

    // REQUIRE(lic.run(4));
    // REQUIRE(lic.number_of_cosets_active() == 3);
    // REQUIRE(lic.word_graph().neighbor(0, 0) == 1);
    // REQUIRE(lic.word_graph().neighbor(0, 1) == 1);
    // REQUIRE(lic.word_graph().neighbor(1, 0) == 1);
    // REQUIRE(lic.word_graph().neighbor(1, 1) == 1);
  }

  LIBSEMIGROUPS_TEST_CASE("LowIndexCongruences",
                          "001",
                          "TODO",
                          "[quick][presentation]") {
    Presentation<word_type> p;
    p.alphabet({0, 1, 2});
    presentation::add_pair(p, {0, 1, 0}, {0, 0});
    presentation::add_pair(p, {2, 2}, {0, 0});
    presentation::add_pair(p, {0, 0, 0}, {0, 0});
    presentation::add_pair(p, {2, 1}, {1, 2});
    presentation::add_pair(p, {2, 0}, {0, 0});
    presentation::add_pair(p, {1, 1}, {1});
    presentation::add_pair(p, {0, 2}, {0, 0});
    LowIndexCongruences lic(p);
    REQUIRE(lic.run(4) == 13);
  }

}  // namespace libsemigroups

// [[[0, 0, 0]],                        #1#
//   [[1, 0, 1], [1, 1, 1]],
//   [[1, 0, 2], [1, 1, 1], [1, 2, 1]],
//   [[1, 1, 1], [1, 1, 1]],            #2#
//   [[1, 1, 2], [1, 1, 1], [1, 1, 1]], #4#
//   [[1, 0, 1], [2, 1, 2], [2, 2, 2]],
//   [[1, 0, 2], [2, 1, 2], [2, 2, 2]],
//   [[1, 1, 2], [2, 1, 2], [2, 2, 2]], #3#
//   [[1, 2, 2], [2, 1, 2], [2, 2, 2]],
//   [[1, 0, 2], [2, 2, 2], [2, 2, 2]],
//   [[1, 2, 1], [2, 2, 2], [2, 2, 2]],
//   [[1, 2, 2], [2, 2, 2], [2, 2, 2]],
//   [[1, 2, 1], [1, 1, 1], [1, 2, 1]]]
//
// [[[0, 0]],                           #1#
// [[1, 0], [1, 1]],
// [[1, 1], [1, 1]],
// [[1, 2], [1, 1], [1, 2]],
// [[1, 2], [1, 1], [2, 2]],
// [[1, 2], [1, 1], [3, 2], [3, 3]]]
//
