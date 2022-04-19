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
#include "libsemigroups/sims1.hpp"  // for Sims1
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

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "000",
                          "fp example 1",
                          "[quick][presentation]") {
    auto rg         = ReportGuard(false);
    using WordGraph = typename Sims1::word_graph_type;
    using node_type = typename WordGraph::node_type;

    Presentation<word_type> p(empty_word::yes);
    p.alphabet({0, 1});
    presentation::add_rule_and_check(p, {0, 0, 0}, {0});
    presentation::add_rule_and_check(p, {1, 1}, {1});
    presentation::add_rule_and_check(p, {0, 1, 0, 1}, {0});

    {
      Sims1 lic(p);
      REQUIRE(lic.number_of_congruences(5) == 6);

      auto it = lic.cbegin(5);
      REQUIRE(*(it++) == action_digraph_helper::make<node_type>(5, {{0, 0}}));
      REQUIRE(*(it++)
              == action_digraph_helper::make<node_type>(
                  5, {{1, 2}, {1, 1}, {3, 2}, {3, 3}}));
      REQUIRE(*(it++)
              == action_digraph_helper::make<node_type>(
                  5, {{1, 2}, {1, 1}, {2, 2}}));
      REQUIRE(*(it++)
              == action_digraph_helper::make<node_type>(
                  5, {{1, 2}, {1, 1}, {1, 2}}));
      REQUIRE(*(it++)
              == action_digraph_helper::make<node_type>(5, {{1, 1}, {1, 1}}));
      REQUIRE(*(it++)
              == action_digraph_helper::make<node_type>(5, {{1, 0}, {1, 1}}));
      REQUIRE(*(it++) == WordGraph(0, 2));
      REQUIRE(*(it++) == WordGraph(0, 2));
    }
    // [[[0, 0]],
    // [[1, 2], [1, 1], [3, 2], [3, 3]],
    // [[1, 2], [1, 1], [2, 2]],
    // [[1, 2], [1, 1], [1, 2]],
    // [[1, 1], [1, 1]],
    // [[1, 0], [1, 1]]]
    {
      Sims1 lic(p, congruence_kind::left);
      REQUIRE(lic.number_of_congruences(5) == 9);
      for (auto it = lic.cbegin(5); it != lic.cend(5); ++it) {
        REQUIRE(action_digraph_helper::follow_path_nc(*it, 0, {1, 0, 1, 0})
                == action_digraph_helper::follow_path_nc(*it, 0, {0}));
      }
    }
    {
      /*Sims1 lic(p, congruence_kind::twosided);
      // REQUIRE(lic.number_of_congruences(5) == 6); # THIS IS CORRECT for
      // 2-sided congruences!!!
      REQUIRE(std::count_if(lic.cbegin(5),
                            lic.cend(5),
                            [](auto const& d) {
                              return action_digraph_helper::follow_path_nc(
                                         d, 0, {1, 0, 1, 0})
                                     == action_digraph_helper::follow_path_nc(
                                         d, 0, {0});
                            })
              == 0);*/
    }
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "001",
                          "fp example 2",
                          "[quick][presentation]") {
    auto rg         = ReportGuard(false);
    using WordGraph = typename Sims1::word_graph_type;
    using node_type = typename WordGraph::node_type;

    Presentation<word_type> p(empty_word::yes);
    p.alphabet({0, 1, 2});
    presentation::add_rule_and_check(p, {0, 1, 0}, {0, 0});
    presentation::add_rule_and_check(p, {2, 2}, {0, 0});
    presentation::add_rule_and_check(p, {0, 0, 0}, {0, 0});
    presentation::add_rule_and_check(p, {2, 1}, {1, 2});
    presentation::add_rule_and_check(p, {2, 0}, {0, 0});
    presentation::add_rule_and_check(p, {1, 1}, {1});
    presentation::add_rule_and_check(p, {0, 2}, {0, 0});

    {
      Sims1 lic(p);
      REQUIRE(lic.number_of_congruences(1) == 1);
      REQUIRE(lic.number_of_congruences(2) == 3);
      REQUIRE(lic.number_of_congruences(3) == 13);
      REQUIRE(lic.number_of_congruences(4) == 36);
      REQUIRE(lic.number_of_congruences(5) == 82);
      REQUIRE(lic.number_of_congruences(6) == 135);
      REQUIRE(lic.number_of_congruences(7) == 166);
      REQUIRE(lic.number_of_congruences(8) == 175);
      REQUIRE(lic.number_of_congruences(9) == 176);
      REQUIRE(lic.number_of_congruences(10) == 176);

      auto it = lic.cbegin(2);
      REQUIRE(*(it++)
              == action_digraph_helper::make<node_type>(2, {{0, 0, 0}}));
      REQUIRE(
          *(it++)
          == action_digraph_helper::make<node_type>(2, {{1, 1, 1}, {1, 1, 1}}));
      REQUIRE(
          *(it++)
          == action_digraph_helper::make<node_type>(2, {{1, 0, 1}, {1, 1, 1}}));
      REQUIRE(*(it++) == WordGraph(0, 3));
      REQUIRE(*(it++) == WordGraph(0, 3));
    }
    {
      Sims1 lic(p, congruence_kind::left);
      REQUIRE(lic.number_of_congruences(11) == 176);
    }
    {
      // Sims1 lic(p, congruence_kind::twosided);
      // REQUIRE(lic.number_of_congruences(10) == 83);
    }
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "002",
                          "ToddCoxeter failing example",
                          "[quick][presentation]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p(empty_word::yes);
    //          a  A  b  B  c  C  e
    p.alphabet({0, 1, 2, 3, 4, 5, 6});
    presentation::identity(p, 6);
    presentation::inverses(p, {1, 0, 3, 2, 5, 4, 6}, 6);
    presentation::add_rule_and_check(p, {0, 0, 5, 0, 4}, {6});
    presentation::add_rule_and_check(p, {0, 4, 2, 2, 1, 5, 2}, {6});
    presentation::add_rule_and_check(p, {1, 3, 0, 2, 4, 4, 4}, {6});
    Sims1 lic(p);
    REQUIRE(lic.number_of_congruences(3) == 15);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "003",
                          "PartitionMonoid(2) right",
                          "[quick][presentation]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p(empty_word::no);
    p.alphabet({0, 1, 2, 3});
    presentation::identity(p, 0);
    presentation::add_rule_and_check(p, {1, 1}, {0});
    presentation::add_rule_and_check(p, {1, 3}, {3});
    presentation::add_rule_and_check(p, {2, 2}, {2});
    presentation::add_rule_and_check(p, {3, 1}, {3});
    presentation::add_rule_and_check(p, {3, 3}, {3});
    presentation::add_rule_and_check(p, {2, 3, 2}, {2});
    presentation::add_rule_and_check(p, {3, 2, 3}, {3});
    presentation::add_rule_and_check(p, {1, 2, 1, 2}, {2, 1, 2});
    presentation::add_rule_and_check(p, {2, 1, 2, 1}, {2, 1, 2});

    Sims1 lic(p);
    REQUIRE(lic.number_of_congruences(2) == 4);
    REQUIRE(lic.number_of_congruences(3) == 7);
    REQUIRE(lic.number_of_congruences(4) == 14);
    REQUIRE(lic.number_of_congruences(5) == 23);
    REQUIRE(lic.number_of_congruences(6) == 36);
    REQUIRE(lic.number_of_congruences(7) == 51);
    REQUIRE(lic.number_of_congruences(8) == 62);
    REQUIRE(lic.number_of_congruences(9) == 74);
    REQUIRE(lic.number_of_congruences(10) == 86);
    REQUIRE(lic.number_of_congruences(11) == 95);
    REQUIRE(lic.number_of_congruences(12) == 100);
    REQUIRE(lic.number_of_congruences(13) == 102);
    REQUIRE(lic.number_of_congruences(14) == 104);
    REQUIRE(lic.number_of_congruences(15) == 105);
    REQUIRE(lic.number_of_congruences(16) == 105);
    REQUIRE(lic.number_of_congruences(17) == 105);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "006",
                          "PartitionMonoid(2) 2-sided",
                          "[fail][presentation]") {
    Presentation<word_type> p;
    p.alphabet({0, 1, 2, 3});
    presentation::add_rule_and_check(p, {1, 1}, {0});
    presentation::add_rule_and_check(p, {1, 3}, {3});
    presentation::add_rule_and_check(p, {2, 2}, {2});
    presentation::add_rule_and_check(p, {3, 1}, {3});
    presentation::add_rule_and_check(p, {3, 3}, {3});
    presentation::add_rule_and_check(p, {2, 3, 2}, {2});
    presentation::add_rule_and_check(p, {3, 2, 3}, {3});
    presentation::add_rule_and_check(p, {1, 2, 1, 2}, {2, 1, 2});
    presentation::add_rule_and_check(p, {2, 1, 2, 1}, {2, 1, 2});
    presentation::identity(p, 0);
    REQUIRE(std::distance(p.cbegin(), p.cend()) == 32);

    Sims1 lic(p, congruence_kind::twosided);
    REQUIRE(
        std::distance(lic.presentation().cbegin(), lic.presentation().cend())
        == 64);
    REQUIRE(std::equal(lic.presentation().cbegin(),
                       lic.presentation().cbegin() + 32,
                       p.cbegin(),
                       p.cend()));
    REQUIRE(*(lic.presentation().cbegin() + 32) == word_type({1, 1}));
    REQUIRE(*(lic.presentation().cbegin() + 33) == word_type({0}));
    REQUIRE(*(lic.presentation().cbegin() + 34) == word_type({3, 1}));
    // REQUIRE(lic.number_of_congruences(2) == 4);
    // REQUIRE(lic.number_of_congruences(3) == 7);
    // REQUIRE(lic.number_of_congruences(4) == 14);
    // REQUIRE(lic.number_of_congruences(5) == 23);
    // REQUIRE(lic.number_of_congruences(6) == 36);
    // REQUIRE(lic.number_of_congruences(7) == 51);
    // REQUIRE(lic.number_of_congruences(8) == 62);
    // REQUIRE(lic.number_of_congruences(9) == 74);
    // REQUIRE(lic.number_of_congruences(10) == 86);
    // REQUIRE(lic.number_of_congruences(11) == 95);
    // REQUIRE(lic.number_of_congruences(12) == 100);
    // REQUIRE(lic.number_of_congruences(13) == 102);
    // REQUIRE(lic.number_of_congruences(14) == 104);
    // REQUIRE(lic.number_of_congruences(15) == 105);
    // REQUIRE(lic.number_of_congruences(16) == 105);
    // FIXME This isn't right, there are only 13 2-sided congruences, but at
    // the same time the presentation is symmetric so I can't see how this
    // would be any different (i.e. the relations in lic in this case are just
    // two copies of the same thing, and so of course the answer is the same.
    // But then why does it work for the full transformation monoid below?
    REQUIRE(lic.number_of_congruences(17) == 13);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "004",
                          "PartitionMonoid(3)",
                          "[quick][presentation]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p(empty_word::no);
    p.alphabet({0, 1, 2, 3, 4});
    presentation::add_rule_and_check(p, {0, 0}, {0});
    presentation::add_rule_and_check(p, {0, 1}, {1});
    presentation::add_rule_and_check(p, {0, 2}, {2});
    presentation::add_rule_and_check(p, {0, 3}, {3});
    presentation::add_rule_and_check(p, {0, 4}, {4});
    presentation::add_rule_and_check(p, {1, 0}, {1});
    presentation::add_rule_and_check(p, {2, 0}, {2});
    presentation::add_rule_and_check(p, {2, 2}, {0});
    presentation::add_rule_and_check(p, {2, 4}, {4});
    presentation::add_rule_and_check(p, {3, 0}, {3});
    presentation::add_rule_and_check(p, {3, 3}, {3});
    presentation::add_rule_and_check(p, {4, 0}, {4});
    presentation::add_rule_and_check(p, {4, 2}, {4});
    presentation::add_rule_and_check(p, {4, 4}, {4});
    presentation::add_rule_and_check(p, {1, 1, 1}, {0});
    presentation::add_rule_and_check(p, {1, 1, 2}, {2, 1});
    presentation::add_rule_and_check(p, {1, 2, 1}, {2});
    presentation::add_rule_and_check(p, {2, 1, 1}, {1, 2});
    presentation::add_rule_and_check(p, {2, 1, 2}, {1, 1});
    presentation::add_rule_and_check(p, {2, 1, 4}, {1, 1, 4});
    presentation::add_rule_and_check(p, {3, 1, 2}, {1, 2, 3});
    presentation::add_rule_and_check(p, {3, 4, 3}, {3});
    presentation::add_rule_and_check(p, {4, 1, 2}, {4, 1, 1});
    presentation::add_rule_and_check(p, {4, 3, 4}, {4});
    presentation::add_rule_and_check(p, {1, 1, 3, 1}, {2, 3, 2});
    presentation::add_rule_and_check(p, {1, 1, 3, 2}, {2, 3, 1});
    presentation::add_rule_and_check(p, {1, 2, 3, 1}, {3, 2});
    presentation::add_rule_and_check(p, {1, 2, 3, 2}, {3, 1});
    presentation::add_rule_and_check(p, {1, 2, 3, 4}, {3, 1, 4});
    presentation::add_rule_and_check(p, {1, 3, 2, 3}, {3, 1, 3});
    presentation::add_rule_and_check(p, {1, 4, 1, 4}, {4, 1, 4});
    presentation::add_rule_and_check(p, {2, 1, 3, 1}, {1, 3, 2});
    presentation::add_rule_and_check(p, {2, 1, 3, 2}, {1, 3, 1});
    presentation::add_rule_and_check(p, {2, 1, 3, 4}, {1, 3, 1, 4});
    presentation::add_rule_and_check(p, {2, 3, 1, 3}, {1, 3, 1, 3});
    presentation::add_rule_and_check(p, {2, 3, 1, 4}, {1, 1, 3, 4});
    presentation::add_rule_and_check(p, {2, 3, 2, 3}, {3, 2, 3});
    presentation::add_rule_and_check(p, {3, 1, 3, 2}, {3, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 4, 3}, {1, 2, 3});
    presentation::add_rule_and_check(p, {3, 2, 3, 2}, {3, 2, 3});
    presentation::add_rule_and_check(p, {4, 1, 1, 4}, {4, 1, 4});
    presentation::add_rule_and_check(p, {4, 1, 3, 2}, {4, 1, 3, 1});
    presentation::add_rule_and_check(p, {4, 1, 4, 1}, {4, 1, 4});
    presentation::add_rule_and_check(p, {1, 3, 1, 1, 3}, {3, 2, 1, 3});
    presentation::add_rule_and_check(p, {1, 3, 4, 1, 4}, {4, 1, 3, 4});
    presentation::add_rule_and_check(p, {2, 3, 1, 1, 3}, {3, 1, 1, 3});
    presentation::add_rule_and_check(p, {2, 3, 2, 1, 3}, {1, 3, 2, 1, 3});
    presentation::add_rule_and_check(p, {2, 3, 4, 1, 3}, {1, 3, 4, 1, 3});
    presentation::add_rule_and_check(p, {2, 3, 4, 1, 4}, {1, 4, 1, 3, 4});
    presentation::add_rule_and_check(p, {3, 1, 1, 4, 1}, {1, 1, 4, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 3, 1, 1}, {3, 2, 1, 3});
    presentation::add_rule_and_check(p, {3, 2, 3, 1, 1}, {3, 1, 1, 3});
    presentation::add_rule_and_check(p, {3, 4, 1, 1, 3}, {1, 2, 3});
    presentation::add_rule_and_check(p, {3, 4, 1, 4, 3}, {1, 1, 4, 1, 3});
    presentation::add_rule_and_check(p, {4, 1, 1, 3, 4}, {4, 3, 1, 4});
    presentation::add_rule_and_check(p, {4, 1, 3, 1, 1}, {1, 3, 1, 1, 4});
    presentation::add_rule_and_check(p, {4, 1, 3, 1, 3}, {4, 3, 1, 3});
    presentation::add_rule_and_check(p, {4, 1, 3, 1, 4}, {4, 1, 3, 4});
    presentation::add_rule_and_check(p, {4, 1, 3, 4, 1}, {4, 1, 3, 4});
    presentation::add_rule_and_check(p, {4, 1, 4, 3, 2}, {4, 1, 4, 3, 1});
    presentation::add_rule_and_check(p, {1, 1, 3, 4, 1, 3}, {3, 1, 4, 1, 3});
    presentation::add_rule_and_check(p, {1, 1, 4, 1, 3, 4}, {3, 4, 1, 4});
    presentation::add_rule_and_check(p, {1, 3, 1, 1, 4, 3}, {4, 3, 2, 1, 3});
    presentation::add_rule_and_check(p, {1, 3, 1, 3, 1, 3}, {3, 1, 3, 1, 3});
    presentation::add_rule_and_check(p, {1, 3, 1, 4, 1, 3}, {3, 4, 1, 3});
    presentation::add_rule_and_check(p, {1, 4, 3, 1, 1, 4}, {4, 3, 1, 1, 4});
    presentation::add_rule_and_check(p, {2, 3, 1, 1, 4, 3}, {1, 4, 3, 2, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 1, 3, 4, 1}, {3, 1, 4, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 1, 4, 3, 1}, {1, 1, 4, 3, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 3, 1, 3, 1}, {3, 1, 3, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 3, 1, 4, 1}, {3, 4, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 4, 1, 1, 3}, {3});
    presentation::add_rule_and_check(p, {4, 1, 4, 3, 1, 1}, {4, 3, 1, 1, 4});
    presentation::add_rule_and_check(p, {4, 1, 4, 3, 1, 4}, {4, 1, 4});
    presentation::add_rule_and_check(p, {4, 3, 1, 3, 1, 4}, {1, 3, 1, 1, 4});
    presentation::add_rule_and_check(
        p, {1, 1, 4, 3, 1, 3, 1}, {3, 1, 1, 4, 3, 2});
    presentation::add_rule_and_check(p, {1, 1, 4, 3, 2, 1, 3}, {3, 1, 1, 4, 3});
    presentation::add_rule_and_check(
        p, {1, 3, 1, 3, 4, 1, 3}, {3, 1, 3, 4, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 1, 4, 3, 2, 1}, {3, 1, 1, 4, 3});
    presentation::add_rule_and_check(
        p, {3, 1, 3, 1, 3, 4, 1}, {3, 1, 3, 4, 1, 3});
    presentation::add_rule_and_check(
        p, {4, 3, 1, 1, 4, 3, 2}, {4, 1, 4, 3, 1, 3, 1});
    presentation::add_rule_and_check(
        p, {3, 1, 1, 4, 3, 2, 3, 1}, {3, 1, 1, 4, 3, 2, 3});
    presentation::add_rule_and_check(
        p, {3, 1, 1, 4, 3, 2, 3, 4, 1}, {1, 1, 4, 3, 1, 3, 4, 1, 3});

    Sims1 lic(p);
    REQUIRE(lic.number_of_congruences(10) == 135);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "005",
                          "PartitionMonoid(3)",
                          "[extreme][presentation]") {
    auto                    rg = ReportGuard(true);
    Presentation<word_type> p;
    p.alphabet({0, 1, 2, 3, 4});
    presentation::add_rule_and_check(p, {0, 0}, {0});
    presentation::add_rule_and_check(p, {0, 1}, {1});
    presentation::add_rule_and_check(p, {0, 2}, {2});
    presentation::add_rule_and_check(p, {0, 3}, {3});
    presentation::add_rule_and_check(p, {0, 4}, {4});
    presentation::add_rule_and_check(p, {1, 0}, {1});
    presentation::add_rule_and_check(p, {2, 0}, {2});
    presentation::add_rule_and_check(p, {2, 2}, {0});
    presentation::add_rule_and_check(p, {2, 4}, {4});
    presentation::add_rule_and_check(p, {3, 0}, {3});
    presentation::add_rule_and_check(p, {3, 3}, {3});
    presentation::add_rule_and_check(p, {4, 0}, {4});
    presentation::add_rule_and_check(p, {4, 2}, {4});
    presentation::add_rule_and_check(p, {4, 4}, {4});
    presentation::add_rule_and_check(p, {1, 1, 1}, {0});
    presentation::add_rule_and_check(p, {1, 1, 2}, {2, 1});
    presentation::add_rule_and_check(p, {1, 2, 1}, {2});
    presentation::add_rule_and_check(p, {2, 1, 1}, {1, 2});
    presentation::add_rule_and_check(p, {2, 1, 2}, {1, 1});
    presentation::add_rule_and_check(p, {2, 1, 4}, {1, 1, 4});
    presentation::add_rule_and_check(p, {3, 1, 2}, {1, 2, 3});
    presentation::add_rule_and_check(p, {3, 4, 3}, {3});
    presentation::add_rule_and_check(p, {4, 1, 2}, {4, 1, 1});
    presentation::add_rule_and_check(p, {4, 3, 4}, {4});
    presentation::add_rule_and_check(p, {1, 1, 3, 1}, {2, 3, 2});
    presentation::add_rule_and_check(p, {1, 1, 3, 2}, {2, 3, 1});
    presentation::add_rule_and_check(p, {1, 2, 3, 1}, {3, 2});
    presentation::add_rule_and_check(p, {1, 2, 3, 2}, {3, 1});
    presentation::add_rule_and_check(p, {1, 2, 3, 4}, {3, 1, 4});
    presentation::add_rule_and_check(p, {1, 3, 2, 3}, {3, 1, 3});
    presentation::add_rule_and_check(p, {1, 4, 1, 4}, {4, 1, 4});
    presentation::add_rule_and_check(p, {2, 1, 3, 1}, {1, 3, 2});
    presentation::add_rule_and_check(p, {2, 1, 3, 2}, {1, 3, 1});
    presentation::add_rule_and_check(p, {2, 1, 3, 4}, {1, 3, 1, 4});
    presentation::add_rule_and_check(p, {2, 3, 1, 3}, {1, 3, 1, 3});
    presentation::add_rule_and_check(p, {2, 3, 1, 4}, {1, 1, 3, 4});
    presentation::add_rule_and_check(p, {2, 3, 2, 3}, {3, 2, 3});
    presentation::add_rule_and_check(p, {3, 1, 3, 2}, {3, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 4, 3}, {1, 2, 3});
    presentation::add_rule_and_check(p, {3, 2, 3, 2}, {3, 2, 3});
    presentation::add_rule_and_check(p, {4, 1, 1, 4}, {4, 1, 4});
    presentation::add_rule_and_check(p, {4, 1, 3, 2}, {4, 1, 3, 1});
    presentation::add_rule_and_check(p, {4, 1, 4, 1}, {4, 1, 4});
    presentation::add_rule_and_check(p, {1, 3, 1, 1, 3}, {3, 2, 1, 3});
    presentation::add_rule_and_check(p, {1, 3, 4, 1, 4}, {4, 1, 3, 4});
    presentation::add_rule_and_check(p, {2, 3, 1, 1, 3}, {3, 1, 1, 3});
    presentation::add_rule_and_check(p, {2, 3, 2, 1, 3}, {1, 3, 2, 1, 3});
    presentation::add_rule_and_check(p, {2, 3, 4, 1, 3}, {1, 3, 4, 1, 3});
    presentation::add_rule_and_check(p, {2, 3, 4, 1, 4}, {1, 4, 1, 3, 4});
    presentation::add_rule_and_check(p, {3, 1, 1, 4, 1}, {1, 1, 4, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 3, 1, 1}, {3, 2, 1, 3});
    presentation::add_rule_and_check(p, {3, 2, 3, 1, 1}, {3, 1, 1, 3});
    presentation::add_rule_and_check(p, {3, 4, 1, 1, 3}, {1, 2, 3});
    presentation::add_rule_and_check(p, {3, 4, 1, 4, 3}, {1, 1, 4, 1, 3});
    presentation::add_rule_and_check(p, {4, 1, 1, 3, 4}, {4, 3, 1, 4});
    presentation::add_rule_and_check(p, {4, 1, 3, 1, 1}, {1, 3, 1, 1, 4});
    presentation::add_rule_and_check(p, {4, 1, 3, 1, 3}, {4, 3, 1, 3});
    presentation::add_rule_and_check(p, {4, 1, 3, 1, 4}, {4, 1, 3, 4});
    presentation::add_rule_and_check(p, {4, 1, 3, 4, 1}, {4, 1, 3, 4});
    presentation::add_rule_and_check(p, {4, 1, 4, 3, 2}, {4, 1, 4, 3, 1});
    presentation::add_rule_and_check(p, {1, 1, 3, 4, 1, 3}, {3, 1, 4, 1, 3});
    presentation::add_rule_and_check(p, {1, 1, 4, 1, 3, 4}, {3, 4, 1, 4});
    presentation::add_rule_and_check(p, {1, 3, 1, 1, 4, 3}, {4, 3, 2, 1, 3});
    presentation::add_rule_and_check(p, {1, 3, 1, 3, 1, 3}, {3, 1, 3, 1, 3});
    presentation::add_rule_and_check(p, {1, 3, 1, 4, 1, 3}, {3, 4, 1, 3});
    presentation::add_rule_and_check(p, {1, 4, 3, 1, 1, 4}, {4, 3, 1, 1, 4});
    presentation::add_rule_and_check(p, {2, 3, 1, 1, 4, 3}, {1, 4, 3, 2, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 1, 3, 4, 1}, {3, 1, 4, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 1, 4, 3, 1}, {1, 1, 4, 3, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 3, 1, 3, 1}, {3, 1, 3, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 3, 1, 4, 1}, {3, 4, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 4, 1, 1, 3}, {3});
    presentation::add_rule_and_check(p, {4, 1, 4, 3, 1, 1}, {4, 3, 1, 1, 4});
    presentation::add_rule_and_check(p, {4, 1, 4, 3, 1, 4}, {4, 1, 4});
    presentation::add_rule_and_check(p, {4, 3, 1, 3, 1, 4}, {1, 3, 1, 1, 4});
    presentation::add_rule_and_check(
        p, {1, 1, 4, 3, 1, 3, 1}, {3, 1, 1, 4, 3, 2});
    presentation::add_rule_and_check(p, {1, 1, 4, 3, 2, 1, 3}, {3, 1, 1, 4, 3});
    presentation::add_rule_and_check(
        p, {1, 3, 1, 3, 4, 1, 3}, {3, 1, 3, 4, 1, 3});
    presentation::add_rule_and_check(p, {3, 1, 1, 4, 3, 2, 1}, {3, 1, 1, 4, 3});
    presentation::add_rule_and_check(
        p, {3, 1, 3, 1, 3, 4, 1}, {3, 1, 3, 4, 1, 3});
    presentation::add_rule_and_check(
        p, {4, 3, 1, 1, 4, 3, 2}, {4, 1, 4, 3, 1, 3, 1});
    presentation::add_rule_and_check(
        p, {3, 1, 1, 4, 3, 2, 3, 1}, {3, 1, 1, 4, 3, 2, 3});
    presentation::add_rule_and_check(
        p, {3, 1, 1, 4, 3, 2, 3, 4, 1}, {1, 1, 4, 3, 1, 3, 4, 1, 3});

    Sims1 lic(p, congruence_kind::twosided);
    REQUIRE(lic.number_of_congruences(204) == 16);
    // FIXME should be 16!
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "007",
                          "FullTransformationMonoid(3) right",
                          "[quick][presentation]") {
    auto                   rg = ReportGuard(false);
    FroidurePin<Transf<3>> S({Transf<3>::make({1, 2, 0}),
                              Transf<3>::make({1, 0, 2}),
                              Transf<3>::make({0, 1, 0})});
    REQUIRE(S.size() == 27);
    REQUIRE(S.number_of_generators() == 3);
    REQUIRE(S.number_of_rules() == 16);
    auto p = make<Presentation<word_type>>(S);
    REQUIRE(static_cast<size_t>(std::distance(p.cbegin(), p.cend()))
            == 2 * S.number_of_rules());
    Sims1 lic(p);
    REQUIRE(lic.number_of_congruences(27) == 287);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "008",
                          "FullTransformationMonoid(3) left",
                          "[quick][presentation]") {
    auto                   rg = ReportGuard(false);
    FroidurePin<Transf<3>> S(
        {Transf<3>({1, 2, 0}), Transf<3>({1, 0, 2}), Transf<3>({0, 1, 0})});
    REQUIRE(S.size() == 27);
    auto  p = make<Presentation<word_type>>(S);
    Sims1 lic(p, congruence_kind::left);
    REQUIRE(lic.number_of_congruences(28) == 120);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "009",
                          "FullTransformationMonoid(3) 2-sided",
                          "[fail][presentation]") {
    auto                   rg = ReportGuard(false);
    FroidurePin<Transf<3>> S(
        {Transf<3>({1, 2, 0}), Transf<3>({1, 0, 2}), Transf<3>({0, 1, 0})});
    REQUIRE(S.size() == 27);
    REQUIRE(S.is_monoid());
    auto  p = make<Presentation<word_type>>(S);
    Sims1 lic(p, congruence_kind::twosided);
    REQUIRE(lic.number_of_congruences(27) == 7);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "010",
                          "PartitionMonoid(2) 2-sided from FroidurePin",
                          "[fail][presentation]") {
    FroidurePin<Bipartition> S({Bipartition::make({{1, -1}, {2, -2}}),
                                Bipartition::make({{1, -2}, {2, -1}}),
                                Bipartition::make({{1}, {2, -2}, {-1}}),
                                Bipartition::make({{1, 2, -1, -2}})});

    REQUIRE(S.size() == 15);
    auto p = make<Presentation<word_type>>(S);
    REQUIRE(std::distance(p.cbegin(), p.cend()) == 32);

    Sims1 lic(p, congruence_kind::twosided);
    REQUIRE(lic.number_of_congruences(16) == 13);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "011",
                          "TemperleyLieb(3) from presentation",
                          "[quick][presentation]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p(empty_word::yes);
    p.alphabet(2);
    for (auto const& rel : TemperleyLieb(3)) {
      p.add_rule_and_check(rel.first.cbegin(),
                           rel.first.cend(),
                           rel.second.cbegin(),
                           rel.second.cend());
    }
    {
      Sims1 lic(p, congruence_kind::right);
      REQUIRE(lic.number_of_congruences(14) == 9);
    }
    {
      Sims1 lic(p, congruence_kind::left);
      REQUIRE(lic.number_of_congruences(14) == 9);
    }
    {
      // Sims1 lic(p, congruence_kind::twosided);
      // REQUIRE(lic.number_of_congruences(14) == 5);
    }
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "012",
                          "TemperleyLieb(4) from presentation",
                          "[quick][presentation]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p(empty_word::yes);
    p.alphabet(3);
    for (auto const& rel : TemperleyLieb(4)) {
      p.add_rule_and_check(rel.first.cbegin(),
                           rel.first.cend(),
                           rel.second.cbegin(),
                           rel.second.cend());
    }
    {
      Sims1 lic(p, congruence_kind::right);
      REQUIRE(lic.number_of_congruences(14) == 79);
    }
    {
      Sims1 lic(p, congruence_kind::left);
      REQUIRE(lic.number_of_congruences(14) == 79);
    }
    {
      // Sims1 lic(p, congruence_kind::twosided);
      // REQUIRE(lic.number_of_congruences(14) == 9);
    }
  }

}  // namespace libsemigroups

// [[[0, 0, 0]],            #1#
// [[0, 0, 1], [1, 0, 1]],  #2#
// [[0, 1, 0], [1, 1, 0]],
// [[0, 1, 1], [1, 1, 1]]]  #3#

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
