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
#include "libsemigroups/sims1.hpp"  // for Sims1_
#include "libsemigroups/transf.hpp"
#include "libsemigroups/types.hpp"  // for word_type

namespace libsemigroups {
  using empty_word   = Presentation<word_type>::empty_word;
  using Sims1_       = Sims1<uint32_t>;
  using digraph_type = typename Sims1_::digraph_type;
  using node_type    = typename digraph_type::node_type;

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "000",
                          "fp example 1",
                          "[quick][presentation]") {
    auto rg = ReportGuard(false);

    Presentation<word_type> p(empty_word::yes);
    p.alphabet({0, 1});
    presentation::add_rule_and_check(p, {0, 0, 0}, {0});
    presentation::add_rule_and_check(p, {1, 1}, {1});
    presentation::add_rule_and_check(p, {0, 1, 0, 1}, {0});

    {
      Sims1_ S(p, congruence_kind::right);
      REQUIRE(S.number_of_congruences(5) == 6);

      auto it = S.cbegin(5);
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
      REQUIRE(*(it++) == action_digraph_helper::make<node_type>(0, 2));
      REQUIRE(*(it++) == action_digraph_helper::make<node_type>(0, 2));
    }
    // [[[0, 0]],
    // [[1, 2], [1, 1], [3, 2], [3, 3]],
    // [[1, 2], [1, 1], [2, 2]],
    // [[1, 2], [1, 1], [1, 2]],
    // [[1, 1], [1, 1]],
    // [[1, 0], [1, 1]]]
    {
      Sims1_ S(p, congruence_kind::left);
      REQUIRE(S.number_of_congruences(5) == 9);
      for (auto it = S.cbegin(5); it != S.cend(5); ++it) {
        REQUIRE(action_digraph_helper::follow_path_nc(*it, 0, {1, 0, 1, 0})
                == action_digraph_helper::follow_path_nc(*it, 0, {0}));
      }
    }
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "001",
                          "fp example 2",
                          "[quick][presentation]") {
    auto                    rg = ReportGuard(false);
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
      Sims1_ S(p, congruence_kind::right);
      REQUIRE(S.number_of_congruences(1) == 1);
      REQUIRE(S.number_of_congruences(2) == 3);
      REQUIRE(S.number_of_congruences(3) == 13);
      REQUIRE(S.number_of_congruences(4) == 36);
      REQUIRE(S.number_of_congruences(5) == 82);
      REQUIRE(S.number_of_congruences(6) == 135);
      REQUIRE(S.number_of_congruences(7) == 166);
      REQUIRE(S.number_of_congruences(8) == 175);
      REQUIRE(S.number_of_congruences(9) == 176);
      REQUIRE(S.number_of_congruences(10) == 176);

      auto it = S.cbegin(2);
      REQUIRE(*(it++)
              == action_digraph_helper::make<node_type>(2, {{0, 0, 0}}));
      REQUIRE(
          *(it++)
          == action_digraph_helper::make<node_type>(2, {{1, 1, 1}, {1, 1, 1}}));
      REQUIRE(
          *(it++)
          == action_digraph_helper::make<node_type>(2, {{1, 0, 1}, {1, 1, 1}}));
      REQUIRE(*(it++) == action_digraph_helper::make<node_type>(0, 3));
      REQUIRE(*(it++) == action_digraph_helper::make<node_type>(0, 3));
    }
    {
      Sims1_ S(p, congruence_kind::left);
      REQUIRE(S.number_of_congruences(11) == 176);
    }
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "002",
                          "ToddCoxeter failing example",
                          "[quick][presentation]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p(empty_word::no);
    //          a  A  b  B  c  C  e
    p.alphabet({0, 1, 2, 3, 4, 5, 6});
    presentation::identity(p, 6);
    presentation::inverses(p, {1, 0, 3, 2, 5, 4, 6}, 6);
    presentation::add_rule_and_check(p, {0, 0, 5, 0, 4}, {6});
    presentation::add_rule_and_check(p, {0, 4, 2, 2, 1, 5, 2}, {6});
    presentation::add_rule_and_check(p, {1, 3, 0, 2, 4, 4, 4}, {6});
    Sims1_ S(p, congruence_kind::right);
    REQUIRE(S.number_of_congruences(3) == 14);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "009",
                          "ToddCoxeter failing example",
                          "[quick][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p(empty_word::no);
    p.alphabet("aAbBcCe");
    presentation::identity(p, 'e');

    presentation::inverses(p, "AaBbCce", 'e');
    presentation::add_rule_and_check(p, "aaCac", "e");
    presentation::add_rule_and_check(p, "acbbACb", "e");
    presentation::add_rule_and_check(p, "ABabccc", "e");
    Sims1_ S(p, congruence_kind::right);
    REQUIRE(S.number_of_congruences(3) == 14);
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

    Sims1_ S(p, congruence_kind::right);
    REQUIRE(S.number_of_congruences(2) == 4);
    REQUIRE(S.number_of_congruences(3) == 7);
    REQUIRE(S.number_of_congruences(4) == 14);
    REQUIRE(S.number_of_congruences(5) == 23);
    REQUIRE(S.number_of_congruences(6) == 36);
    REQUIRE(S.number_of_congruences(7) == 51);
    REQUIRE(S.number_of_congruences(8) == 62);
    REQUIRE(S.number_of_congruences(9) == 74);
    REQUIRE(S.number_of_congruences(10) == 86);
    REQUIRE(S.number_of_congruences(11) == 95);
    REQUIRE(S.number_of_congruences(12) == 100);
    REQUIRE(S.number_of_congruences(13) == 102);
    REQUIRE(S.number_of_congruences(14) == 104);
    REQUIRE(S.number_of_congruences(15) == 105);
    REQUIRE(S.number_of_congruences(16) == 105);
    REQUIRE(S.number_of_congruences(17) == 105);
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

    Sims1_ S(p, congruence_kind::right);
    REQUIRE(S.number_of_congruences(10) == 135);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "005",
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
    Sims1_ C(p, congruence_kind::right);
    REQUIRE(C.number_of_congruences(27) == 287);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "006",
                          "FullTransformationMonoid(3) left",
                          "[quick][presentation]") {
    auto                   rg = ReportGuard(false);
    FroidurePin<Transf<3>> S(
        {Transf<3>({1, 2, 0}), Transf<3>({1, 0, 2}), Transf<3>({0, 1, 0})});
    REQUIRE(S.size() == 27);
    auto   p = make<Presentation<word_type>>(S);
    Sims1_ C(p, congruence_kind::left);
    REQUIRE(C.number_of_congruences(28) == 120);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "007",
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
      Sims1_ S(p, congruence_kind::right);
      REQUIRE(S.number_of_congruences(14) == 9);
    }
    {
      Sims1_ S(p, congruence_kind::left);
      REQUIRE(S.number_of_congruences(14) == 9);
    }
  }

  LIBSEMIGROUPS_TEST_CASE("Sims1",
                          "008",
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
      Sims1_ S(p, congruence_kind::right);
      REQUIRE(S.number_of_congruences(14) == 79);
    }
    {
      Sims1_ S(p, congruence_kind::left);
      REQUIRE(S.number_of_congruences(14) == 79);
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
