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

  namespace {

    template <typename T>
    void check_compatibility(ActionDigraph<T> const &       d,
                             Presentation<word_type> const &p) {
      for (size_t i = 0; i < d.number_of_nodes(); ++i) {
        for (auto it = p.cbegin(); it != p.cend(); it += 2) {
          // std::cout << " i = " << i << std::endl;
          // std::cout << " it = " << *it << std::endl;
          // std::cout << " it + 1 = " << *(it + 1) << std::endl;
          REQUIRE(action_digraph_helper::follow_path_nc(d, i, *it)
                  == action_digraph_helper::follow_path_nc(d, i, *(it + 1)));
        }
      }
    }
  }  // namespace

  LIBSEMIGROUPS_TEST_CASE("Sims2",
                          "000",
                          "fp example 1",
                          "[quick][presentation]") {
    auto rg            = ReportGuard(false);
    using digraph_type = typename Sims2Graph::digraph_type;
    using node_type    = typename digraph_type::node_type;

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
                  4, {{1, 2}, {1, 3}, {1, 2}, {1, 3}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(
                  4, {{1, 2}, {1, 1}, {3, 2}, {3, 3}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(
                  4, {{1, 2}, {1, 2}, {1, 2}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(
                  4, {{1, 2}, {1, 1}, {2, 2}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(
                  4, {{1, 2}, {1, 1}, {1, 2}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(
                  4, {{1, 2}, {1, 1}, {1, 2}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(4, {{1, 1}, {1, 1}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(4, {{1, 1}, {1, 1}}));
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(4, {{1, 0}, {1, 1}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(4, {{1, 0}, {1, 1}}));

      ++it;
      REQUIRE(it == s.cend(4));
      REQUIRE(s.number_of_congruences(4) == 6);
      REQUIRE(s.number_of_congruences(5) == 6);
      REQUIRE(s.number_of_congruences(6) == 6);
    }
  }

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

  LIBSEMIGROUPS_TEST_CASE("Sims2",
                          "001",
                          "fp example 2",
                          "[quick][presentation]") {
    auto rg            = ReportGuard(false);
    using digraph_type = typename Sims2Graph::digraph_type;
    using node_type    = typename digraph_type::node_type;

    Presentation<word_type> p(empty_word::yes);
    p.alphabet({0, 1, 2});
    presentation::add_rule_and_check(p, {0, 1, 0}, {0, 0});
    presentation::add_rule_and_check(p, {2, 2}, {0, 0});
    presentation::add_rule_and_check(p, {0, 0, 0}, {0, 0});
    presentation::add_rule_and_check(p, {2, 1}, {1, 2});
    presentation::add_rule_and_check(p, {2, 0}, {0, 0});
    presentation::add_rule_and_check(p, {1, 1}, {1});
    presentation::add_rule_and_check(p, {0, 2}, {0, 0});

    Sims2 s(p);
    for (auto it = s.cbegin(9); it != s.cend(9); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(1) == 1);
    REQUIRE(s.number_of_congruences(2) == 3);
    REQUIRE(s.number_of_congruences(3) == 10);
    REQUIRE(s.number_of_congruences(4) == 20);
    REQUIRE(s.number_of_congruences(5) == 39);
    REQUIRE(s.number_of_congruences(6) == 61);
    REQUIRE(s.number_of_congruences(7) == 76);
    REQUIRE(s.number_of_congruences(8) == 82);
    REQUIRE(s.number_of_congruences(9) == 83);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims2",
                          "002",
                          "PartitionMonoid(2) 2-sided",
                          "[quick][presentation]") {
    using digraph_type = typename Sims2Graph::digraph_type;
    using node_type    = typename digraph_type::node_type;
    Presentation<word_type> p(empty_word::no);
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
    Sims2 s(p);
    REQUIRE(s.number_of_congruences(1) == 1);
    {
      auto it = s.cbegin(2);
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 1, 2, 2}, {1, 1, 2, 2}, {2, 2, 2, 2}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 1, 2, 2}, {1, 1, 2, 2}, {2, 2, 2, 2}}));
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
      ++it;
      REQUIRE(it->left()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 1, 1, 1}, {1, 1, 1, 1}}));
      REQUIRE(it->right()
              == action_digraph_helper::make<node_type>(
                  3, {{1, 1, 1, 1}, {1, 1, 1, 1}}));
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
      ++it;
      REQUIRE(it == s.cend(4));

      // [
      //   [ [[ 0, 0, 0, 0 ]], [[ 0, 0, 0, 0 ]] ],
      //   [
      //     [ [ 0, 0, 1, 1 ], [ 1, 1, 1, 1 ] ],
      //     [ [ 0, 0, 1, 1 ], [ 1, 1, 1, 1 ] ]
      //   ]
      // ]

      REQUIRE(s.number_of_congruences(2)
              == 2);  // this is correct verified with GAP
    }
    for (auto it = s.cbegin(3); it != s.cend(3); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(3) == 5);

    for (auto it = s.cbegin(4); it != s.cend(4); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(4) == 7);

    for (auto it = s.cbegin(5); it != s.cend(5); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(5) == 8);

    for (auto it = s.cbegin(6); it != s.cend(6); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(6) == 9);

    for (auto it = s.cbegin(7); it != s.cend(7); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(7) == 9);

    for (auto it = s.cbegin(8); it != s.cend(8); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(8) == 9);

    for (auto it = s.cbegin(9); it != s.cend(9); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(9) == 9);

    for (auto it = s.cbegin(10); it != s.cend(10); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(10) == 9);

    for (auto it = s.cbegin(11); it != s.cend(11); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(11) == 9);

    for (auto it = s.cbegin(12); it != s.cend(12); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(12) == 10);

    for (auto it = s.cbegin(13); it != s.cend(13); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(13) == 12);

    for (auto it = s.cbegin(14); it != s.cend(14); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(14) == 12);

    for (auto it = s.cbegin(15); it != s.cend(15); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(15) == 13);

    for (auto it = s.cbegin(16); it != s.cend(16); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(16) == 13);

    for (auto it = s.cbegin(17); it != s.cend(17); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    REQUIRE(s.number_of_congruences(17) == 13);
  }

  LIBSEMIGROUPS_TEST_CASE("Sims2",
                          "003",
                          "FullTransformationMonoid(2) 2-sided",
                          "[quick][presentation]") {
    auto                   rg = ReportGuard(false);
    FroidurePin<Transf<3>> S(
        {Transf<3>({1, 2, 0}), Transf<3>({1, 0, 2}), Transf<3>({0, 1, 0})});
    REQUIRE(S.size() == 27);
    REQUIRE(S.is_monoid());
    auto  p = make<Presentation<word_type>>(S);
    Sims2 s(p);
    REQUIRE(s.number_of_congruences(27) == 7);  // Correct and verified with GAP
  }

  LIBSEMIGROUPS_TEST_CASE("Sims2",
                          "010",
                          "PartitionMonoid(2) 2-sided from FroidurePin",
                          "[quick][sims2]") {
    FroidurePin<Bipartition> S({Bipartition::make({{1, -1}, {2, -2}}),
                                Bipartition::make({{1, -2}, {2, -1}}),
                                Bipartition::make({{1}, {2, -2}, {-1}}),
                                Bipartition::make({{1, 2, -1, -2}})});

    REQUIRE(S.size() == 15);
    auto p = make<Presentation<word_type>>(S);
    REQUIRE(std::distance(p.cbegin(), p.cend()) == 32);

    Sims2 s(p);
    REQUIRE(s.number_of_congruences(16)
            == 13);  // Correct and verified with GAP
  }

  LIBSEMIGROUPS_TEST_CASE("Sims2",
                          "012",
                          "TemperleyLieb(4) from presentation",
                          "[quick][sims2]") {
    using digraph_type         = typename Sims2Graph::digraph_type;
    using node_type            = typename digraph_type::node_type;
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p(empty_word::yes);
    p.alphabet(3);
    for (auto const &rel : TemperleyLieb(4)) {
      p.add_rule_and_check(rel.first.cbegin(),
                           rel.first.cend(),
                           rel.second.cbegin(),
                           rel.second.cend());
    }
    Sims2 s(p);
    for (auto it = s.cbegin(14); it != s.cend(14); ++it) {
      check_compatibility(it->left(), s.left_presentation());
      check_compatibility(it->right(), s.right_presentation());
    }
    auto it = s.cbegin(14);
    // FIXME the following does not appear to be correct (just the first
    // example) the others are verified with GAP
    // REQUIRE(
    //     it->left()
    //     == action_digraph_helper::make<node_type>(14, {{0, 1, 0}, {0, 1,
    //     0}}));
    // REQUIRE(it->right() == it->left());

    REQUIRE(it->left()
            == action_digraph_helper::make<node_type>(14, {{0, 0, 0}}));
    REQUIRE(it->right() == it->left());

    ++it;
    REQUIRE(it->left()
            == action_digraph_helper::make<node_type>(14,
                                                      {{1, 2, 3},
                                                       {1, 6, 5},
                                                       {4, 2, 8},
                                                       {5, 7, 3},
                                                       {4, 2, 10},
                                                       {5, 11, 5},
                                                       {1, 6, 12},
                                                       {9, 7, 3},
                                                       {10, 2, 8},
                                                       {9, 7, 5},
                                                       {10, 13, 10},
                                                       {5, 11, 5},
                                                       {5, 6, 12},
                                                       {10, 13, 10}}));
    REQUIRE(it->right()
            == action_digraph_helper::make<node_type>(14,
                                                      {{1, 2, 3},
                                                       {1, 4, 5},
                                                       {6, 2, 7},
                                                       {5, 8, 3},
                                                       {1, 4, 9},
                                                       {5, 10, 5},
                                                       {6, 2, 11},
                                                       {11, 2, 7},
                                                       {12, 8, 3},
                                                       {5, 4, 9},
                                                       {5, 10, 5},
                                                       {11, 13, 11},
                                                       {12, 8, 5},
                                                       {11, 13, 11}}));

    REQUIRE(s.number_of_congruences(14)
            == 9);  // 9 is the correct answer verified with GAP
  }

  LIBSEMIGROUPS_TEST_CASE("Sims2",
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

    Sims2 S(p);
    REQUIRE(S.number_of_congruences(204) == 16);
  }

  //   [ [ [ 0, 0, 0 ] ],
  //     [ [ 0, 0, 0 ] ] ]
  //
  // [ [ [ 1, 1, 1 ], [ 1, 1, 1 ] ],
  //   [ [ 1, 1, 1 ], [ 1, 1, 1 ] ] ]
  //
  // [ [ [ 1, 2, 1 ], [ 1, 1, 1 ], [ 2, 2, 2 ] ],
  //   [ [ 1, 2, 1 ], [ 1, 2, 1 ], [ 1, 2, 1 ] ] ]
  //
  // [ [ [ 1, 2, 1 ], [ 1, 2, 1 ], [ 1, 2, 1 ] ],
  //   [ [ 1, 2, 1 ], [ 1, 1, 1 ], [ 2, 2, 2 ] ] ]
  //
  // [ [ [ 1, 2, 1 ], [ 1, 3, 1 ], [ 4, 2, 4 ], [ 1, 3, 1 ], [ 4, 2, 4 ] ],
  //   [ [ 1, 2, 1 ], [ 1, 4, 1 ], [ 3, 2, 3 ], [ 3, 2, 3 ], [ 1, 4, 1 ] ] ]
  //
  // [ [ [ 1, 2, 3 ], [ 1, 4, 5 ], [ 6, 2, 7 ], [ 5, 8, 3 ], [ 1, 4, 9 ],
  //     [ 5, 5, 5 ], [ 6, 2, 5 ], [ 5, 2, 7 ], [ 10, 8, 3 ], [ 5, 4, 9 ],
  //     [ 10, 8, 5 ] ],
  //   [ [ 1, 2, 3 ], [ 1, 6, 5 ], [ 4, 2, 8 ], [ 5, 7, 3 ], [ 4, 2, 5 ],
  //     [ 5, 5, 5 ], [ 1, 6, 10 ], [ 9, 7, 3 ], [ 5, 2, 8 ], [ 9, 7, 5 ],
  //     [ 5, 6, 10 ] ] ]
  //
  // [ [ [ 1, 2, 3 ], [ 1, 4, 5 ], [ 6, 2, 7 ], [ 5, 8, 3 ], [ 1, 4, 9 ],
  //     [ 5, 5, 5 ], [ 6, 2, 10 ], [ 10, 2, 7 ], [ 11, 8, 3 ], [ 5, 4, 9 ],
  //     [ 10, 10, 10 ], [ 11, 8, 5 ] ],
  //   [ [ 1, 2, 3 ], [ 1, 6, 5 ], [ 4, 2, 8 ], [ 5, 7, 3 ], [ 4, 2, 5 ],
  //     [ 5, 10, 5 ], [ 1, 6, 11 ], [ 9, 7, 3 ], [ 5, 2, 8 ], [ 9, 7, 5 ],
  //     [ 5, 10, 5 ], [ 5, 6, 11 ] ] ]
  //
  // [ [ [ 1, 2, 3 ], [ 1, 4, 5 ], [ 6, 2, 7 ], [ 5, 8, 3 ], [ 1, 4, 9 ],
  //     [ 5, 10, 5 ], [ 6, 2, 5 ], [ 5, 2, 7 ], [ 11, 8, 3 ], [ 5, 4, 9 ],
  //     [ 5, 10, 5 ], [ 11, 8, 5 ] ],
  //   [ [ 1, 2, 3 ], [ 1, 6, 5 ], [ 4, 2, 8 ], [ 5, 7, 3 ], [ 4, 2, 10 ],
  //     [ 5, 5, 5 ], [ 1, 6, 11 ], [ 9, 7, 3 ], [ 10, 2, 8 ], [ 9, 7, 5 ],
  //     [ 10, 10, 10 ], [ 5, 6, 11 ] ] ]
  //
  //
  //
  //
  // [ [ [ 1, 2, 3 ], [ 1, 4, 5 ], [ 6, 2, 7 ], [ 5, 8, 3 ], [ 1, 4, 9 ],
  //     [ 5, 10, 5 ], [ 6, 2, 11 ], [ 11, 2, 7 ], [ 12, 8, 3 ], [ 5, 4, 9 ],
  //     [ 5, 10, 5 ], [ 11, 13, 11 ], [ 12, 8, 5 ], [ 11, 13, 11 ] ],
  //   [ [ 1, 2, 3 ], [ 1, 6, 5 ], [ 4, 2, 8 ], [ 5, 7, 3 ], [ 4, 2, 10 ],
  //     [ 5, 11, 5 ], [ 1, 6, 12 ], [ 9, 7, 3 ], [ 10, 2, 8 ], [ 9, 7, 5 ],
  //     [ 10, 13, 10 ], [ 5, 11, 5 ], [ 5, 6, 12 ], [ 10, 13, 10 ] ] ]

}  // namespace libsemigroups
