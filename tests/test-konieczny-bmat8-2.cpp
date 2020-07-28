// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2020 Finn Smith
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

#include <cstddef>  // for size_t

#include "catch.hpp"      // for REQUIRE
#include "test-main.hpp"  // FOR LIBSEMIGROUPS_TEST_CASE

#include "libsemigroups/bmat8.hpp"      // for BMat8
#include "libsemigroups/konieczny.hpp"  // for Konieczny

namespace libsemigroups {

  constexpr bool REPORT = false;

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "009",
                          "full bmat monoid 5",
                          "[extreme][bmat8]") {
    auto                     rg         = ReportGuard(REPORT);
    const std::vector<BMat8> bmat5_gens = {BMat8({{1, 0, 0, 0, 0},
                                                  {0, 1, 0, 0, 0},
                                                  {0, 0, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {0, 0, 0, 0, 1}}),
                                           BMat8({{0, 1, 0, 0, 0},
                                                  {0, 0, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {0, 0, 0, 0, 1},
                                                  {1, 0, 0, 0, 0}}),
                                           BMat8({{0, 1, 0, 0, 0},
                                                  {1, 0, 0, 0, 0},
                                                  {0, 0, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {0, 0, 0, 0, 1}}),
                                           BMat8({{1, 0, 0, 0, 0},
                                                  {0, 1, 0, 0, 0},
                                                  {0, 0, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {1, 0, 0, 0, 1}}),
                                           BMat8({{1, 1, 0, 0, 0},
                                                  {1, 0, 1, 0, 0},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 0, 1, 1, 0},
                                                  {0, 0, 0, 0, 1}}),
                                           BMat8({{1, 1, 0, 0, 0},
                                                  {1, 0, 1, 0, 0},
                                                  {0, 1, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {0, 0, 0, 0, 1}}),
                                           BMat8({{1, 1, 1, 0, 0},
                                                  {1, 0, 0, 1, 0},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 0, 1, 1, 0},
                                                  {0, 0, 0, 0, 1}}),
                                           BMat8({{1, 1, 0, 0, 0},
                                                  {1, 0, 1, 0, 0},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 0, 1, 0, 1},
                                                  {0, 0, 0, 1, 1}}),
                                           BMat8({{1, 1, 1, 1, 0},
                                                  {1, 0, 0, 0, 1},
                                                  {0, 1, 0, 0, 1},
                                                  {0, 0, 1, 0, 1},
                                                  {0, 0, 0, 1, 1}}),
                                           BMat8({{1, 0, 0, 0, 0},
                                                  {0, 1, 0, 0, 0},
                                                  {0, 0, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {0, 0, 0, 0, 0}}),
                                           BMat8({{1, 1, 1, 0, 0},
                                                  {1, 0, 0, 1, 0},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 0, 1, 0, 1},
                                                  {0, 0, 0, 1, 1}}),
                                           BMat8({{1, 1, 1, 0, 0},
                                                  {1, 0, 0, 1, 0},
                                                  {1, 0, 0, 0, 1},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 0, 1, 0, 1}}),
                                           BMat8({{1, 1, 1, 0, 0},
                                                  {1, 0, 0, 1, 1},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 1, 0, 0, 1},
                                                  {0, 0, 1, 1, 0}}),
                                           BMat8({{1, 1, 1, 0, 0},
                                                  {1, 1, 0, 1, 0},
                                                  {1, 0, 0, 0, 1},
                                                  {0, 1, 0, 0, 1},
                                                  {0, 0, 1, 1, 1}})};

    Konieczny<BMat8> T(bmat5_gens);
    REQUIRE(T.size() == 33554432);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "010",
                          "regular generated bmat monoid 4 idempotents",
                          "[quick][no-valgrind][bmat8]") {
    auto                     rg = ReportGuard(REPORT);
    const std::vector<BMat8> reg_bmat4_gens
        = {BMat8({{0, 1, 0, 0}, {1, 0, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}, {1, 0, 0, 0}}),
           BMat8({{1, 0, 0, 0}, {1, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{0, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}})};

    Konieczny<BMat8> S(reg_bmat4_gens);
    REQUIRE(S.size() == 63904);

    size_t reg_elts = 0;
    for (auto it = S.cbegin_regular_D_classes();
         it < S.cend_regular_D_classes();
         ++it) {
      reg_elts += (*it)->size();
    }
    REQUIRE(reg_elts == 40408);

    size_t idems = 0;
    for (auto it = S.cbegin_regular_D_classes();
         it < S.cend_regular_D_classes();
         ++it) {
      idems += (*it)->nr_idempotents();
    }
    REQUIRE(idems == 2360);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "011",
                          "regular generated bmat monoid 5",
                          "[extreme][bmat8]") {
    auto                     rg             = ReportGuard(REPORT);
    const std::vector<BMat8> reg_bmat5_gens = {BMat8({{0, 1, 0, 0, 0},
                                                      {1, 0, 0, 0, 0},
                                                      {0, 0, 1, 0, 0},
                                                      {0, 0, 0, 1, 0},
                                                      {0, 0, 0, 0, 1}}),
                                               BMat8({{0, 1, 0, 0, 0},
                                                      {0, 0, 1, 0, 0},
                                                      {0, 0, 0, 1, 0},
                                                      {0, 0, 0, 0, 1},
                                                      {1, 0, 0, 0, 0}}),
                                               BMat8({{1, 0, 0, 0, 0},
                                                      {1, 1, 0, 0, 0},
                                                      {0, 0, 1, 0, 0},
                                                      {0, 0, 0, 1, 0},
                                                      {0, 0, 0, 0, 1}}),
                                               BMat8({{0, 0, 0, 0, 0},
                                                      {0, 1, 0, 0, 0},
                                                      {0, 0, 1, 0, 0},
                                                      {0, 0, 0, 1, 0},
                                                      {0, 0, 0, 0, 1}})};

    Konieczny<BMat8> T(reg_bmat5_gens);
    REQUIRE(T.size() == 32311832);

    size_t reg_elts = 0;
    for (auto it = T.cbegin_regular_D_classes();
         it < T.cend_regular_D_classes();
         ++it) {
      reg_elts += (*it)->size();
    }
    REQUIRE(reg_elts == 8683982);

    size_t idems = 0;
    for (auto it = T.cbegin_regular_D_classes();
         it < T.cend_regular_D_classes();
         ++it) {
      idems += (*it)->nr_idempotents();
    }
    REQUIRE(idems == 73023);
  }
  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "012",
                          "my favourite example",
                          "[quick][finite][no-valgrind][bmat8]") {
    auto                     rg   = ReportGuard(REPORT);
    const std::vector<BMat8> gens = {BMat8({{0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0}}),
                                     BMat8({{0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1}}),
                                     BMat8({{0, 0, 0, 1, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 0, 0, 0, 1, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1}})};

    Konieczny<BMat8> S(gens);
    REQUIRE(S.size() == 597369);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "013",
                          "another large example",
                          "[quick][no-valgrind][bmat8]") {
    auto                     rg   = ReportGuard(REPORT);
    const std::vector<BMat8> gens = {BMat8({{0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1}}),
                                     BMat8({{0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1}}),
                                     BMat8({{0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1}}),
                                     BMat8({{1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 0, 0, 0, 1, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0}}),
                                     BMat8({{0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0}})};

    Konieczny<BMat8> S(gens);
    REQUIRE(S.size() == 201750);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "014",
                          "my favourite example transposed",
                          "[quick][no-valgrind][bmat8]") {
    auto                     rg   = ReportGuard(REPORT);
    const std::vector<BMat8> gens = {BMat8({{0, 0, 0, 0, 1, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 1, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1}}),
                                     BMat8({{0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 1, 0},
                                            {1, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 1},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 1, 0, 0, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {1, 0, 1, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 1, 0, 0, 1},
                                            {0, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 1, 1, 0, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 1, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 1, 0, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0}}),
                                     BMat8({{0, 1, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 1, 1, 1, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 1},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {1, 0, 0, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0}}),
                                     BMat8({{0, 0, 0, 1, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 1, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 1, 0, 0, 1, 0, 0},
                                            {0, 0, 0, 0, 0, 0, 0, 0},
                                            {0, 0, 0, 0, 1, 0, 0, 0},
                                            {1, 1, 0, 0, 0, 0, 0, 1}})};

    Konieczny<BMat8> S(gens);
    REQUIRE(S.size() == 597369);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "024",
                          "full bmat monoid 5 with stop in Action",
                          "[extreme][bmat8]") {
    auto                     rg         = ReportGuard(REPORT);
    const std::vector<BMat8> bmat5_gens = {BMat8({{1, 0, 0, 0, 0},
                                                  {0, 1, 0, 0, 0},
                                                  {0, 0, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {0, 0, 0, 0, 1}}),
                                           BMat8({{0, 1, 0, 0, 0},
                                                  {0, 0, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {0, 0, 0, 0, 1},
                                                  {1, 0, 0, 0, 0}}),
                                           BMat8({{0, 1, 0, 0, 0},
                                                  {1, 0, 0, 0, 0},
                                                  {0, 0, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {0, 0, 0, 0, 1}}),
                                           BMat8({{1, 0, 0, 0, 0},
                                                  {0, 1, 0, 0, 0},
                                                  {0, 0, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {1, 0, 0, 0, 1}}),
                                           BMat8({{1, 1, 0, 0, 0},
                                                  {1, 0, 1, 0, 0},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 0, 1, 1, 0},
                                                  {0, 0, 0, 0, 1}}),
                                           BMat8({{1, 1, 0, 0, 0},
                                                  {1, 0, 1, 0, 0},
                                                  {0, 1, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {0, 0, 0, 0, 1}}),
                                           BMat8({{1, 1, 1, 0, 0},
                                                  {1, 0, 0, 1, 0},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 0, 1, 1, 0},
                                                  {0, 0, 0, 0, 1}}),
                                           BMat8({{1, 1, 0, 0, 0},
                                                  {1, 0, 1, 0, 0},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 0, 1, 0, 1},
                                                  {0, 0, 0, 1, 1}}),
                                           BMat8({{1, 1, 1, 1, 0},
                                                  {1, 0, 0, 0, 1},
                                                  {0, 1, 0, 0, 1},
                                                  {0, 0, 1, 0, 1},
                                                  {0, 0, 0, 1, 1}}),
                                           BMat8({{1, 0, 0, 0, 0},
                                                  {0, 1, 0, 0, 0},
                                                  {0, 0, 1, 0, 0},
                                                  {0, 0, 0, 1, 0},
                                                  {0, 0, 0, 0, 0}}),
                                           BMat8({{1, 1, 1, 0, 0},
                                                  {1, 0, 0, 1, 0},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 0, 1, 0, 1},
                                                  {0, 0, 0, 1, 1}}),
                                           BMat8({{1, 1, 1, 0, 0},
                                                  {1, 0, 0, 1, 0},
                                                  {1, 0, 0, 0, 1},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 0, 1, 0, 1}}),
                                           BMat8({{1, 1, 1, 0, 0},
                                                  {1, 0, 0, 1, 1},
                                                  {0, 1, 0, 1, 0},
                                                  {0, 1, 0, 0, 1},
                                                  {0, 0, 1, 1, 0}}),
                                           BMat8({{1, 1, 1, 0, 0},
                                                  {1, 1, 0, 1, 0},
                                                  {1, 0, 0, 0, 1},
                                                  {0, 1, 0, 0, 1},
                                                  {0, 0, 1, 1, 1}})};

    Konieczny<BMat8> T(bmat5_gens);
    T.run_for(std::chrono::milliseconds(100));
    T.run_for(std::chrono::milliseconds(100));
    T.run_for(std::chrono::milliseconds(100));
    T.run_for(std::chrono::milliseconds(100));
    T.run_for(std::chrono::milliseconds(100));
    T.run();
    T.run_for(std::chrono::milliseconds(100));
    T.run_for(std::chrono::milliseconds(100));
    REQUIRE(T.size() == 33554432);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "021",
                          "regular generated bmat monoid 5 with stops",
                          "[extreme][bmat8]") {
    auto                     rg             = ReportGuard(REPORT);
    const std::vector<BMat8> reg_bmat5_gens = {BMat8({{0, 1, 0, 0, 0},
                                                      {1, 0, 0, 0, 0},
                                                      {0, 0, 1, 0, 0},
                                                      {0, 0, 0, 1, 0},
                                                      {0, 0, 0, 0, 1}}),
                                               BMat8({{0, 1, 0, 0, 0},
                                                      {0, 0, 1, 0, 0},
                                                      {0, 0, 0, 1, 0},
                                                      {0, 0, 0, 0, 1},
                                                      {1, 0, 0, 0, 0}}),
                                               BMat8({{1, 0, 0, 0, 0},
                                                      {1, 1, 0, 0, 0},
                                                      {0, 0, 1, 0, 0},
                                                      {0, 0, 0, 1, 0},
                                                      {0, 0, 0, 0, 1}}),
                                               BMat8({{0, 0, 0, 0, 0},
                                                      {0, 1, 0, 0, 0},
                                                      {0, 0, 1, 0, 0},
                                                      {0, 0, 0, 1, 0},
                                                      {0, 0, 0, 0, 1}})};

    Konieczny<BMat8> T(reg_bmat5_gens);
    T.run_for(std::chrono::milliseconds(4000));
    size_t nr_classes = T.cend_D_classes() - T.cbegin_D_classes();
    REQUIRE(nr_classes > 0);
    T.run_for(std::chrono::milliseconds(2000));
    REQUIRE(T.cend_D_classes() - T.cbegin_D_classes() > nr_classes);

    REQUIRE(T.size() == 32311832);

    size_t reg_elts = 0;
    for (auto it = T.cbegin_regular_D_classes();
         it < T.cend_regular_D_classes();
         ++it) {
      reg_elts += (*it)->size();
    }
    REQUIRE(reg_elts == 8683982);

    size_t idems = 0;
    for (auto it = T.cbegin_regular_D_classes();
         it < T.cend_regular_D_classes();
         ++it) {
      idems += (*it)->nr_idempotents();
    }
    REQUIRE(idems == 73023);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny", "026", "exceptions", "[quick][bmat8]") {
    auto                     rg    = ReportGuard(REPORT);
    const std::vector<BMat8> gens  = {BMat8({{0, 1, 0}, {0, 0, 1}, {1, 0, 0}}),
                                     BMat8({{0, 1, 0}, {1, 0, 0}, {0, 0, 1}}),
                                     BMat8({{1, 0, 0}, {1, 1, 0}, {0, 0, 1}}),
                                     BMat8({{1, 1, 0}, {0, 1, 1}, {1, 0, 1}})};
    const std::vector<BMat8> idems = {BMat8({{1, 0, 0}, {0, 1, 0}, {0, 0, 1}}),
                                      BMat8({{1, 0, 0}, {1, 1, 0}, {0, 0, 1}}),
                                      BMat8({{1, 0, 0}, {1, 1, 1}, {0, 0, 1}}),
                                      BMat8({{1, 0, 0}, {1, 1, 0}, {1, 0, 1}}),
                                      BMat8({{1, 0, 0}, {1, 1, 0}, {1, 1, 1}}),
                                      BMat8({{1, 1, 0}, {1, 1, 0}, {0, 0, 1}}),
                                      BMat8({{1, 0, 0}, {1, 1, 1}, {1, 1, 1}}),
                                      BMat8({{1, 1, 0}, {1, 1, 0}, {1, 1, 1}}),
                                      BMat8({{1, 1, 1}, {1, 1, 1}, {1, 1, 1}})};
    const std::vector<BMat8> non_reg_reps
        = {BMat8({{0, 0, 1}, {1, 0, 1}, {1, 1, 0}}),
           BMat8({{0, 0, 1}, {1, 1, 1}, {1, 1, 0}}),
           BMat8({{0, 1, 1}, {1, 0, 1}, {1, 1, 1}}),
           BMat8({{0, 1, 1}, {1, 1, 0}, {1, 0, 1}}),
           BMat8({{1, 0, 1}, {1, 0, 1}, {1, 1, 0}}),
           BMat8({{1, 1, 0}, {1, 1, 1}, {1, 1, 1}})};

    REQUIRE_THROWS_AS(Konieczny<BMat8>({}), LibsemigroupsException);

    Konieczny<BMat8> KS(gens);
    KS.run();

    REQUIRE(KS.cend_regular_D_classes() - KS.cbegin_regular_D_classes()
            == idems.size());

    for (BMat8 id : idems) {
      REQUIRE_THROWS_AS(Konieczny<BMat8>::NonRegularDClass(&KS, id),
                        LibsemigroupsException);
    }

    for (BMat8 x : non_reg_reps) {
      REQUIRE_THROWS_AS(Konieczny<BMat8>::RegularDClass(&KS, x),
                        LibsemigroupsException);
    }
  }
}  // namespace libsemigroups
