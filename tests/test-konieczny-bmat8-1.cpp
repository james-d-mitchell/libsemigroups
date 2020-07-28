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

#include "libsemigroups/bmat8.hpp"         // for BMat8
#include "libsemigroups/froidure-pin.hpp"  // for FroidurePin
#include "libsemigroups/konieczny.hpp"     // for Konieczny

namespace libsemigroups {

  constexpr bool REPORT = false;

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "000",
                          "regular elements and idempotents",
                          "[quick][no-valgrind][bmat8]") {
    auto                     rg = ReportGuard(REPORT);
    const std::vector<BMat8> gens
        = {BMat8({{0, 1, 0, 0}, {1, 0, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}, {1, 0, 0, 0}}),
           BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {1, 0, 0, 1}}),
           BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 0}})};
    Konieczny<BMat8>   KS(gens);
    FroidurePin<BMat8> S(gens);
    S.run();

    REQUIRE(KS.size() == 63904);
    REQUIRE(S.size() == 63904);

    size_t count = 0;
    for (auto it = S.cbegin(); it < S.cend(); ++it) {
      if (KS.is_regular_element(*it)) {
        count++;
      }
    }
    REQUIRE(count == 40408);

    size_t sum = 0;
    for (auto it = KS.cbegin_regular_D_classes();
         it < KS.cend_regular_D_classes();
         ++it) {
      sum += (*it)->size();
    }
    REQUIRE(sum == 40408);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "001",
                          "regular D class 01",
                          "[quick][bmat8]") {
    auto                     rg   = ReportGuard(REPORT);
    const std::vector<BMat8> gens = {BMat8({{0, 1, 0}, {0, 0, 1}, {1, 0, 0}}),
                                     BMat8({{0, 1, 0}, {1, 0, 0}, {0, 0, 1}}),
                                     BMat8({{1, 0, 0}, {1, 1, 0}, {0, 0, 1}}),
                                     BMat8({{1, 1, 0}, {0, 1, 1}, {1, 0, 1}})};
    Konieczny<BMat8>         KS(gens);
    REQUIRE(KS.size() == 247);

    BMat8                           x({{1, 0, 0}, {1, 1, 0}, {1, 0, 1}});
    Konieczny<BMat8>::RegularDClass D = Konieczny<BMat8>::RegularDClass(&KS, x);
    REQUIRE(D.nr_L_classes() == 3);
    REQUIRE(D.nr_R_classes() == 3);
    REQUIRE(D.size() == 18);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "002",
                          "regular D class 02",
                          "[quick][bmat8]") {
    auto                     rg = ReportGuard(REPORT);
    const std::vector<BMat8> gens
        = {BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{0, 1, 0, 0}, {1, 0, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}, {1, 0, 0, 0}}),
           BMat8({{0, 1, 0, 1}, {1, 0, 1, 0}, {1, 0, 1, 0}, {0, 0, 1, 1}}),
           BMat8({{0, 1, 0, 1}, {1, 0, 1, 0}, {1, 0, 1, 0}, {0, 1, 0, 1}}),
           BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 0}})};

    Konieczny<BMat8> KS(gens);
    KS.run();
    BMat8 idem(BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}));
    Konieczny<BMat8>::RegularDClass D
        = Konieczny<BMat8>::RegularDClass(&KS, idem);
    REQUIRE(D.size() == 24);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "004",
                          "regular D class 04: contains",
                          "[quick][no-valgrind][bmat8]") {
    auto                     rg = ReportGuard(REPORT);
    const std::vector<BMat8> gens
        = {BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{0, 1, 0, 0}, {1, 0, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}, {1, 0, 0, 0}}),
           BMat8({{0, 1, 0, 1}, {1, 0, 1, 0}, {1, 0, 1, 0}, {0, 0, 1, 1}}),
           BMat8({{0, 1, 0, 1}, {1, 0, 1, 0}, {1, 0, 1, 0}, {0, 1, 0, 1}}),
           BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 0}})};

    Konieczny<BMat8>   KS(gens);
    FroidurePin<BMat8> S(gens);
    KS.run();
    S.run();
    BMat8 idem(BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}));
    Konieczny<BMat8>::RegularDClass D
        = Konieczny<BMat8>::RegularDClass(&KS, idem);

    // test that the top D class contains only permutation matrices
    for (auto it = S.cbegin(); it < S.cend(); it++) {
      REQUIRE(D.contains(*it) == (((*it) * (*it).transpose()) == gens[0]));
    }
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "005",
                          "non-regular D classes 01",
                          "[quick][bmat8]") {
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

    Konieczny<BMat8> KS(gens);
    KS.run();

    REQUIRE(KS.cend_regular_D_classes() - KS.cbegin_regular_D_classes()
            == idems.size());

    size_t count = 0;
    for (BMat8 id : idems) {
      Konieczny<BMat8>::RegularDClass D(&KS, id);
      count += D.size();
    }

    REQUIRE(count == 142);

    std::vector<BMat8> non_reg_reps
        = {BMat8({{0, 0, 1}, {1, 0, 1}, {1, 1, 0}}),
           BMat8({{0, 0, 1}, {1, 1, 1}, {1, 1, 0}}),
           BMat8({{0, 1, 1}, {1, 0, 1}, {1, 1, 1}}),
           BMat8({{0, 1, 1}, {1, 1, 0}, {1, 0, 1}}),
           BMat8({{1, 0, 1}, {1, 0, 1}, {1, 1, 0}}),
           BMat8({{1, 1, 0}, {1, 1, 1}, {1, 1, 1}})};

    {
      Konieczny<BMat8>::NonRegularDClass X(&KS, non_reg_reps[0]);
      REQUIRE(X.size() == 36);
      REQUIRE(X.size_H_class() == 1);
      REQUIRE(X.nr_L_classes() == 6);
      REQUIRE(X.nr_R_classes() == 6);
    }

    {
      Konieczny<BMat8>::NonRegularDClass X(&KS, non_reg_reps[1]);
      REQUIRE(X.size() == 18);
      REQUIRE(X.size_H_class() == 1);
      REQUIRE(X.nr_L_classes() == 3);
      REQUIRE(X.nr_R_classes() == 6);
    }

    {
      Konieczny<BMat8>::NonRegularDClass X(&KS, non_reg_reps[2]);
      REQUIRE(X.size() == 18);
      REQUIRE(X.size_H_class() == 2);
      REQUIRE(X.nr_L_classes() == 3);
      REQUIRE(X.nr_R_classes() == 3);
    }

    {
      Konieczny<BMat8>::NonRegularDClass X(&KS, non_reg_reps[3]);
      REQUIRE(X.size() == 6);
      REQUIRE(X.size_H_class() == 6);
      REQUIRE(X.nr_L_classes() == 1);
      REQUIRE(X.nr_R_classes() == 1);
    }

    {
      Konieczny<BMat8>::NonRegularDClass X(&KS, non_reg_reps[4]);
      REQUIRE(X.size() == 18);
      REQUIRE(X.size_H_class() == 1);
      REQUIRE(X.nr_L_classes() == 6);
      REQUIRE(X.nr_R_classes() == 3);
    }

    {
      Konieczny<BMat8>::NonRegularDClass X(&KS, non_reg_reps[5]);
      REQUIRE(X.size() == 9);
      REQUIRE(X.size_H_class() == 1);
      REQUIRE(X.nr_L_classes() == 3);
      REQUIRE(X.nr_R_classes() == 3);
    }

    for (BMat8 x : non_reg_reps) {
      Konieczny<BMat8>::NonRegularDClass N(&KS, x);
      count += N.size();
    }

    REQUIRE(count == 247);

    REQUIRE(KS.size() == 247);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "007",
                          "RegularDClass",
                          "[quick][bmat8]") {
    auto                     rg = ReportGuard(REPORT);
    const std::vector<BMat8> gens
        = {BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{0, 1, 0, 0}, {1, 0, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{0, 1, 0, 1}, {1, 0, 1, 0}, {1, 0, 1, 0}, {0, 0, 1, 1}}),
           BMat8({{0, 1, 0, 1}, {1, 0, 1, 0}, {1, 0, 1, 0}, {0, 1, 0, 1}}),
           BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, 0}})};

    Konieczny<BMat8> KS(gens);
    KS.run();
    BMat8 x = BMat8({{0, 1, 0}, {1, 0, 0}, {0, 0, 0}});
    Konieczny<BMat8>::RegularDClass D = Konieczny<BMat8>::RegularDClass(&KS, x);
    REQUIRE(D.size() == 90);
    REQUIRE(D.nr_L_classes() == 5);
    REQUIRE(D.nr_R_classes() == 9);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "008",
                          "full bmat monoid 4",
                          "[quick][no-valgrind][bmat8]") {
    auto                     rg = ReportGuard(REPORT);
    const std::vector<BMat8> bmat4_gens
        = {BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{1, 1, 1, 0}, {1, 0, 0, 1}, {0, 1, 0, 1}, {0, 0, 1, 1}}),
           BMat8({{1, 1, 0, 0}, {1, 0, 1, 0}, {0, 1, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{1, 1, 0, 0}, {1, 0, 1, 0}, {0, 1, 0, 1}, {0, 0, 1, 1}}),
           BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {1, 0, 0, 1}}),
           BMat8({{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 0}}),
           BMat8({{0, 1, 0, 0}, {1, 0, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),
           BMat8({{0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}, {1, 0, 0, 0}})};

    Konieczny<BMat8> S(bmat4_gens);
    REQUIRE(S.size() == 65536);
  }
}  // namespace libsemigroups
