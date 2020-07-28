
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

#include "libsemigroups/element-adapters.hpp"  // for Degree etc
#include "libsemigroups/element.hpp"           // for Transformation
#include "libsemigroups/konieczny.hpp"         // for Konieczny

namespace libsemigroups {

  constexpr bool REPORT = false;

  LIBSEMIGROUPS_TEST_CASE("Konieczny", "015", "transformations", "[quick]") {
    auto                              rg = ReportGuard(REPORT);
    Konieczny<Transformation<size_t>> S(
        {Transformation<size_t>({1, 0, 2, 3, 4}),
         Transformation<size_t>({1, 2, 3, 4, 0}),
         Transformation<size_t>({0, 0, 2, 3, 4})});
    S.run();
    REQUIRE(S.size() == 3125);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "016",
                          "transformations - JDM favourite example",
                          "[quick][no-valgrind]") {
    auto                                    rg = ReportGuard(REPORT);
    Konieczny<Transformation<uint_fast8_t>> S(
        {Transformation<uint_fast8_t>({1, 7, 2, 6, 0, 4, 1, 5}),
         Transformation<uint_fast8_t>({2, 4, 6, 1, 4, 5, 2, 7}),
         Transformation<uint_fast8_t>({3, 0, 7, 2, 4, 6, 2, 4}),
         Transformation<uint_fast8_t>({3, 2, 3, 4, 5, 3, 0, 1}),
         Transformation<uint_fast8_t>({4, 3, 7, 7, 4, 5, 0, 4}),
         Transformation<uint_fast8_t>({5, 6, 3, 0, 3, 0, 5, 1}),
         Transformation<uint_fast8_t>({6, 0, 1, 1, 1, 6, 3, 4}),
         Transformation<uint_fast8_t>({7, 7, 4, 0, 6, 4, 1, 7})});
    REQUIRE(S.size() == 597369);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "019",
                          "transformations - large example",
                          "[standard][no-valgrind]") {
    auto                                    rg = ReportGuard(REPORT);
    Konieczny<Transformation<uint_fast8_t>> S(
        {Transformation<uint_fast8_t>({2, 1, 0, 4, 2, 1, 1, 8, 0}),
         Transformation<uint_fast8_t>({1, 7, 6, 2, 5, 1, 1, 4, 3}),
         Transformation<uint_fast8_t>({1, 0, 7, 2, 1, 3, 1, 3, 7}),
         Transformation<uint_fast8_t>({0, 3, 8, 1, 2, 8, 1, 7, 0}),
         Transformation<uint_fast8_t>({0, 0, 0, 2, 7, 7, 5, 5, 3})});
    REQUIRE(S.size() == 232511);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "020",
                          "transformations - large example with stop",
                          "[standard][no-valgrind]") {
    auto                                    rg = ReportGuard(REPORT);
    Konieczny<Transformation<uint_fast8_t>> S(
        {Transformation<uint_fast8_t>({2, 1, 0, 4, 2, 1, 1, 8, 0}),
         Transformation<uint_fast8_t>({1, 7, 6, 2, 5, 1, 1, 4, 3}),
         Transformation<uint_fast8_t>({1, 0, 7, 2, 1, 3, 1, 3, 7}),
         Transformation<uint_fast8_t>({0, 3, 8, 1, 2, 8, 1, 7, 0}),
         Transformation<uint_fast8_t>({0, 0, 0, 2, 7, 7, 5, 5, 3})});
    S.run_for(std::chrono::milliseconds(100));
    REQUIRE(S.size() == 232511);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "022",
                          "transformations - large example with run_until",
                          "[standard][no-valgrind]") {
    auto                                    rg = ReportGuard(REPORT);
    Konieczny<Transformation<uint_fast8_t>> S(
        {Transformation<uint_fast8_t>({2, 1, 0, 4, 2, 1, 1, 8, 0}),
         Transformation<uint_fast8_t>({1, 7, 6, 2, 5, 1, 1, 4, 3}),
         Transformation<uint_fast8_t>({1, 0, 7, 2, 1, 3, 1, 3, 7}),
         Transformation<uint_fast8_t>({0, 3, 8, 1, 2, 8, 1, 7, 0}),
         Transformation<uint_fast8_t>({0, 0, 0, 2, 7, 7, 5, 5, 3})});
    S.run_until([&S]() -> bool {
      return S.cend_D_classes() - S.cbegin_D_classes() > 20;
    });

    size_t nr_classes1 = S.cend_D_classes() - S.cbegin_D_classes();
    REQUIRE(nr_classes1 >= 20);
    S.run();
    size_t nr_classes2 = S.cend_D_classes() - S.cbegin_D_classes();
    REQUIRE(S.size() == 232511);
    REQUIRE(nr_classes1 < nr_classes2);
    REQUIRE(nr_classes2 == 2122);
  }

  LIBSEMIGROUPS_TEST_CASE("Konieczny",
                          "023",
                          "transformations - large example with stop in Action",
                          "[standard][no-valgrind]") {
    auto                                    rg = ReportGuard(REPORT);
    Konieczny<Transformation<uint_fast8_t>> S(
        {Transformation<uint_fast8_t>({2, 1, 0, 4, 2, 1, 1, 8, 0}),
         Transformation<uint_fast8_t>({1, 7, 6, 2, 5, 1, 1, 4, 3}),
         Transformation<uint_fast8_t>({1, 0, 7, 2, 1, 3, 1, 3, 7}),
         Transformation<uint_fast8_t>({0, 3, 8, 1, 2, 8, 1, 7, 0}),
         Transformation<uint_fast8_t>({0, 0, 0, 2, 7, 7, 5, 5, 3})});
    S.run_for(std::chrono::milliseconds(5));
    S.run_for(std::chrono::milliseconds(5));
    S.run_for(std::chrono::milliseconds(5));
    S.run_for(std::chrono::milliseconds(100));
    S.run_for(std::chrono::milliseconds(100));
    S.run();
    S.run_for(std::chrono::milliseconds(100));
    S.run_for(std::chrono::milliseconds(100));
    REQUIRE(S.size() == 232511);
  }
}  // namespace libsemigroups
