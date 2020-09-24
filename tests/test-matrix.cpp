// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2020 James D. Mitchell
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

#include <array>
#include <cstddef>  // for size_t
#include <cstdint>  // for uint64_t

#include "catch.hpp"  // for REQUIRE, REQUIRE_THROWS_AS, REQUIRE_NOTHROW
#include "libsemigroups/containers.hpp"  // for ?
#include "libsemigroups/matrix.hpp"      // for ?
#include "libsemigroups/report.hpp"      // for ?
#include "test-main.hpp"                 // for LIBSEMIGROUPS_TEST_CASE

namespace libsemigroups {
  constexpr bool REPORT = false;

  LIBSEMIGROUPS_TEST_CASE("Matrix", "001", "", "[quick]") {
    auto    rg = ReportGuard(REPORT);
    BMat<2> m({0, 1, 0, 1});
    REQUIRE(m == BMat<2>({0, 1, 0, 1}));
    REQUIRE(!(m == BMat<2>({0, 0, 0, 1})));
    REQUIRE(m == BMat<2>({{0, 1}, {0, 1}}));
    m.product_inplace(BMat<2>({{0, 0}, {0, 0}}), BMat<2>({{0, 0}, {0, 0}}));
    REQUIRE(m == BMat<2>({{0, 0}, {0, 0}}));
    m.product_inplace(BMat<2>({{0, 0}, {0, 0}}), BMat<2>({{1, 1}, {1, 1}}));
    REQUIRE(m == BMat<2>({{0, 0}, {0, 0}}));
    m.product_inplace(BMat<2>({{1, 1}, {1, 1}}), BMat<2>({{0, 0}, {0, 0}}));
    REQUIRE(m == BMat<2>({{0, 0}, {0, 0}}));

    m.product_inplace(BMat<2>({{0, 1}, {1, 0}}), BMat<2>({{1, 0}, {1, 0}}));
    REQUIRE(m == BMat<2>({{1, 0}, {1, 0}}));
  }

  LIBSEMIGROUPS_TEST_CASE("Matrix", "002", "", "[quick]") {
    auto    rg = ReportGuard(REPORT);
    BMat<3> m;
    m.product_inplace(BMat<3>({{1, 1, 0}, {0, 0, 1}, {1, 0, 1}}),
                      BMat<3>({{1, 0, 1}, {0, 0, 1}, {1, 1, 0}}));
    REQUIRE(m == BMat<3>({{1, 0, 1}, {1, 1, 0}, {1, 1, 1}}));
  }

  LIBSEMIGROUPS_TEST_CASE("Matrix", "003", "", "[quick]") {
    auto       rg = ReportGuard(REPORT);
    PMat<3, 3> m;
    m.product_inplace(PMat<3, 3>({{1, 1, 0}, {0, 0, 1}, {1, 0, 1}}),
                      PMat<3, 3>({{1, 0, 1}, {0, 0, 1}, {1, 1, 0}}));
    REQUIRE(m == PMat<3, 3>({{1, 0, 2}, {1, 1, 0}, {2, 1, 1}}));
  }

}  // namespace libsemigroups
