//
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
//

#include "bench-main.hpp"  // for LIBSEMIGROUPS_BENCHMARK
#include "catch.hpp"       // for REQUIRE, REQUIRE_NOTHROW, REQUIRE_THROWS_AS

#include "libsemigroups/action.hpp"            // for LeftAction
#include "libsemigroups/bitset.hpp"            // for BitSet
#include "libsemigroups/element-adapters.hpp"  // for Lambda
#include "libsemigroups/element-helper.hpp"    // for PPermHelper
#include "libsemigroups/element.hpp"           // for PartialPerm
#include "libsemigroups/report.hpp"            // for ReportGuard

#define FOR_SET_BITS(__bit_int, __nr_bits, __variable) \
  uint_fast32_t block = __bit_int;                     \
  while (block != 0) {                                 \
    uint_fast32_t t          = block & -block;         \
    int           __variable = __builtin_ctzll(block); \
    if (__variable >= __nr_bits) {                     \
      break;                                           \
    }

#define END_FOR_SET_BITS \
  block ^= t;            \
  }

static constexpr uint_fast32_t MASK[32]
    = {0x1,        0x2,       0x4,       0x8,       0x10,       0x20,
       0x40,       0x80,      0x100,     0x200,     0x400,      0x800,
       0x1000,     0x2000,    0x4000,    0x8000,    0x10000,    0x20000,
       0x40000,    0x80000,   0x100000,  0x200000,  0x400000,   0x800000,
       0x1000000,  0x2000000, 0x4000000, 0x8000000, 0x10000000, 0x20000000,
       0x40000000, 0x80000000};

namespace libsemigroups {
  // Basic version of a function using BitSet in element.hpp, retained for the
  // purposes of comparison.
  template <typename TIntType>
  struct ImageRightAction<PartialPerm<TIntType>, uint_fast32_t> {
    void operator()(uint_fast32_t&               res,
                    uint_fast32_t const&         pt,
                    PartialPerm<TIntType> const& x) const {
      res = 0;
      FOR_SET_BITS(pt, static_cast<int>(x.degree()), i) {
        if (x[i] != UNDEFINED) {
          res |= MASK[x[i]];
        }
      }
      END_FOR_SET_BITS
    }
  };

  template <typename T>
  void benchmark_example1(T& o) {
    using PPerm = PPermHelper<17>::type;
    o.add_generator(
        PPerm({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
              {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0},
              17));
    o.add_generator(
        PPerm({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
              {1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
              17));
    o.add_generator(
        PPerm({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
              {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
              17));
    o.add_generator(
        PPerm({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
              {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
              17));
  }

  template <typename T>
  void benchmark_example1_inverse(T& o) {
    using PPerm = PPermHelper<17>::type;
    o.add_generator(
        PPerm({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
              {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0},
              17));
    o.add_generator(
        PPerm({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
              {1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
              17));
    o.add_generator(
        PPerm({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
              {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
              17)
            .inverse());
    o.add_generator(
        PPerm({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
              {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
              17)
            .inverse());
  }

  TEST_CASE("Slowest PartialPerm", "[quick][001]") {
    auto rg     = ReportGuard(false);
    using PPerm = PPermHelper<17>::type;
    BENCHMARK("ImageRightAction = PartialPerm") {
      RightAction<PPerm, PPerm, ImageRightAction<PPerm, PPerm>> o;
      o.add_seed(One<PPerm>()(17));
      benchmark_example1(o);
      REQUIRE(o.size() == 131072);
    };

    BENCHMARK("ImageLeftAction = PartialPerm") {
      LeftAction<PPerm, PPerm, ImageLeftAction<PPerm, PPerm>> o;
      o.add_seed(One<PPerm>()(17));
      benchmark_example1(o);
      REQUIRE(o.size() == 131072);
    };
  }

  TEST_CASE("Second slowest PartialPerm", "[quick][002]") {
    auto rg        = ReportGuard(false);
    using PPerm    = PPermHelper<17>::type;
    using int_type = uint_fast8_t;
    BENCHMARK("ImageRightAction = vector") {
      RightAction<PPerm,
                  std::vector<int_type>,
                  ImageRightAction<PPerm, std::vector<int_type>>>
          o;
      o.add_seed({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16});
      benchmark_example1(o);
      REQUIRE(o.size() == 131072);
    };
    BENCHMARK("ImageLeftAction = vector") {
      LeftAction<PPerm,
                 std::vector<int_type>,
                 ImageLeftAction<PPerm, std::vector<int_type>>>
          o;
      o.add_seed({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16});
      benchmark_example1(o);
      REQUIRE(o.size() == 131072);
    };
  }

  TEST_CASE("Second fastest PartialPerm", "[quick][005]") {
    auto rg        = ReportGuard(false);
    using PPerm    = PPermHelper<17>::type;
    using int_type = uint_fast8_t;
    BENCHMARK("ImageRightAction = array/StaticVector1") {
      RightAction<PPerm,
                  detail::StaticVector1<int_type, 17>,
                  ImageRightAction<PPerm, detail::StaticVector1<int_type, 17>>>
          o;
      o.add_seed({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16});
      benchmark_example1(o);
      REQUIRE(o.size() == 131072);
    };
    BENCHMARK("ImageLeftAction = array/StaticVector1") {
      LeftAction<PPerm,
                 detail::StaticVector1<int_type, 17>,
                 ImageLeftAction<PPerm, detail::StaticVector1<int_type, 17>>>
          o;
      o.add_seed({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16});
      benchmark_example1(o);
      REQUIRE(o.size() == 131072);
    };
  }

  TEST_CASE("fastest PartialPerm", "[quick][004]") {
    auto rg     = ReportGuard(false);
    using PPerm = PPermHelper<17>::type;
    BENCHMARK("ImageRightAction = BitSets") {
      RightAction<PPerm, BitSet<17>, ImageRightAction<PPerm, BitSet<17>>> o;

      BitSet<17> sd;
      sd.set();
      // sd.set(0, 17, true);

      // sd.reset();
      // for (size_t i = 0; i < 17; ++i) {
      //  REQUIRE(sd.count() == i);
      //  sd.set(i);
      // }

      REQUIRE(sd.size() == 17);
      REQUIRE(sd.count() == 17);
      o.add_seed(sd);
      benchmark_example1(o);
      // REQUIRE(std::all_of(
      //    o.cbegin(), o.cend(), [](BitSet<17> i) { return i.count() == 17;
      //    }));
      REQUIRE(o.size() == 131072);
    };

    BENCHMARK("ImageLeftAction (via inverses) = BitSets") {
      RightAction<PPerm, BitSet<17>, ImageRightAction<PPerm, BitSet<17>>> o;

      BitSet<17> sd;
      sd.set();

      REQUIRE(sd.size() == 17);
      REQUIRE(sd.count() == 17);
      o.add_seed(sd);
      benchmark_example1_inverse(o);
      REQUIRE(o.size() == 131072);
    };

    BENCHMARK("ImageLeftAction = BitSets") {
      LeftAction<PPerm, BitSet<17>, ImageLeftAction<PPerm, BitSet<17>>> o;

      BitSet<17> sd;
      sd.set();
      REQUIRE(sd.size() == 17);
      REQUIRE(sd.count() == 17);
      o.add_seed(sd);
      benchmark_example1(o);
      // REQUIRE(std::all_of(
      //    o.cbegin(), o.cend(), [](BitSet<17> const& bs) { return bs.count()
      //    == 17; }));

      REQUIRE(o.size() == 131072);
    };
  }

  TEST_CASE("fastest PartialPerm comparison", "[quick][003]") {
    auto rg     = ReportGuard(false);
    using PPerm = PPermHelper<17>::type;
    BENCHMARK("ImageRightAction = naked bitset") {
      RightAction<PPerm, uint_fast32_t, ImageRightAction<PPerm, uint_fast32_t>>
          o;
      o.add_seed(static_cast<uint_fast32_t>(-1));
      benchmark_example1(o);
      REQUIRE(o.size() == 131073);
      // The above is off-by-one because the seed corresponds to a set of size
      // 32
    };
  }
}  // namespace libsemigroups
