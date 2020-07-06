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

#include "libsemigroups/action.hpp"          // for LeftAction
#include "libsemigroups/bitset.hpp"          // for BitSet
#include "libsemigroups/element-helper.hpp"  // for PartialPerm
#include "libsemigroups/element.hpp"         // for Lambda
#include "libsemigroups/report.hpp"          // for ReportGuard

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

  namespace old {

    template <typename TElementType, typename TPointType, typename = void>
    struct ImageRightAction;

    template <typename TIntType>
    struct ImageRightAction<PartialPerm<TIntType>, PartialPerm<TIntType>> {
      void operator()(PartialPerm<TIntType>&       res,
                      PartialPerm<TIntType> const& pt,
                      PartialPerm<TIntType> const& x) const noexcept {
        res.redefine(pt, x);
        res.swap(res.right_one());
      }
    };
  }  // namespace old

  template <typename TIntType>
  struct ImageRightAction<PartialPerm<TIntType>, std::vector<TIntType>> {
    void operator()(std::vector<TIntType>&       res,
                    std::vector<TIntType> const& pt,
                    PartialPerm<TIntType> const& x) const {
      res.clear();
      for (auto i : pt) {
        if (x[i] != UNDEFINED) {
          res.push_back(x[i]);
        }
      }
      std::sort(res.begin(), res.end());
    }
  };

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

  template <typename TIntType, size_t N>
  struct ImageRightAction<PartialPerm<TIntType>, BitSet<N>> {
    void operator()(BitSet<N>&               res,
                    BitSet<N> const&         pt,
                    PartialPerm<TIntType> const& x) const {
      res.reset();
      // Apply the lambda to every set bit in pt
      pt.apply([&x, &res](size_t i) {
        if (x[i] != UNDEFINED) {
          res.set(x[i]);
        }
      });
    }
  };

  TEST_CASE("PartialPerm 0", "[quick][001]") {
    auto rg     = ReportGuard(false);
    using PPerm = PPermHelper<17>::type;
    BENCHMARK("ImageRightAction original") {
      RightAction<PPerm, PPerm, old::ImageRightAction<PPerm, PPerm>> o;
      o.add_seed(One<PPerm>()(17));
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
      REQUIRE(o.size() == 131072);
    };
  }

  TEST_CASE("PartialPerm 1", "[quick][002]") {
    auto rg     = ReportGuard(false);
    using PPerm = PPermHelper<17>::type;
    BENCHMARK("ImageRightAction = OnSets") {
      using int_type = uint_fast8_t;
      RightAction<PPerm,
                  std::vector<int_type>,
                  ImageRightAction<PPerm, std::vector<int_type>>>
          o;
      o.add_seed({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16});
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
      REQUIRE(o.size() == 131072);
    };
  }

  TEST_CASE("PartialPerm 2", "[quick][003]") {
    auto rg     = ReportGuard(false);
    using PPerm = PPermHelper<17>::type;
    BENCHMARK("ImageRightAction = OnIntegers") {
      RightAction<PPerm, uint_fast32_t, ImageRightAction<PPerm, uint_fast32_t>>
          o;
      o.add_seed(static_cast<uint_fast32_t>(-1));
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
      // FIXME the following is off by 1
      REQUIRE(o.size() == 131073);
    };
  }

  TEST_CASE("PartialPerm 3", "[quick][004]") {
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
      REQUIRE(std::all_of(
          o.cbegin(), o.cend(), [](BitSet<17> i) { return i.count() == 17; }));
      REQUIRE(o.size() == 131072);
    };
  }
  /*using Lambda = ::libsemigroups::Lambda<element_type>;
  using Rho    = ::libsemigroups::Rho<element_type>;

  using lambda_value_type =
      typename ::libsemigroups::Lambda<element_type>::result_type;
  using rho_value_type =
      typename ::libsemigroups::Rho<element_type>::result_type;

  using LambdaAction = ImageRightAction<element_type, lambda_value_type>;
  using RhoAction    = ImageLeftAction<element_type, rho_value_type>;*/
}  // namespace libsemigroups
