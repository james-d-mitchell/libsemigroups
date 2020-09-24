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

#include "libsemigroups/element.hpp"   // for BooleanMat
#include "libsemigroups/matrix.hpp"    // for BMat
#include "libsemigroups/semiring.hpp"  // for Semiring

#include "../tests/test-konieczny-booleanmat-data.hpp"

namespace libsemigroups {

  int myproduct(int x, int* y) {
    return x & *y;
  }

  int mysum(int x, int y) {
    return x | y;
  }

  void mymatmult(std::vector<int>& res,
                 std::vector<int>& A,
                 std::vector<int>& B) {
    size_t m = 40;
    // init res with right size
    // res.resize(m * m);
    // get a pointer array for the entire column in B matrix
    static std::vector<int*> colPtr;
    colPtr.clear();
    for (size_t i = 0; i < m; i++) {
      colPtr.push_back(&B[i * m]);
    }
    // loop over output columns first, because column element addresses are not
    // continuous
    for (size_t c = 0; c < m; c++) {
      for (size_t r = 0; r < m - 1; r++) {
        res[r * m + c] = std::inner_product(A.begin() + r * m,
                                            A.begin() + (r + 1) * m,
                                            colPtr.begin(),
                                            0,
                                            mysum,
                                            myproduct);
      }
      res[(m - 1) * m + c] = std::inner_product(A.begin() + (m - 1) * m,
                                                A.end(),
                                                colPtr.begin(),
                                                0,
                                                mysum,
                                                myproduct);
      // move column pointer array to the next column
      std::transform(colPtr.begin(), colPtr.end(), colPtr.begin(), [](int* x) {
        return ++x;
      });
    }
  }

  std::vector<int> booleanmat_to_vec(BooleanMat const& x) {
    std::vector<int> vec;
    for (size_t i = 0; i < x.degree() * x.degree(); ++i) {
      vec.push_back(x[i]);
    }
    return vec;
  }

  template <size_t N>
  BMat<N> booleanmat_to_bmat(BooleanMat const& x) {
    BMat<N> xx;
    for (size_t r = 0; r < x.degree(); ++r) {
      for (size_t c = 0; c < x.degree(); ++c) {
        xx(r, c, x.at(r * N + c));
      }
    }
    return xx;
  }

  TEST_CASE("BooleanMat1", "[quick][000]") {
    BENCHMARK("redefine") {
      BooleanMat result1(size_t(40));
      BooleanMat result2 = konieczny_data::clark_gens.back();
      REQUIRE(konieczny_data::clark_gens.size() == 6);
      for (size_t i = 0; i < 500; ++i) {
        for (auto const& y : konieczny_data::clark_gens) {
          result1.redefine(result2, y);
          std::swap(result1, result2);
        }
      }
    };
  }

  TEST_CASE("BooleanMat2", "[quick][001]") {
    std::vector<int>              result1(40 * 40, false);
    std::vector<std::vector<int>> clark;
    for (auto const& x : konieczny_data::clark_gens) {
      clark.push_back(booleanmat_to_vec(x));
    }
    std::vector<int> result2 = clark.back();
    REQUIRE(clark.size() == 6);
    REQUIRE(result2.size() == 1600);

    BENCHMARK("inner product") {
      for (size_t i = 0; i < 500; ++i) {
        for (auto& y : clark) {
          mymatmult(result1, result2, y);
          std::swap(result1, result2);
        }
      }
    };
  }

  TEST_CASE("BooleanMat3", "[quick][002]") {
    BMat<40>              result1;
    std::vector<BMat<40>> clark;
    for (auto const& x : konieczny_data::clark_gens) {
      clark.push_back(booleanmat_to_bmat<40>(x));
    }
    auto result2 = clark.back();
    REQUIRE(clark.size() == 6);

    BENCHMARK("inner product") {
      for (size_t i = 0; i < 500; ++i) {
        for (auto& y : clark) {
          result1.product_inplace(result2, y);
          std::swap(result1, result2);
        }
      }
    };
  }
}  // namespace libsemigroups
