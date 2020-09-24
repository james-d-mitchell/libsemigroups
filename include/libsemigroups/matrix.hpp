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

#ifndef LIBSEMIGROUPS_MATRIX_HPP_
#define LIBSEMIGROUPS_MATRIX_HPP_

#include "libsemigroups-debug.hpp"

namespace libsemigroups {

  template <typename Plus,
            typename Prod,
            typename Zero,
            typename One,
            size_t N,
            typename Container>
  class Matrix {
   public:
    using entry_type = typename Container::value_type;

    Matrix() = default;

    explicit Matrix(Container&& c) : _container(std::move(c)) {
      LIBSEMIGROUPS_ASSERT(_container.size() == N * N);
    }

    explicit Matrix(std::initializer_list<std::initializer_list<entry_type>> C)
        : Matrix() {
      // TODO checks
      for (size_t r = 0; r < N; ++r) {
        for (size_t c = 0; c < N; ++c) {
          _container[r * N + c] = *((C.begin() + r)->begin() + c);
        }
      }
    }

    bool operator==(Matrix const& other) const {
      return _container == other._container;
    }

    bool operator!=(Matrix const& other) const {
      return _container != other._container;
    }

    void operator()(size_t r, size_t c, entry_type val) {
      _container[r * N + c] = val;
    }

    void product_inplace(Matrix const& A, Matrix const& B) {
      // get a pointer array for the entire column in B matrix
      static std::array<bool, N> colPtr;
      // loop over output columns first, because column element addresses are
      // not continuous
      for (size_t c = 0; c < N; c++) {
        for (size_t i = 0; i < N; ++i) {
          colPtr[i] = B._container[i * N + c];
        }
        for (size_t r = 0; r < N; r++) {
          _container[r * N + c]
              = std::inner_product(A._container.begin() + r * N,
                                   A._container.begin() + (r + 1) * N,
                                   colPtr.cbegin(),
                                   Zero()(),
                                   Plus(),
                                   Prod());
        }
        /*_container[(N - 1) * N + c]
            = std::inner_product(A._container.begin() + (N - 1) * N,
                                 A._container.end(),
                                 colPtr.begin(),
                                 Zero()(),
                                 Plus(),
                                 Prod());*/
        // move column pointer array to the next column
        /*std::transform(
            colPtr.begin(),
            colPtr.end(),
            colPtr.begin(),
            [](typename Container::const_iterator it) { return ++it; });*/
      }
    }

   private:
    Container _container;
  };  // namespace libsemigroups

  struct BooleanPlus {
    bool operator()(bool const x, bool const y) const {
      return x || y;
    }
  };

  struct BooleanProd {
    bool operator()(bool const x, bool const y) const {
      return x && y;
    }
  };

  struct BooleanOne {
    bool operator()() {
      return true;
    }
  };

  struct BooleanZero {
    bool operator()() {
      return false;
    }
  };

  template <size_t N>
  using BMat = Matrix<BooleanPlus,
                      BooleanProd,
                      BooleanZero,
                      BooleanOne,
                      N,
                      std::array<bool, N * N>>;

  template <size_t N>
  struct PlusMod {
    uint_fast8_t operator()(uint_fast8_t const x, uint_fast8_t const y) const {
      return (x + y) % N;
    }
  };

  template <size_t N>
  struct ProdMod {
    uint_fast8_t operator()(uint_fast8_t const x, uint_fast8_t const y) const {
      return (x * y) % N;
    }
  };

  struct One {
    uint_fast8_t operator()() {
      return 1;
    }
  };

  struct Zero {
    uint_fast8_t operator()() {
      return 0;
    }
  };

  template <size_t N, size_t M>
  using PMat = Matrix<PlusMod<M>,
                      ProdMod<M>,
                      Zero,
                      One,
                      N,
                      std::array<uint_fast8_t, N * N>>;

}  // namespace libsemigroups

#endif  // LIBSEMIGROUPS_MATRIX_HPP_
