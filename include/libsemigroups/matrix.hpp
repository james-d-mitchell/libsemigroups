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

#include <algorithm> // for min

#include "libsemigroups-debug.hpp"
#include "constants.hpp"
#include "string.hpp"

namespace libsemigroups {

  template <typename Plus,
            typename Prod,
            typename Zero,
            typename One,
            size_t N,
            typename Container>
  class Matrix {
    // TODO: rows_type alias
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

    typename Container::const_iterator operator[](size_t r) {
      return _container.cbegin() + (r * N);
    }

    //! Returns \c true if \c this is less than \p that.
    bool operator<(Matrix const& that) const {
      return this->_container < that._container;
    }

    //! Insertion operator
    // TODO formatting
    friend std::ostringstream& operator<<(std::ostringstream& os,
                                          Matrix const&       x) {
      os << x._container;
      return os;
    }

    //! Insertion operator
    friend std::ostream& operator<<(std::ostream& os, Matrix const& x) {
      os << detail::to_string(x);
      return os;
    }

    void product_inplace(Matrix const& A, Matrix const& B) {
      // get a pointer array for the entire column in B matrix
      static std::array<entry_type, N> colPtr;
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

    Matrix operator*(Matrix const& y) const {
      Matrix xy;
      xy.product_inplace(*this, y);
      return xy;
    }

    std::vector<std::array<entry_type, N>> rows() const {
      std::vector<std::array<entry_type, N>> out(N);
      for (size_t i = 0; i < N; ++i) {
        for (size_t j = 0; j < N; ++j) {
          out[i][j] = _container[i * N + j];
        }
      }
      return out;
    }
    
    size_t degree() const {
      return N;
    }

    static Matrix identity() {
      Container x;
      x.fill(Zero()());
      for (size_t i = 0; i < N; ++i) {
        x[i * N + i] = One()();
      }
      return Matrix(std::move(x));
    }

    // TODO this should perhaps take the semiring into account
    size_t complexity() const {
      return N * N * N;
    }

    // TODO cache and shouldn't be std::hash
    size_t hash_value() const {
      return std::hash<Container>()(_container);
    }

    Matrix transpose() const {
      Container x;
      x.fill(Zero()());
      for (size_t i = 0; i < N; ++i) {
        for (size_t j = 0; j < N; ++j) {
          x[i * N + j] = _container[j * N + i];
        }
      }
      return Matrix(std::move(x));
    }

    void
    right_product(std::vector<std::array<entry_type, N>>&       res,
                  std::vector<std::array<entry_type, N>> const& rows) const {
      // TODO assertions
      // TODO duplication
      res.resize(rows.size());
      static std::array<entry_type, N> colPtr;
      for (size_t c = 0; c < N; c++) {
        for (size_t i = 0; i < N; ++i) {
          colPtr[i] = _container[i * N + c];
        }
        for (size_t r = 0; r < rows.size(); r++) {
          res[r][c] = std::inner_product(rows[r].begin(),
                                         rows[r].begin() + N,
                                         colPtr.cbegin(),
                                         Zero()(),
                                         Plus(),
                                         Prod());
        }
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

  struct IntegerOne {
    uint_fast8_t operator()() {
      return 1;
    }
  };

  struct IntegerZero {
    uint_fast8_t operator()() {
      return 0;
    }
  };

  template <size_t N, size_t M>
  using PMat = Matrix<PlusMod<M>,
                      ProdMod<M>,
                      IntegerZero,
                      IntegerOne,
                      N,
                      std::array<uint_fast8_t, N * N>>;

  struct MaxPlusPlus {
    int64_t operator()(int64_t const x, int64_t const y) const {
      if (x == NEGATIVE_INFINITY) {
        return y;
      } else if (y == NEGATIVE_INFINITY) {
        return x;
      }
      return std::max(x, y);
    }
  };

  template <size_t N>
  struct MaxPlusProd {
    int64_t operator()(int64_t const x, int64_t const y) const {
      if (x == NEGATIVE_INFINITY || y == NEGATIVE_INFINITY) {
        return NEGATIVE_INFINITY;
      }
      return std::min(x + y, static_cast<int64_t>(N));
    }
  };

  struct MaxPlusOne {
    int64_t operator()() {
      return 0;
    }
  };

  struct MaxPlusZero {
    int64_t operator()() {
      return NEGATIVE_INFINITY;
    }
  };

  template <size_t dim, size_t thresh>
  using TropicalMaxPlusMat = Matrix<MaxPlusPlus,
                      MaxPlusProd<thresh>,
                      MaxPlusZero,
                      MaxPlusOne,
                      dim,
                      std::array<int64_t, dim * dim>>;

  namespace matrix_helpers {
    template <typename Plus, typename Container>
    struct RowAddition {
      void operator()(Container& x, Container const& y) const {
        LIBSEMIGROUPS_ASSERT(x.size() == y.size());
        for (size_t i = 0; i < x.size(); ++i) {
          x[i] = Plus()(x[i], y[i]);
        }
      }

      void operator()(Container&       res,
                      Container const& x,
                      Container const& y) const {
        LIBSEMIGROUPS_ASSERT(res.size() == x.size());
        LIBSEMIGROUPS_ASSERT(x.size() == y.size());
        for (size_t i = 0; i < x.size(); ++i) {
          res[i] = Plus()(x[i], y[i]);
        }
      }
    };

    template <typename Prod, typename Container>
    Container scalar_row_product(Container row, typename Container::value_type scalar) {
      //TODO static assert
      Container out(row);
      for (size_t i = 0; i < out.size(); ++i) {
        out[i] = Prod()(out[i], scalar);
      }
      return out;
    }

    template <size_t dim, size_t thresh>
    void
    tropical_max_plus_row_basis(std::vector<std::array<int64_t, dim>>& rows) {
      //! Modifies \p res to contain the row space basis of \p x.
      // TODO assertions, proper types
      static thread_local std::vector<std::array<int64_t, dim>> buf;
      buf.clear();
      std::sort(rows.begin(), rows.end());
      for (size_t row = 0; row < rows.size(); ++row) {
        // TODO fix this def
        std::array<int64_t, dim> sum;
        sum.fill(NEGATIVE_INFINITY);
        if (row == 0 || rows[row] != rows[row - 1]) {
          for (size_t row2 = 0; row2 < row; ++row2) {
            int64_t max_scalar = thresh;
            for (size_t col = 0; col < dim; ++col) {
              if (rows[row2][col] == NEGATIVE_INFINITY) {
                continue;
              }
              if (rows[row][col] >= rows[row2][col]) {
                if (rows[row][col] != thresh) {
                  max_scalar
                      = std::min(max_scalar, rows[row][col] - rows[row2][col]);
                }
              } else {
                max_scalar = NEGATIVE_INFINITY;
                break;
              }
            }
            if (max_scalar != NEGATIVE_INFINITY) {
              auto scalar_prod = scalar_row_product<MaxPlusProd<thresh>,
                                                    std::array<int64_t, dim>>(
                  rows[row2], max_scalar);
              RowAddition<MaxPlusPlus, std::array<int64_t, dim>>()(sum,
                                                                   scalar_prod);
            }
          }
          if (sum != rows[row]) {
            buf.push_back(rows[row]);
          }
        }
      }
      std::swap(buf, rows);
    }
  }

}  // namespace libsemigroups

#endif  // LIBSEMIGROUPS_MATRIX_HPP_
