//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019 James D. Mitchell
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

// This file contains the specializations of various adapters for
// derived classes of Element.

#ifndef LIBSEMIGROUPS_ELEMENT_ADAPTERS_HPP_
#define LIBSEMIGROUPS_ELEMENT_ADAPTERS_HPP_

#include <unordered_set>  // for unordered_set

#include "adapters.hpp"             // for Complexity etc
#include "bitset.hpp"               // for BitSet
#include "constants.hpp"            // for UNDEFINED
#include "element.hpp"              // for Element
#include "libsemigroups-debug.hpp"  // for LIBSEMIGROUPS_ASSERT
#include "stl.hpp"                  // for Hash, EqualTo, Less

namespace libsemigroups {
  // Specialization of templates from adapters.hpp for classes derived from
  // the class Element, such as Transformation<size_t> and so on . . .
  //! Specialization of the adapter Complexity for pointers to subclasses of
  //! Element.
  //!
  //! \sa Complexity.
  template <typename TSubclass>
  struct Complexity<TSubclass*,
                    typename std::enable_if<
                        std::is_base_of<Element, TSubclass>::value>::type> {
    //! Returns \p x->complexity().
    inline size_t operator()(TSubclass const* x) const {
      return x->complexity();
    }
  };

  //! Specialization of the adapter Complexity for subclasses of
  //! Element.
  //!
  //! \sa Complexity.
  template <typename TSubclass>
  struct Complexity<TSubclass,
                    typename std::enable_if<
                        std::is_base_of<Element, TSubclass>::value>::type> {
    //! Returns \p x.complexity().
    inline size_t operator()(TSubclass const& x) const {
      return x.complexity();
    }
  };

  //! Specialization of the adapter Degree for pointers to subclasses of
  //! Element.
  //!
  //! \sa Degree.
  template <typename TSubclass>
  struct Degree<TSubclass*,
                typename std::enable_if<
                    std::is_base_of<Element, TSubclass>::value>::type> {
    //! Returns \p x->degree().
    inline size_t operator()(TSubclass const* x) const {
      return x->degree();
    }
  };

  //! Specialization of the adapter Degree for subclasses of
  //! Element.
  //!
  //! \sa Degree.
  template <typename TSubclass>
  struct Degree<TSubclass,
                typename std::enable_if<
                    std::is_base_of<Element, TSubclass>::value>::type> {
    //! Returns \p x.degree().
    inline size_t operator()(TSubclass const& x) const {
      return x.degree();
    }
  };

  //! Specialization of the adapter IncreaseDegree for pointers to subclasses
  //! of Element.
  //!
  //! \sa IncreaseDegree.
  template <typename TSubclass>
  struct IncreaseDegree<TSubclass*,
                        typename std::enable_if<
                            std::is_base_of<Element, TSubclass>::value>::type> {
    //! Returns \p x->increase_degree_by(\p n).
    inline void operator()(TSubclass* x, size_t n) const {
      return x->increase_degree_by(n);
    }
  };

  // FIXME(later) why is there no specialisation for non-pointers for
  // IncreaseDegree?

  //! Specialization of the adapter Less for pointers to subclasses
  //! of Element.
  //!
  //! \sa Less.
  template <typename TSubclass>
  struct Less<TSubclass*,
              typename std::enable_if<
                  std::is_base_of<Element, TSubclass>::value>::type> {
    //! Returns \c true if the object pointed to by \p x is less than the
    //! object pointed to by \p y.
    inline bool operator()(TSubclass const* x, TSubclass const* y) const {
      return *x < *y;
    }
  };

  //! Specialization of the adapter One for pointers to subclasses
  //! of Element.
  //!
  //! \sa One.
  template <typename TSubclass>
  struct One<TSubclass*,
             typename std::enable_if<
                 std::is_base_of<Element, TSubclass>::value>::type> {
    //! Returns a pointer to a new instance of the one of \p x.
    TSubclass* operator()(Element const* x) const {
      // return new TSubclass(std::move(x->identity<TSubclass>()));
      return static_cast<TSubclass*>(x->heap_identity());
    }

    //! Returns a pointer to a new instance of the one of \p x.
    TSubclass* operator()(size_t n) {
      return new TSubclass(std::move(TSubclass::one(n)));
    }
  };

  //! Specialization of the adapter One for subclasses of Element.
  //!
  //! \sa One.
  template <typename TSubclass>
  struct One<TSubclass,
             typename std::enable_if<
                 std::is_base_of<Element, TSubclass>::value>::type> {
    //! Returns a new instance of the one of \p x.
    TSubclass operator()(TSubclass const& x) const {
      return static_cast<TSubclass>(x.identity());
    }

    //! Returns a new instance of the one of \p x.
    TSubclass operator()(size_t n) {
      return TSubclass(std::move(TSubclass::identity(n)));
    }
  };

  //! Specialization of the adapter Product for pointers to subclasses of
  //! Element.
  //!
  //! \sa Product.
  template <typename TSubclass>
  struct Product<TSubclass*,
                 typename std::enable_if<
                     std::is_base_of<Element, TSubclass>::value>::type> {
    //! Changes \p xy in-place to hold the product of \p x and \p y using
    //! Element::redefine.
    void operator()(TSubclass*       xy,
                    TSubclass const* x,
                    TSubclass const* y,
                    size_t           tid = 0) {
      xy->redefine(*x, *y, tid);
    }
  };

  //! Specialization of the adapter Product for subclasses of Element.
  //!
  //! \sa Product.
  template <typename TSubclass>
  struct Product<TSubclass,
                 typename std::enable_if<
                     std::is_base_of<Element, TSubclass>::value>::type> {
    //! Changes \p xy in-place to hold the product of \p x and \p y using
    //! Element::redefine.
    void operator()(TSubclass&       xy,
                    TSubclass const& x,
                    TSubclass const& y,
                    size_t           tid = 0) {
      xy.redefine(x, y, tid);
    }
  };

  //! Specialization of the adapter Swap for subclasses of Element.
  //!
  //! \sa Swap.
  template <typename TSubclass>
  struct Swap<TSubclass*,
              typename std::enable_if<
                  std::is_base_of<Element, TSubclass>::value>::type> {
    //! Swaps the object pointed to by \p x with the one pointed to by \p y.
    void operator()(TSubclass* x, TSubclass* y) const {
      x->swap(*y);
    }
  };

  //! Specialization of the adapter ImageRightAction for pointers to
  //! Permutation instances.
  //!
  //! \sa ImageRightAction.
  template <typename TValueType>
  struct ImageRightAction<
      Permutation<TValueType>*,
      TValueType,
      typename std::enable_if<std::is_integral<TValueType>::value>::type> {
    //! Returns the image of \p pt under \p x.
    TValueType operator()(Permutation<TValueType> const* x,
                          TValueType const               pt) {
      return (*x)[pt];
    }
  };

  //! Specialization of the adapter Inverse for pointers to
  //! Permutation instances.
  //!
  //! \sa Inverse.
  template <typename TValueType>
  struct Inverse<Permutation<TValueType>*> {
    //! Returns a pointer to a new instance of the inverse of \p x.
    Permutation<TValueType>* operator()(Permutation<TValueType>* x) {
      return new Permutation<TValueType>(std::move(x->inverse()));
    }
  };

  //! Specialization of the adapter Inverse for Permutation instances.
  //!
  //! \sa Inverse.
  template <typename TValueType>
  struct Inverse<Permutation<TValueType>> {
    //! Returns the inverse of \p x.
    Permutation<TValueType> operator()(Permutation<TValueType> const& x) {
      return x.inverse();
    }
  };

  //! Specialization of the adapter Hash for subclasses of Element.
  //!
  //! \sa Hash.
  template <typename TSubclass>
  struct Hash<TSubclass,
              typename std::enable_if<
                  std::is_base_of<Element, TSubclass>::value>::type> {
    //! Returns \p x.hash_value()
    size_t operator()(TSubclass const& x) const {
      return x.hash_value();
    }
  };

  //! Specialization of the adapter Hash for pointers to subclasses of Element.
  //!
  //! \sa Hash.
  template <typename TSubclass>
  struct Hash<TSubclass*,
              typename std::enable_if<
                  std::is_base_of<Element, TSubclass>::value>::type> {
    //! Returns \p x->hash_value()
    size_t operator()(TSubclass const* x) const {
      return x->hash_value();
    }
  };

  //! Specialization of the adapter ImageRightAction for instance of
  //! PartialPerm.
  // Slowest
  template <typename TIntType>
  struct ImageRightAction<PartialPerm<TIntType>, PartialPerm<TIntType>> {
    //! Stores the idempotent \f$(xy) ^ {-1}xy\f$ in \p res.
    void operator()(PartialPerm<TIntType>&       res,
                    PartialPerm<TIntType> const& pt,
                    PartialPerm<TIntType> const& x) const noexcept {
      res.redefine(pt, x);
      res.swap(res.right_one());
    }
  };

  // Faster than the above, but slower than the below
  template <typename S, typename T>
  struct ImageRightAction<PartialPerm<S>, T> {
    void operator()(T& res, T const& pt, PartialPerm<S> const& x) const {
      res.clear();
      for (auto i : pt) {
        if (x[i] != UNDEFINED) {
          res.push_back(x[i]);
        }
      }
      std::sort(res.begin(), res.end());
    }
  };

  // Fastest, but limited to at most degree 64
  template <typename TIntType, size_t N>
  struct ImageRightAction<PartialPerm<TIntType>, BitSet<N>> {
    void operator()(BitSet<N>&                   res,
                    BitSet<N> const&             pt,
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

  //! Specialization of the adapter ImageLeftAction for instances of
  //! PartialPerm.
  //!
  //! \sa ImageLeftAction.
  // Slowest
  template <typename TIntType>
  struct ImageLeftAction<PartialPerm<TIntType>, PartialPerm<TIntType>> {
    //! Stores the idempotent \f$xy(xy) ^ {-1}\f$ in \p res.
    void operator()(PartialPerm<TIntType>&       res,
                    PartialPerm<TIntType> const& pt,
                    PartialPerm<TIntType> const& x) const noexcept {
      res.redefine(x, pt);
      res.swap(res.left_one());
    }
  };

  // Faster than the above, but slower than the below
  // works for T = std::vector and T = BitSet<N>
  template <typename S, typename T>
  struct ImageLeftAction<PartialPerm<S>, T> {
    void operator()(T& res, T const& pt, PartialPerm<S> const& x) const {
      static PartialPerm<S> xx;
      x.inverse(xx);
      ImageRightAction<PartialPerm<S>, T>()(res, pt, xx);
    }
  };

  // Fastest, but limited to at most degree 64
  // template <typename TIntType, size_t N>
  // struct ImageLeftAction<PartialPerm<TIntType>, BitSet<N>> {
  //   void operator()(BitSet<N>&                   res,
  //                   BitSet<N> const&             pt,
  //                   PartialPerm<TIntType> const& x) const {
  //     res.reset();
  //     // Apply the lambda to every set bit in pt
  //     // for (TIntType i = 0; i < x.degree(); ++i) {
  //     //  if (x[i] != UNDEFINED && pt[x[i]]) {
  //     //    res.set(i);
  //     //  }
  //     // }
  //     // The approach below seems to be marginally faster than the one above,
  //     // but both are slower than ImageRightAction (slightly less than 2
  //     times) static PartialPerm<TIntType> xx; x.inverse(xx);
  //     ImageRightAction<PartialPerm<S>, T>()(
  //         res, pt, xx);
  // };

  //! Specialization of the adapter EqualTo for pointers to subclasses of
  //! Element.
  //!
  //! \sa EqualTo.
  template <typename TSubclass>
  struct EqualTo<
      TSubclass*,
      typename std::enable_if<
          std::is_base_of<libsemigroups::Element, TSubclass>::value>::type> {
    //! Tests equality of two const Element pointers via equality of the
    //! Elements they point to.
    bool operator()(TSubclass const* x, TSubclass const* y) const {
      return *x == *y;
    }
  };

  //! Specialization of the adapter ImageRightAction for instances of
  //! Permutation.
  //!
  //! \sa ImageRightAction.
  template <typename TIntType>
  struct ImageRightAction<
      Permutation<TIntType>,
      TIntType,
      typename std::enable_if<std::is_integral<TIntType>::value>::type> {
    //! Stores the image of \p pt under the action of \p p in \p res.
    void operator()(TIntType&                    res,
                    TIntType const&              pt,
                    Permutation<TIntType> const& p) const noexcept {
      LIBSEMIGROUPS_ASSERT(pt < p.degree());
      res = p[pt];
    }

    //! Returns the image of \p pt under the action of \p p.
    TIntType operator()(TIntType const pt, Permutation<TIntType> const& x) {
      return x[pt];
    }
  };

  // TODO use the final template parameter
  // TODO remove code duplication, Lambda = ImageRightAction(res, x,
  // identity_transformation);
  template <typename TIntType>
  struct Lambda<Transformation<TIntType>> {
    using result_type = std::vector<TIntType>;
    void operator()(std::vector<TIntType>&          res,
                    Transformation<TIntType> const& x) const noexcept {
      res.clear();
      res.resize(x.degree());
      for (size_t i = 0; i < res.size(); ++i) {
        res[i] = x[i];
      }
      std::sort(res.begin(), res.end());
      res.erase(std::unique(res.begin(), res.end()), res.end());
    }
    std::vector<TIntType> operator()(Transformation<TIntType> const& x) const {
      std::vector<TIntType> res;
      this->                operator()(res, x);
      return res;
    }
  };

  // TODO use the final template parameter
  // TODO remove code duplication, Rho = ImageLeftAction(res, x,
  // identity_transformation);
  template <typename TIntType>
  struct Rho<Transformation<TIntType>> {
    using result_type = std::vector<TIntType>;
    void operator()(std::vector<TIntType>&          res,
                    Transformation<TIntType> const& x) const noexcept {
      res.clear();
      res.resize(x.degree());
      std::vector<TIntType> buf(x.degree(), TIntType(UNDEFINED));
      TIntType              next = 0;

      for (size_t i = 0; i < res.size(); ++i) {
        if (buf[x[i]] == UNDEFINED) {
          buf[x[i]] = next++;
        }
        res[i] = buf[x[i]];
      }
    }
    std::vector<TIntType> operator()(Transformation<TIntType> const& x) const {
      std::vector<TIntType> res;
      this->                operator()(res, x);
      return res;
    }
  };

  // OnSets
  template <typename TIntType>
  struct ImageRightAction<Transformation<TIntType>, std::vector<TIntType>> {
    void operator()(std::vector<TIntType>&          res,
                    std::vector<TIntType> const&    pt,
                    Transformation<TIntType> const& x) const {
      res.clear();
      for (auto i : pt) {
        res.push_back(x[i]);
      }
      std::sort(res.begin(), res.end());
      res.erase(std::unique(res.begin(), res.end()), res.end());
    }
    std::vector<TIntType> operator()(std::vector<TIntType> const&    pt,
                                     Transformation<TIntType> const& x) const {
      std::vector<TIntType> res;
      this->                operator()(res, pt, x);
      return res;
    }
  };

  // OnKernelAntiAction
  template <typename TIntType>
  struct ImageLeftAction<Transformation<TIntType>, std::vector<TIntType>> {
    void operator()(std::vector<TIntType>&          res,
                    std::vector<TIntType> const&    pt,
                    Transformation<TIntType> const& x) const {
      res.clear();
      res.resize(x.degree());
      std::vector<TIntType> buf(x.degree(), TIntType(UNDEFINED));
      TIntType              next = 0;

      for (size_t i = 0; i < res.size(); ++i) {
        if (buf[pt[x[i]]] == UNDEFINED) {
          buf[pt[x[i]]] = next++;
        }
        res[i] = buf[pt[x[i]]];
      }
    }

    std::vector<TIntType> operator()(std::vector<TIntType> const&    pt,
                                     Transformation<TIntType> const& x) const {
      std::vector<TIntType> res;
      this->                operator()(res, pt, x);
      return res;
    }
  };

  template <typename TIntType>
  struct Rank<Transformation<TIntType>> {
    size_t operator()(Transformation<TIntType> const& x) {
      return x.crank();
    }
  };

  // TODO this involves lots of copying
  template <>
  struct Lambda<BooleanMat> {
    using result_type = std::vector<std::vector<bool>>;
    void operator()(std::vector<std::vector<bool>>& res,
                    BooleanMat const&               x) const noexcept {
      res = x.row_space_basis();
    }
    std::vector<std::vector<bool>> operator()(BooleanMat const& x) const {
      std::vector<std::vector<bool>> res;
      this->                         operator()(res, x);
      return res;
    }
  };

  // TODO fix this too
  template <>
  struct Rho<BooleanMat> {
    using result_type = std::vector<std::vector<bool>>;
    void operator()(std::vector<std::vector<bool>>& res,
                    BooleanMat const&               x) const noexcept {
      res = x.transpose().row_space_basis();
    }
    std::vector<std::vector<bool>> operator()(BooleanMat const& x) const {
      std::vector<std::vector<bool>> res;
      this->                         operator()(res, x);
      return res;
    }
  };

  // TODO: remove noexcepts from all of these
  template <>
  struct ImageRightAction<BooleanMat, std::vector<std::vector<bool>>> {
    void operator()(std::vector<std::vector<bool>>&       res,
                    std::vector<std::vector<bool>> const& pt,
                    BooleanMat const&                     x) const noexcept {
      std::vector<std::vector<bool>> out;
      for (auto it = pt.cbegin(); it < pt.cend(); ++it) {
        std::vector<bool> cup(x.degree(), false);
        for (size_t i = 0; i < x.degree(); ++i) {
          if ((*it)[i]) {
            for (size_t j = 0; j < x.degree(); ++j) {
              cup[j] = cup[j] || x[i * x.degree() + j];
            }
          }
        }
        out.push_back(cup);
      }
      res = boolmat_helpers::rows_basis(out);
    }
    std::vector<std::vector<bool>>
    operator()(std::vector<std::vector<bool>> const& pt,
               BooleanMat const&                     x) const {
      std::vector<std::vector<bool>> res;
      this->                         operator()(res, pt, x);
      return res;
    }
  };

  template <>
  struct ImageLeftAction<BooleanMat, std::vector<std::vector<bool>>> {
    void operator()(std::vector<std::vector<bool>>&       res,
                    std::vector<std::vector<bool>> const& pt,
                    BooleanMat const&                     x) const noexcept {
      BooleanMat transpose = x.transpose();
      ImageRightAction<BooleanMat, std::vector<std::vector<bool>>>()(
          res, pt, transpose);
    }
    std::vector<std::vector<bool>>
    operator()(std::vector<std::vector<bool>> const& pt,
               BooleanMat const&                     x) const {
      std::vector<std::vector<bool>> res;
      this->                         operator()(res, pt, x);
      return res;
    }
  };

  template <>
  struct Rank<BooleanMat> {
    size_t operator()(BooleanMat const& x) {
      return x.row_space_size();
    }
  };
}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_ELEMENT_ADAPTERS_HPP_
