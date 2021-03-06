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

// This file contains the specializations of various adapters for
// derived classes of Element.

#ifndef LIBSEMIGROUPS_ELEMENT_ADAPTERS_HPP_
#define LIBSEMIGROUPS_ELEMENT_ADAPTERS_HPP_

#include "adapters.hpp"                 // for Complexity etc
#include "bitset.hpp"                   // for BitSet
#include "constants.hpp"                // for UNDEFINED
#include "element.hpp"                  // for Element
#include "libsemigroups-debug.hpp"      // for LIBSEMIGROUPS_ASSERT
#include "libsemigroups-exception.hpp"  // for LIBSEMIGROUPS_EXCEPTION
#include "stl.hpp"                      // for Hash, EqualTo, Less

namespace libsemigroups {
  ////////////////////////////////////////////////////////////////////////
  // Complexity specializations
  ////////////////////////////////////////////////////////////////////////

  // Specialization of templates from adapters.hpp for classes derived from
  // the class Element, such as Transformation<size_t> and so on . . .
  //! Specialization of the adapter Complexity for pointers to subclasses of
  //! Element.
  //!
  //! \sa Complexity.
  template <typename TSubclass>
  struct Complexity<
      TSubclass*,
      std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
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
  struct Complexity<
      TSubclass,
      std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
    //! Returns \p x.complexity().
    inline size_t operator()(TSubclass const& x) const {
      return x.complexity();
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Degree specializations
  ////////////////////////////////////////////////////////////////////////

  //! Specialization of the adapter Degree for pointers to subclasses of
  //! Element.
  //!
  //! \sa Degree.
  template <typename TSubclass>
  struct Degree<TSubclass*,
                std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
    //! Returns \p x->degree().
    inline size_t operator()(TSubclass const* x) const {
      return x->degree();
    }
  };

  //! Specialization of the adapter Degree for subclasses of Element.
  //!
  //! \sa Degree.
  template <typename TSubclass>
  struct Degree<
      TSubclass,
      std::enable_if_t<std::is_base_of<Element, TSubclass>::value, void>> {
    //! Returns \p x.degree().
    inline size_t operator()(TSubclass const& x) const {
      return x.degree();
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // IncreaseDegree specializations
  ////////////////////////////////////////////////////////////////////////

  //! Specialization of the adapter IncreaseDegree for pointers to subclasses
  //! of Element.
  //!
  //! \sa IncreaseDegree.
  template <typename TSubclass>
  struct IncreaseDegree<
      TSubclass*,
      std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
    //! Returns \p x->increase_degree_by(\p n).
    inline void operator()(TSubclass* x, size_t n) const {
      return x->increase_degree_by(n);
    }
  };

  // TODO(later) why is there no specialisation for non-pointers for
  // IncreaseDegree?

  ////////////////////////////////////////////////////////////////////////
  // Less specializations
  ////////////////////////////////////////////////////////////////////////

  //! Specialization of the adapter Less for pointers to subclasses
  //! of Element.
  //!
  //! \sa Less.
  template <typename TSubclass>
  struct Less<TSubclass*,
              std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
    //! Returns \c true if the object pointed to by \p x is less than the
    //! object pointed to by \p y.
    inline bool operator()(TSubclass const* x, TSubclass const* y) const {
      return *x < *y;
    }
  };

  // TODO(later) why is there no specialisation for non-pointers for
  // Less?

  ////////////////////////////////////////////////////////////////////////
  // One specializations
  ////////////////////////////////////////////////////////////////////////

  //! Specialization of the adapter One for pointers to subclasses
  //! of Element.
  //!
  //! \sa One.
  template <typename TSubclass>
  struct One<TSubclass*,
             std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
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
             std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
    //! Returns a new instance of the one of \p x.
    TSubclass operator()(TSubclass const& x) const {
      return static_cast<TSubclass>(x.identity());
    }

    //! Returns a new instance of the one of \p x.
    TSubclass operator()(size_t n) {
      return TSubclass(std::move(TSubclass::identity(n)));
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Product specializations
  ////////////////////////////////////////////////////////////////////////

  //! Specialization of the adapter Product for pointers to subclasses of
  //! Element.
  //!
  //! \sa Product.
  template <typename TSubclass>
  struct Product<TSubclass*,
                 std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
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
                 std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
    //! Changes \p xy in-place to hold the product of \p x and \p y using
    //! Element::redefine.
    void operator()(TSubclass&       xy,
                    TSubclass const& x,
                    TSubclass const& y,
                    size_t           tid = 0) {
      xy.redefine(x, y, tid);
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Swap specializations
  ////////////////////////////////////////////////////////////////////////

  //! Specialization of the adapter Swap for subclasses of Element.
  //!
  //! \sa Swap.
  template <typename TSubclass>
  struct Swap<TSubclass*,
              std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
    //! Swaps the object pointed to by \p x with the one pointed to by \p y.
    void operator()(TSubclass* x, TSubclass* y) const {
      x->swap(*y);
    }
  };

  // TODO(later) why is there no specialisation for non-pointers for
  // Swap?

  ////////////////////////////////////////////////////////////////////////
  // Inverse specializations
  ////////////////////////////////////////////////////////////////////////

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

  ////////////////////////////////////////////////////////////////////////
  // Hash specializations
  ////////////////////////////////////////////////////////////////////////

  //! Specialization of the adapter Hash for subclasses of Element.
  //!
  //! \sa Hash.
  template <typename TSubclass>
  struct Hash<TSubclass,
              std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
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
              std::enable_if_t<std::is_base_of<Element, TSubclass>::value>> {
    //! Returns \p x->hash_value()
    size_t operator()(TSubclass const* x) const {
      return x->hash_value();
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // EqualTo specializations
  ////////////////////////////////////////////////////////////////////////

  //! Specialization of the adapter EqualTo for pointers to subclasses of
  //! Element.
  //!
  //! \sa EqualTo.
  template <typename TSubclass>
  struct EqualTo<TSubclass*,
                 std::enable_if_t<std::is_base_of<libsemigroups::Element,
                                                  TSubclass>::value>> {
    //! Tests equality of two const Element pointers via equality of the
    //! Elements they point to.
    bool operator()(TSubclass const* x, TSubclass const* y) const {
      return *x == *y;
    }
  };

  // TODO(later) why is there no specialisation for non-pointers for
  // EqualTo?

  ////////////////////////////////////////////////////////////////////////
  // ImageRight/LeftAction - PartialPerm
  ////////////////////////////////////////////////////////////////////////

  // Slowest
  //! Specialization of the adapter ImageRightAction for instances of
  //! PartialPerm.
  //!
  //! \sa ImageRightAction
  template <typename T>
  struct ImageRightAction<PartialPerm<T>, PartialPerm<T>> {
    //! Stores the idempotent \f$(xy) ^ {-1}xy\f$ in \p res.
    void operator()(PartialPerm<T>&       res,
                    PartialPerm<T> const& pt,
                    PartialPerm<T> const& x) const noexcept {
      res.redefine(pt, x);
      res.swap(res.right_one());
    }
  };

  // Faster than the above, but slower than the below
  // works for T = std::vector and T = StaticVector1
  //! Specialization of the adapter ImageRightAction for instances of
  //! PartialPerm and std::vector.
  //!
  //! \sa ImageRightAction
  template <typename S, typename T>
  struct ImageRightAction<PartialPerm<S>, T> {
    //! Stores the image set of \c pt under \c x in \p res.
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
  //! Specialization of the adapter ImageRightAction for instances of
  //! PartialPerm and BitSet<N> (\f$0 \leq N \leq 64\f$).
  //!
  //! \sa ImageRightAction
  template <typename T, size_t N>
  struct ImageRightAction<PartialPerm<T>, BitSet<N>> {
    //! Stores the image set of \c pt under \c x in \p res.
    void operator()(BitSet<N>&            res,
                    BitSet<N> const&      pt,
                    PartialPerm<T> const& x) const {
      res.reset();
      // Apply the lambda to every set bit in pt
      pt.apply([&x, &res](size_t i) {
        if (x[i] != UNDEFINED) {
          res.set(x[i]);
        }
      });
    }
  };

  // Slowest
  //! Specialization of the adapter ImageLeftAction for instances of
  //! PartialPerm.
  //!
  //! \sa ImageLeftAction.
  template <typename T>
  struct ImageLeftAction<PartialPerm<T>, PartialPerm<T>> {
    //! Stores the idempotent \f$xy(xy) ^ {-1}\f$ in \p res.
    void operator()(PartialPerm<T>&       res,
                    PartialPerm<T> const& pt,
                    PartialPerm<T> const& x) const noexcept {
      res.redefine(x, pt);
      res.swap(res.left_one());
    }
  };

  // Fastest when used with BitSet<N>.
  // works for T = std::vector and T = BitSet<N>
  // Using BitSet<N> limits this to size 64. However, if we are trying to
  // compute a LeftAction object, then the max size of such is 2 ^ 64, which is
  // probably not achievable. So, for higher degrees, we will only be able to
  // compute relatively sparse LeftActions (i.e. not containing the majority of
  // the 2 ^ n possible subsets), in which case using vectors or
  // StaticVector1's might be not be appreciable slower anyway. All of this is
  // to say that it probably isn't worthwhile trying to make BitSet's work for
  // more than 64 bits.
  //! Specialization of the adapter ImageLeftAction for instances of
  //! PartialPerm and std::vector or BitSet<N> (\f$0 \leq N \leq 64\f$).
  //!
  //! \sa ImageLeftAction.
  template <typename S, typename T>
  struct ImageLeftAction<PartialPerm<S>, T> {
    void operator()(T& res, T const& pt, PartialPerm<S> const& x) const {
      //! Stores the inverse image set of \c pt under \c x in \p res.
      static PartialPerm<S> xx({});
      x.inverse(xx);
      ImageRightAction<PartialPerm<S>, T>()(res, pt, xx);
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Lambda/Rho - PartialPerm
  ////////////////////////////////////////////////////////////////////////

  // This currently limits the use of Konieczny to partial perms of degree at
  // most 64 with the default traits class, since we cannot know the degree
  // at compile time, only at run time.
  //! Specialization of the adapter LambdaValue for instances of PartialPerm.
  //! Note that the the type chosen here limits the Konieczny algorithm to
  //! PartialPerms of degree at most 64 (or 32 on 32-bit systems).
  //!
  //! \sa LambdaValue.
  template <typename T>
  struct LambdaValue<PartialPerm<T>> {
    static constexpr size_t N = BitSet<1>::max_size();
    //! For PartialPerms, \c type is BitSet<N>, representing the image of the
    //! PartialPerms.
    using type = BitSet<N>;
  };

  //! Specialization of the adapter RhoValue for instances of PartialPerm.
  //! Note that the the type chosen here limits the Konieczny algorithm to
  //! PartialPerms of degree at most 64 (or 32 on 32-bit systems).
  //!
  //! \sa RhoValue.
  template <typename T>
  struct RhoValue<PartialPerm<T>> {
    //! For PartialPerms, \c type is BitSet<N>, representing the domain of the
    //! PartialPerms.
    using type = typename LambdaValue<PartialPerm<T>>::type;
  };

  //! Specialization of the adapter Lambda for instances of PartialPerm and
  //! BitSet<N>.
  //!
  //! \sa Lambda.
  template <typename T, size_t N>
  struct Lambda<PartialPerm<T>, BitSet<N>> {
    //! Modifies \p res to contain the image set of \p x; that is, \p res[i]
    //! will be \c true if and only if `x[j] = i` for some \f$j\f$.
    void operator()(BitSet<N>& res, PartialPerm<T> const& x) const {
      if (x.degree() > N) {
        LIBSEMIGROUPS_EXCEPTION(
            "expected partial perm of degree at most %llu, found %llu",
            static_cast<uint64_t>(N),
            static_cast<uint64_t>(x.degree()));
      }
      res.reset();
      for (size_t i = 0; i < x.degree(); ++i) {
        if (x[i] != UNDEFINED) {
          res.set(x[i]);
        }
      }
    }
  };

  //! Specialization of the adapter Rho for instances of PartialPerm and
  //! BitSet<N>.
  //!
  //! \sa Rho.
  template <typename T, size_t N>
  struct Rho<PartialPerm<T>, BitSet<N>> {
    //! Modifies \p res to contain the domain of \p x; that is, \p res[i]
    //! will be \c true if and only if `x[i] != UNDEFINED`.
    void operator()(BitSet<N>& res, PartialPerm<T> const& x) const {
      if (x.degree() > N) {
        LIBSEMIGROUPS_EXCEPTION(
            "expected partial perm of degree at most %llu, found %llu",
            static_cast<uint64_t>(N),
            static_cast<uint64_t>(x.degree()));
      }
      static PartialPerm<T> xx({});
      x.inverse(xx);
      Lambda<PartialPerm<T>, BitSet<N>>()(res, xx);
    }
  };

  //! Specialization of the adapter Rank for instances of PartialPerm.
  //!
  //! \sa Rank and PartialPerm::crank.
  template <typename T>
  struct Rank<PartialPerm<T>> {
    //! Returns the rank of \p x.
    //!
    //! The rank of a PartialPerm is the number of points in the image.
    size_t operator()(PartialPerm<T> const& x) const {
      return x.crank();
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // ImageRight/LeftAction - Transformation
  ////////////////////////////////////////////////////////////////////////

  // Equivalent to OnSets in GAP
  // Slowest
  // works for T = std::vector and T = StaticVector1
  //! Specialization of the adapter ImageRightAction for instances of
  //! Transformation and std::vector.
  //!
  //! \sa ImageRightAction
  template <typename S, typename T>
  struct ImageRightAction<Transformation<S>, T> {
    //! Stores the image set of \c pt under \c x in \p res.
    void operator()(T& res, T const& pt, Transformation<S> const& x) const {
      res.clear();
      for (auto i : pt) {
        res.push_back(x[i]);
      }
      std::sort(res.begin(), res.end());
      res.erase(std::unique(res.begin(), res.end()), res.end());
    }
  };

  // Fastest, but limited to at most degree 64
  //! Specialization of the adapter ImageRightAction for instances of
  //! Transformation and BitSet<N> (\f$0 \leq N leq 64\f$).
  //!
  //! \sa ImageRightAction
  template <typename TIntType, size_t N>
  struct ImageRightAction<Transformation<TIntType>, BitSet<N>> {
    //! Stores the image set of \c pt under \c x in \p res.
    void operator()(BitSet<N>&                      res,
                    BitSet<N> const&                pt,
                    Transformation<TIntType> const& x) const {
      res.reset();
      // Apply the lambda to every set bit in pt
      pt.apply([&x, &res](size_t i) { res.set(x[i]); });
    }
  };

  // OnKernelAntiAction
  // T = StaticVector1<S> or std::vector<S>
  //! Specialization of the adapter ImageLeftAction for instances of
  //! Transformation and std::vector.
  //!
  //! \sa ImageLeftAction
  template <typename S, typename T>
  struct ImageLeftAction<Transformation<S>, T> {
    //! Stores the image of \p pt under the left action of \p x in \p res.
    void operator()(T& res, T const& pt, Transformation<S> const& x) const {
      res.clear();
      res.resize(x.degree());
      static thread_local std::vector<S> buf;
      buf.clear();
      buf.resize(x.degree(), S(UNDEFINED));
      S next = 0;

      for (size_t i = 0; i < res.size(); ++i) {
        if (buf[pt[x[i]]] == UNDEFINED) {
          buf[pt[x[i]]] = next++;
        }
        res[i] = buf[pt[x[i]]];
      }
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Lambda/Rho - Transformation
  ////////////////////////////////////////////////////////////////////////

  // This currently limits the use of Konieczny to transformation of degree at
  // most 64 with the default traits class, since we cannot know the degree at
  // compile time, only at run time.
  //! Specialization of the adapter LambdaValue for instances of Transformation.
  //! Note that the the type chosen here limits the Konieczny algorithm to
  //! Transformations of degree at most 64 (or 32 on 32-bit systems).
  //!
  //! \sa LambdaValue.
  template <typename T>
  struct LambdaValue<Transformation<T>> {
    //! For Transformations, \c type is the largest BitSet available,
    //! representing the image set of the Transformations.
    static constexpr size_t N = BitSet<1>::max_size();
    using type                = BitSet<N>;
  };

  // Benchmarks indicate that using std::vector yields similar performance to
  // using StaticVector1's.
  //! Specialization of the adapter RhoValue for instances of Transformation.
  //!
  //! \sa RhoValue.
  template <typename T>
  struct RhoValue<Transformation<T>> {
    //! For Transformation<T>s, \c type is std::vector<T>, representing the
    //! kernel of the Transformations.
    using type = std::vector<T>;
  };

  // T = std::vector or StaticVector1
  //! Specialization of the adapter Lambda for instances of Transformation and
  //! std::vector.
  //!
  //! \sa Lambda.
  template <typename S, typename T>
  struct Lambda<Transformation<S>, T> {
    // not noexcept because std::vector::resize isn't (although
    // StaticVector1::resize is).
    //! Modifies \p res to contain the image set of \p x; that is, \p res[i]
    //! will be \c true if and only if `x[j] = i` for some \f$j\f$.
    void operator()(T& res, Transformation<S> const& x) const {
      res.clear();
      res.resize(x.degree());
      for (size_t i = 0; i < res.size(); ++i) {
        res[i] = x[i];
      }
      std::sort(res.begin(), res.end());
      res.erase(std::unique(res.begin(), res.end()), res.end());
    }
  };

  //! Specialization of the adapter Lambda for instances of Transformation and
  //! BitSet<N>.
  //!
  //! \sa Lambda.
  template <typename T, size_t N>
  struct Lambda<Transformation<T>, BitSet<N>> {
    // not noexcept because it can throw
    //! Modifies \p res to contain the image set of \p x; that is, \p res[i]
    //! will be \c true if and only if `x[j] = i` for some \f$j\f$.
    void operator()(BitSet<N>& res, Transformation<T> const& x) const {
      if (x.degree() > N) {
        LIBSEMIGROUPS_EXCEPTION(
            "expected a transformation of degree at most %llu, found %llu",
            static_cast<uint64_t>(N),
            static_cast<uint64_t>(x.degree()));
      }
      res.reset();
      for (size_t i = 0; i < x.degree(); ++i) {
        res.set(x[i]);
      }
    }
  };

  // T = std::vector<S> or StaticVector1<S, N>
  //! Specialization of the adapter Rho for instances of Transformation and
  //! std::vector.
  //!
  //! \sa Rho.
  template <typename S, typename T>
  struct Rho<Transformation<S>, T> {
    // not noexcept because std::vector::resize isn't (although
    // StaticVector1::resize is).
    void operator()(T& res, Transformation<S> const& x) const {
      res.clear();
      res.resize(x.degree());
      static thread_local std::vector<S> buf;
      buf.clear();
      buf.resize(x.degree(), S(UNDEFINED));
      S next = 0;

      for (size_t i = 0; i < res.size(); ++i) {
        if (buf[x[i]] == UNDEFINED) {
          buf[x[i]] = next++;
        }
        res[i] = buf[x[i]];
      }
    }
  };

  //! Specialization of the adapter Rank for instances of Transformation.
  //!
  //! \sa Rank.
  template <typename T>
  struct Rank<Transformation<T>> {
    size_t operator()(Transformation<T> const& x) {
      return x.crank();
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // ImageRightAction - Permutation specialisation
  ////////////////////////////////////////////////////////////////////////

  //! Specialization of the adapter ImageRightAction for pointers to
  //! Permutation instances.
  //!
  //! \sa ImageRightAction.
  template <typename TValueType>
  struct ImageRightAction<
      Permutation<TValueType>*,
      TValueType,
      std::enable_if_t<std::is_integral<TValueType>::value>> {
    //! Returns the image of \p pt under \p x.
    TValueType operator()(Permutation<TValueType> const* x,
                          TValueType const               pt) {
      return (*x)[pt];
    }
  };

  //! Specialization of the adapter ImageRightAction for instances of
  //! Permutation.
  //!
  //! \sa ImageRightAction.
  template <typename TIntType>
  struct ImageRightAction<Permutation<TIntType>,
                          TIntType,
                          std::enable_if_t<std::is_integral<TIntType>::value>> {
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

}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_ELEMENT_ADAPTERS_HPP_
