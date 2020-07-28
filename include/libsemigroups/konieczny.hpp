//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019-20 Finn Smith
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
// This file contains a generic implementation of Konieczny's algorithm,
// originally for computing subsemigroups of the boolean matrix monoid.

// TODO(later):
// 1) exception safety!
// 3) expose iterators to relevant things in D classes
// 4) maps to D classes containing given L/R values
// 5) more reporting
// 6) remove pointers
// 7) 0-parameter constructor
//
// TODO(now):
// 4) Constructors
// 7) noexcept - FLS
// 8) linting - later
// 9) formatting - last

#ifndef LIBSEMIGROUPS_KONIECZNY_HPP_
#define LIBSEMIGROUPS_KONIECZNY_HPP_

#include <cstddef>        // for size_t
#include <set>            // for set
#include <type_traits>    // for is_pointer
#include <unordered_map>  // for unordered_map
#include <unordered_set>  // for unordered_set
#include <utility>        // for pair, make_pair
#include <vector>         // for vector

#include "action.hpp"                   // for LeftAction, RightAction
#include "bruidhinn-traits.hpp"         // for BruidhinnTraits
#include "constants.hpp"                // for UNDEFINED
#include "libsemigroups-debug.hpp"      // for LIBSEMIGROUPS_ASSERT
#include "libsemigroups-exception.hpp"  // for LIBSEMIGROUPS_EXCEPTION
#include "report.hpp"                   // for REPORT_DEFAULT
#include "runner.hpp"                   // for Runner
#include "timer.hpp"                    // for Timer

namespace libsemigroups {

  namespace detail {
    struct PairHash {
      //! Hashes a pair of size_t.
      size_t operator()(std::pair<size_t, size_t> const& x) const noexcept {
        // this is bad in general, but if the actions have > 2^32 points then
        // hash collisions in the index tables will probably be the least of our
        // worries
        return (x.first << 32) + x.second;
      }
    };
  }  // namespace detail

  //! Defined in ``konieczny.hpp``.
  //!
  //! This is a traits class for use with Konieczny.
  //!
  //! \sa Konieczny
  template <typename TElementType>
  struct KoniecznyTraits {
    //! The type of the elements of a Konieczny instance with const removed.
    using element_type =
        typename detail::BruidhinnTraits<TElementType>::value_type;

    //! \copydoc libsemigroups::Lambda
    using Lambda = ::libsemigroups::Lambda<element_type>;

    //! \copydoc libsemigroups::Rho
    using Rho = ::libsemigroups::Rho<element_type>;

    //! The type of lambda values of a Konieczny instance.
    //! \sa Lambda
    using lambda_value_type =
        typename ::libsemigroups::Lambda<element_type>::result_type;

    //! The type of lambda values of a Konieczny instance.
    //! \sa Rho
    using rho_value_type =
        typename ::libsemigroups::Rho<element_type>::result_type;

    //! The action of the elements on the lambda values.
    //! \sa ImageRightAction
    using LambdaAction = ImageRightAction<element_type, lambda_value_type>;

    //! The action of the elements on the rho values.
    //! \sa ImageLeftAction
    using RhoAction = ImageLeftAction<element_type, rho_value_type>;

    //! The orbit of the lambda values under LambdaAction
    //! \sa LambdaAction and RightAction
    using lambda_orb_type
        = RightAction<element_type, lambda_value_type, LambdaAction>;

    //! The orbit of the rho values under RhoAction
    //! \sa RhoAction and LeftAction
    using rho_orb_type = LeftAction<element_type, rho_value_type, RhoAction>;

    //! \copydoc libsemigroups::Product
    using Product = ::libsemigroups::Product<element_type>;

    //! \copydoc libsemigroups::Rank
    using Rank = ::libsemigroups::Rank<element_type>;

    //! \copydoc libsemigroups::One
    using One = ::libsemigroups::One<element_type>;

    //! \copydoc libsemigroups::VecHash
    using VecHash = ::libsemigroups::VecHash<element_type>;

    //! \copydoc libsemigroups::Hash
    using ElementHash = ::libsemigroups::Hash<element_type>;

    //! \copydoc libsemigroups::EqualTo
    using EqualTo = ::libsemigroups::EqualTo<element_type>;

    //! \copydoc libsemigroups::Swap
    using Swap = ::libsemigroups::Swap<element_type>;

    //! \copydoc libsemigroups::Less
    using Less = ::libsemigroups::Less<element_type>;

    //! \copydoc libsemigroups::Degree
    using Degree = ::libsemigroups::Degree<element_type>;
  };

  //! Defined in ``konieczny.hpp``.
  //!
  //! The class template Konieczny implements %Konieczny's algorithm as
  //! described in the article 'Green's equivalences in finite semigroups of
  //! binary relations' by Janusz %Konieczny; see [here] for more details.
  //! This algorithm is similar to that of Lallement and McFadden; see [this]
  //! paper for more details. It differs in being applicable to subsemigroups of
  //! a non-regular semigroup, though is essentially the same algorithm for
  //! elements which happen to be regular.
  //!
  //! A Konieczny instance is defined by a generating set, and the main
  //! member function is Konieczny::run, which implements
  //! %Konieczny's Algorithm. If Konieczny::run is invoked and
  //! Konieczny::finished returns \c true, then the size, partial order of
  //! \f$\mathscr{D}\f$-classes, and complete frames for each
  //! \f$\mathscr{D}\f$-class are known.
  //!
  //! \sa KoniecznyTraits, BaseDClass, RegularDClass, and NonRegularDClass
  //!
  //! [here]:  https://link.springer.com/article/10.1007/BF02573672
  //! [this]:
  //! https://www.sciencedirect.com/science/article/pii/S0747717108800570
  // TODO(??) Example
  template <typename TElementType,
            typename TTraits = KoniecznyTraits<TElementType>>
  class Konieczny : public Runner,
                    private detail::BruidhinnTraits<TElementType> {
    // pointers are not currently supported
    static_assert(!std::is_pointer<TElementType>::value,
                  "Pointer types are not currently supported by Konieczny");
    ////////////////////////////////////////////////////////////////////////
    // Konieczny - aliases - private
    ////////////////////////////////////////////////////////////////////////

    using internal_element_type =
        typename detail::BruidhinnTraits<TElementType>::internal_value_type;
    using internal_const_element_type = typename detail::BruidhinnTraits<
        TElementType>::internal_const_value_type;
    using internal_const_reference = typename detail::BruidhinnTraits<
        TElementType>::internal_const_reference;
    using internal_reference =
        typename detail::BruidhinnTraits<TElementType>::internal_reference;

    using PairHash = detail::PairHash;

    ////////////////////////////////////////////////////////////////////////
    // Konieczny - internal structs - private
    ////////////////////////////////////////////////////////////////////////

    struct InternalElementHash : private detail::BruidhinnTraits<TElementType> {
      using Hash = typename TTraits::ElementHash;
      size_t operator()(internal_const_element_type x) const {
        return Hash()(this->to_external_const(x));
      }
    };

    struct InternalEqualTo : private detail::BruidhinnTraits<TElementType> {
      bool operator()(internal_const_reference x,
                      internal_const_reference y) const {
        return EqualTo()(this->to_external_const(x),
                         this->to_external_const(y));
      }
    };

    struct InternalLess : private detail::BruidhinnTraits<TElementType> {
      bool operator()(internal_const_reference x,
                      internal_const_reference y) const {
        return Less()(this->to_external_const(x), this->to_external_const(y));
      }
    };

    struct InternalVecHash : private detail::BruidhinnTraits<TElementType> {
      //! Hashes a vector of internal_element_types.
      size_t operator()(std::vector<internal_element_type> const& vec) const {
        size_t hash = 0;
        for (internal_const_reference x : vec) {
          hash ^= Hash<element_type>()(this->to_external_const(x))
                  + 0x9e3779b97f4a7c16 + (hash << 6) + (hash >> 2);
        }
        return hash;
      }
    };

    struct InternalVecEqualTo : private detail::BruidhinnTraits<TElementType> {
      size_t operator()(std::vector<internal_element_type> const& x,
                        std::vector<internal_element_type> const& y) const {
        LIBSEMIGROUPS_ASSERT(x.size() == y.size());
        return std::equal(x.cbegin(), x.cend(), y.cbegin(), InternalEqualTo());
      }
    };

    template <typename TCollType>
    struct InternalCollFree : private detail::BruidhinnTraits<TElementType> {
      void operator()(TCollType const& x) {
        for (auto it = x.cbegin(); it != x.cend(); ++it) {
          this->internal_free(*it);
        }
      }
    };

    using InternalVecFree
        = InternalCollFree<std::vector<internal_element_type>>;
    using InternalSetFree
        = InternalCollFree<std::unordered_set<internal_element_type,
                                              InternalElementHash,
                                              InternalEqualTo>>;

   public:
    ////////////////////////////////////////////////////////////////////////
    // Konieczny - aliases - public
    ////////////////////////////////////////////////////////////////////////

    //! The type of the elements of the semigroup represented by \c this.
    using element_type = typename TTraits::element_type;

    //! The type of a const reference to an element of the semigroup represented
    //! by \c this.
    using const_reference = element_type const&;

    //! The type of indices of \f$\mathscr{D}\f$-classes in the semigroup
    //! represented by \c this. \sa cbegin_D_classes and
    //! cbegin_regular_D_classes
    using D_class_index_type = size_t;

    //! The type of the lambda values that the semigroup represented by \c this
    //! acts on.
    using lambda_value_type = typename TTraits::lambda_value_type;

    //! The type of the orbit of the lambda values under the action of the
    //! semigroup represented by \c this.
    using lambda_orb_type = typename TTraits::lambda_orb_type;

    //! The type of the rho values that the semigroup represented by \c this
    //! acts on.
    using rho_value_type = typename TTraits::rho_value_type;

    //! The type of the orbit of the rho values under the action of the
    //! semigroup represented by \c this.
    using rho_orb_type = typename TTraits::rho_orb_type;

    //! \copydoc libsemigroups::Degree
    using Degree = typename TTraits::Degree;

    //! \copydoc libsemigroups::EqualTo
    using EqualTo = typename TTraits::EqualTo;

    //! \copydoc libsemigroups::Lambda
    using Lambda = typename TTraits::Lambda;

    //! \copydoc libsemigroups::Less
    using Less = typename TTraits::Less;

    //! \copydoc libsemigroups::One
    using One = typename TTraits::One;

    //! \copydoc libsemigroups::Product
    using Product = typename TTraits::Product;

    //! \copydoc libsemigroups::Rank
    using Rank = typename TTraits::Rank;

    //! \copydoc libsemigroups::Rho
    using Rho = typename TTraits::Rho;

    //! \copydoc libsemigroups::Swap
    using Swap = typename TTraits::Swap;

   private:
    ////////////////////////////////////////////////////////////////////////
    // Konieczny - aliases - private
    ////////////////////////////////////////////////////////////////////////
    using lambda_orb_index_type     = typename lambda_orb_type::index_type;
    using lambda_orb_scc_index_type = typename lambda_orb_type::scc_index_type;
    using rho_orb_index_type        = typename rho_orb_type::index_type;
    using rho_orb_scc_index_type    = typename rho_orb_type::scc_index_type;

   public:
    ////////////////////////////////////////////////////////////////////////
    // Konieczny - constructor and destructor - public
    ////////////////////////////////////////////////////////////////////////

    //! Construct from generators.
    //!
    //! This is the default constructor for a semigroup generated by a vector
    //! of generators.  There can be duplicate generators and although they do
    //! not count as distinct elements, they do count as distinct generators.
    //! In other words, the generators of the semigroup are precisely (a copy
    //! of) \p gens in the same order they occur in \p gens.
    //!
    //! The generators \p gens are copied by the constructor, and so it is the
    //! responsibility of the caller to delete \p gens.
    //!
    //! \param gens the generators of the semigroup represented by \c this.
    //!
    //! \throws LibsemigroupsException if \p gens is empty, or
    //! Konieczny::Degree()(x) != Konieczny::Degree()(y) for \c x, \c y in
    //! \p gens.
    explicit Konieczny(std::vector<element_type> const& gens)
        : _adjoined_identity_contained(false),
          _computed_all_classes(false),
          _D_classes(),
          _D_rels(),
          _gens(),
          _group_indices(),
          _group_indices_rev(),
          _initialised(false),
          _lambda_orb(),
          _nonregular_reps(),
          _one(),
          _ranks(),
          _regular_D_classes(),
          _reg_reps(),
          _rho_orb(),
          _tmp_element1(),
          _tmp_element2(),
          _tmp_element3(),
          _tmp_lambda_value1(),
          _tmp_lambda_value2(),
          _tmp_rho_value1(),
          _tmp_rho_value2() {
      if (gens.empty()) {
        LIBSEMIGROUPS_EXCEPTION(
            "expected a positive number of generators, but got 0");
      }

      size_t const deg = Degree()(gens[0]);

      for (const_reference x : gens) {
        _gens.push_back(this->internal_copy(this->to_internal_const(x)));
        size_t const xdeg = Degree()(x);
        if (deg != xdeg) {
          LIBSEMIGROUPS_EXCEPTION(
              "element has degree %d but should have degree %d", xdeg, deg);
        }
      }

      _one = this->to_internal(One()(gens[0]));

      _tmp_element1 = this->internal_copy(_one);
      _tmp_element2 = this->internal_copy(_one);
      _tmp_element3 = this->internal_copy(_one);

      _tmp_lambda_value1 = Lambda()(gens[0]);
      _tmp_lambda_value2 = Lambda()(gens[0]);

      _tmp_rho_value1 = Lambda()(gens[0]);
      _tmp_rho_value2 = Lambda()(gens[0]);

      _gens.push_back(_one);  // TODO(later): maybe not this

      _nonregular_reps = std::vector<
          std::vector<std::pair<internal_element_type, D_class_index_type>>>(
          Rank()(this->to_external_const(_one)) + 1,
          std::vector<std::pair<internal_element_type, D_class_index_type>>());
      _reg_reps = std::vector<
          std::vector<std::pair<internal_element_type, D_class_index_type>>>(
          Rank()(this->to_external_const(_one)) + 1,
          std::vector<std::pair<internal_element_type, D_class_index_type>>());
    }

    ~Konieczny();

    ////////////////////////////////////////////////////////////////////////
    // Konieczny - forward class declarations - public
    ////////////////////////////////////////////////////////////////////////

    class BaseDClass;
    class RegularDClass;
    class NonRegularDClass;

    ////////////////////////////////////////////////////////////////////////
    // Konieczny - member functions - public
    ////////////////////////////////////////////////////////////////////////

    //! Returns the size of \c this.
    //!
    //! This involves computing complete frames for every
    //! \f$\mathscr{D}\f$-class of \c this, if they are not already computed.
    // TODO(later): current_size const noexcept
    size_t size();

    //! Returns the size of \c this.
    //!
    //! This involves computing the orbits of the Lambda and Rho values under
    //! the action of \c this, if they are not already computed.
    bool is_regular_element(internal_const_reference bm) {
      compute_orbs();
      if (find_group_index(bm) != UNDEFINED) {
        return true;
      }
      return false;
    }

    ////////////////////////////////////////////////////////////////////////
    // Konieczny - iterators - public
    ////////////////////////////////////////////////////////////////////////

    //! Returns a const iterator referring to a pointer to the first regular D-
    //! class of the semigroup.
    //!
    //! This member function does not perform any enumeration of the semigroup;
    //! the iterator returned may be invalidated by any call to a non-const
    //! member function of the Konieczny class.
    typename std::vector<RegularDClass*>::const_iterator
    cbegin_regular_D_classes() const {
      auto it = _regular_D_classes.cbegin();
      if (!_adjoined_identity_contained) {
        it++;
      }
      return it;
    }

    //! Returns a const iterator referring to past the pointer to the last
    //! regular \f$\mathscr{D}\f$-class of the semigroup.
    //!
    //! This member function does not perform any enumeration of the semigroup;
    //! the iterator returned may be invalidated by any call to a non-const
    //! member function of the Konieczny class.
    typename std::vector<RegularDClass*>::const_iterator
    cend_regular_D_classes() const noexcept {
      return _regular_D_classes.cend();
    }

    //! Returns a const iterator referring to a pointer to the first
    //! \f$\mathscr{D}\f$-class of the semigroup.
    //!
    //! This member function does not perform any enumeration of the semigroup;
    //! the iterator returned may be invalidated by any call to a non-const
    //! member function of the Konieczny class.
    typename std::vector<BaseDClass*>::const_iterator cbegin_D_classes() const {
      auto it = _D_classes.cbegin();
      if (!_adjoined_identity_contained) {
        it++;
      }
      return it;
    }

    //! Returns a const iterator referring to past the pointer to the last
    //! \f$\mathscr{D}\f$-class of the semigroup.
    //!
    //! This member function does not perform any enumeration of the semigroup;
    //! the iterator returned may be invalidated by any call to a non-const
    //! member function of the Konieczny class.
    typename std::vector<BaseDClass*>::const_iterator cend_D_classes() const
        noexcept {
      return _D_classes.cend();
    }

   private:
    ////////////////////////////////////////////////////////////////////////
    // Konieczny - utility methods - private
    ////////////////////////////////////////////////////////////////////////

    //! Finds a group index of a H class in the R class of \p x.
    // modifies _tmp_element1, _tmp_element2, _tmp_element3
    // modifies _tmp_lambda_value1
    // modifies _tmp_rho_value1
    lambda_orb_index_type find_group_index(internal_const_reference x) {
      Rho()(_tmp_rho_value1, this->to_external_const(x));
      Lambda()(_tmp_lambda_value1, this->to_external_const(x));
      lambda_orb_index_type lpos = _lambda_orb.position(_tmp_lambda_value1);
      LIBSEMIGROUPS_ASSERT(lpos != UNDEFINED);

      lambda_orb_scc_index_type lval_scc_id
          = _lambda_orb.digraph().scc_id(lpos);

      std::pair<rho_orb_index_type, lambda_orb_scc_index_type> key
          = std::make_pair(_rho_orb.position(_tmp_rho_value1), lval_scc_id);

      if (_group_indices.find(key) != _group_indices.end()) {
        return _group_indices.at(key);
      } else {
        // use _tmp_element2 since is_group_index modifies 1
        Product()(this->to_external(_tmp_element2),
                  this->to_external_const(x),
                  _lambda_orb.multiplier_to_scc_root(lpos));
        for (auto it = _lambda_orb.digraph().cbegin_scc(lval_scc_id);
             it < _lambda_orb.digraph().cend_scc(lval_scc_id);
             it++) {
          Product()(this->to_external(_tmp_element3),
                    this->to_external(_tmp_element2),
                    _lambda_orb.multiplier_from_scc_root(*it));
          if (is_group_index(this->to_external_const(x),
                             this->to_external(_tmp_element3))) {
            _group_indices.emplace(key, *it);
            return *it;
          }
        }
      }
      _group_indices.emplace(key, UNDEFINED);
      return UNDEFINED;
    }

    //! Finds the idempotent in the H class of \p x. Note that it is assumed
    //! that \p x is in a group H class.
    // TODO(later): it must be possible to do better than this
    void idem_in_H_class(internal_element_type&   res,
                         internal_const_reference x) const {
      this->to_external(res) = this->to_external_const(x);
      do {
        Swap()(this->to_external(res), this->to_external(_tmp_element1));
        Product()(this->to_external(res),
                  this->to_external_const(_tmp_element1),
                  this->to_external_const(x));
        Product()(this->to_external(_tmp_element1),
                  this->to_external_const(res),
                  this->to_external_const(res));
      } while (!InternalEqualTo()(res, _tmp_element1));
    }

    //! Finds an idempotent in the \f$\mathscr{D}\f$-class of \c x, if \c x is
    //! regular, and modifies \c x in place to be this idempotent
    // modifies _tmp_element1, _tmp_element2, and _tmp_element3
    // modifies _tmp_lambda_value1
    void make_idem(internal_reference x) {
      LIBSEMIGROUPS_ASSERT(Degree()(this->to_external_const(x))
                           == Degree()(this->to_external_const(_tmp_element1)));
      LIBSEMIGROUPS_ASSERT(Degree()(this->to_external_const(x))
                           == Degree()(this->to_external_const(_tmp_element2)));
      LIBSEMIGROUPS_ASSERT(is_regular_element(x));

      Product()(this->to_external(_tmp_element1),
                this->to_external_const(x),
                this->to_external_const(x));
      if (EqualTo()(this->to_external(_tmp_element1),
                    this->to_external_const(x))) {
        return;
      }

      lambda_orb_index_type i = find_group_index(x);
      Lambda()(_tmp_lambda_value1, this->to_external_const(x));
      lambda_orb_index_type pos = _lambda_orb.position(_tmp_lambda_value1);

      Product()(this->to_external(_tmp_element1),
                this->to_external_const(x),
                _lambda_orb.multiplier_to_scc_root(pos));
      Product()(this->to_external(_tmp_element2),
                this->to_external(_tmp_element1),
                _lambda_orb.multiplier_from_scc_root(i));

      idem_in_H_class(_tmp_element3, _tmp_element2);
      this->to_external(x) = this->to_external_const(_tmp_element3);
    }

    //! Finds the group inverse of \p x in its H class; i.e. the element \c y
    //! in the H class of \p x such that <tt> xy = \p id</tt>. Will run forever
    //! if no such element exists.
    void group_inverse(internal_element_type&   res,
                       internal_const_reference id,
                       internal_const_reference x) const {
      this->to_external(_tmp_element1) = this->to_external_const(x);
      do {
        Swap()(this->to_external(res), this->to_external(_tmp_element1));
        Product()(this->to_external(_tmp_element1),
                  this->to_external_const(res),
                  this->to_external_const(x));
      } while (!InternalEqualTo()(_tmp_element1, id));
    }

    //! Determines whether <tt>(x, y)</tt> forms a group index.
    // modifies _tmp_element1
    // modifies _tmp_lambda_value and _tmp_rho_value
    bool is_group_index(const_reference x, const_reference y) const {
      Product()(this->to_external(_tmp_element1), y, x);
      Lambda()(_tmp_lambda_value1, this->to_external(_tmp_element1));
      Rho()(_tmp_rho_value1, this->to_external(_tmp_element1));
      Lambda()(_tmp_lambda_value2, x);
      Rho()(_tmp_rho_value2, y);
      return _tmp_lambda_value1 == _tmp_lambda_value2
             && _tmp_rho_value1 == _tmp_rho_value2;
    }

    ////////////////////////////////////////////////////////////////////////
    // Konieczny - accessor member functions - private
    ////////////////////////////////////////////////////////////////////////
    void add_D_class(Konieczny::RegularDClass* D);
    void add_D_class(Konieczny::NonRegularDClass* D);

    typename std::vector<internal_element_type>::const_iterator
    cbegin_generators() const noexcept {
      return _gens.cbegin();
    }

    typename std::vector<internal_element_type>::const_iterator
    cend_generators() const noexcept {
      return _gens.cend();
    }

    ////////////////////////////////////////////////////////////////////////
    // Konieczny - initialisation member functions - private
    ////////////////////////////////////////////////////////////////////////
    void init();

    void compute_orbs() {
      detail::Timer t;
      REPORT_DEFAULT("Computing orbits . . .\n");

      if (!_lambda_orb.started()) {
        _lambda_orb.add_seed(Lambda()(this->to_external_const(_one)));
        for (internal_const_element_type g : _gens) {
          _lambda_orb.add_generator(this->to_external_const(g));
        }
      }
      if (!_rho_orb.started()) {
        _rho_orb.add_seed(Rho()(this->to_external_const(_one)));
        for (internal_const_element_type g : _gens) {
          _rho_orb.add_generator(this->to_external_const(g));
        }
      }
      _lambda_orb.run_until([this]() -> bool { return this->stopped(); });
      _rho_orb.run_until([this]() -> bool { return this->stopped(); });
      REPORT_DEFAULT("Found %llu lambda-values and %llu rho-values in %s\n",
                     _lambda_orb.current_size(),
                     _rho_orb.current_size(),
                     t.string());
    }

    ////////////////////////////////////////////////////////////////////////
    // Konieczny - Runner methods - private
    ////////////////////////////////////////////////////////////////////////
    bool finished_impl() const override;
    void run_impl() override;

    ////////////////////////////////////////////////////////////////////////
    // Konieczny - data - private
    ////////////////////////////////////////////////////////////////////////
    bool                                         _adjoined_identity_contained;
    bool                                         _computed_all_classes;
    std::vector<BaseDClass*>                     _D_classes;
    std::vector<std::vector<D_class_index_type>> _D_rels;
    std::vector<internal_element_type>           _gens;
    std::unordered_map<std::pair<rho_orb_index_type, lambda_orb_scc_index_type>,
                       lambda_orb_index_type,
                       PairHash>
        _group_indices;
    std::unordered_map<std::pair<rho_orb_scc_index_type, lambda_orb_index_type>,
                       rho_orb_index_type,
                       PairHash>
                    _group_indices_rev;
    bool            _initialised;
    lambda_orb_type _lambda_orb;
    std::vector<
        std::vector<std::pair<internal_element_type, D_class_index_type>>>
                                _nonregular_reps;
    internal_element_type       _one;
    std::set<size_t>            _ranks;
    std::vector<RegularDClass*> _regular_D_classes;
    std::vector<
        std::vector<std::pair<internal_element_type, D_class_index_type>>>
                                  _reg_reps;
    rho_orb_type                  _rho_orb;
    mutable internal_element_type _tmp_element1;
    mutable internal_element_type _tmp_element2;
    mutable internal_element_type _tmp_element3;
    mutable lambda_value_type     _tmp_lambda_value1;
    mutable lambda_value_type     _tmp_lambda_value2;
    mutable rho_value_type        _tmp_rho_value1;
    mutable rho_value_type        _tmp_rho_value2;
  };

  /////////////////////////////////////////////////////////////////////////////
  // BaseDClass
  /////////////////////////////////////////////////////////////////////////////

  //! Defined in ``konieczny.hpp``.
  //!
  //! The nested abstract class Konieczny::BaseDClass represents a
  //! \f$\mathscr{D}\f$-class via a complete frame as computed in %Konieczny's
  //! algorithm. See [here] for more details.
  //!
  //! A BaseDClass is defined by a pointer to the corresponding Konieczny
  //! object, together with a representative of the \f$\mathscr{D}\f$-class, but
  //! as an abstract class cannot be directly constructed; instead you should
  //! construct a RegularDClass or NonRegularDClass. Note that the values
  //! returned by calls to member functions of BaseDClass and its derived
  //! classes are unlikely to be correct unless the parent semigroup has been
  //! sufficiently enumerated.
  //!
  //! \sa Konieczny, RegularDClass, and NonRegularDClass
  //!
  //! [here]:  https://link.springer.com/article/10.1007/BF02573672
  template <typename TElementType, typename TTraits>
  class Konieczny<TElementType, TTraits>::BaseDClass
      : protected detail::BruidhinnTraits<TElementType> {
    ////////////////////////////////////////////////////////////////////////
    // BaseDClass - aliases - protected
    ////////////////////////////////////////////////////////////////////////
   protected:
    using left_indices_index_type  = size_t;
    using right_indices_index_type = size_t;

   protected:
    ////////////////////////////////////////////////////////////////////////
    // BaseDClass - constructor - protected
    ////////////////////////////////////////////////////////////////////////
    BaseDClass(Konieczny* parent, element_type& rep)
        : _class_computed(false),
          _H_class(),
          _H_class_computed(false),
          _left_mults(),
          _left_mults_inv(),
          _left_reps(),
          _mults_computed(false),
          _parent(parent),
          _rank(Rank()(rep)),
          _rep(this->to_internal(rep)),
          _reps_computed(false),
          _right_mults(),
          _right_mults_inv(),
          _right_reps(),
          _tmp_element(this->internal_copy(_rep)),
          _tmp_element2(this->internal_copy(_rep)),
          _tmp_element3(this->internal_copy(_rep)),
          _tmp_element4(this->internal_copy(_rep)),
          _tmp_internal_set(),
          _tmp_internal_vec(),
          _tmp_lambda_value(Lambda()(rep)),
          _tmp_rho_value(Rho()(rep)) {}

   public:
    ////////////////////////////////////////////////////////////////////////
    // BaseDClass - destructor - public
    ////////////////////////////////////////////////////////////////////////
    virtual ~BaseDClass() {
      // the user of _tmp_internal_vec/_tmp_internal_set is responsible for
      // freeing any necessary elements
      InternalVecFree()(_H_class);
      InternalVecFree()(_left_mults);
      InternalVecFree()(_left_mults_inv);
      InternalVecFree()(_left_reps);
      this->internal_free(_rep);
      InternalVecFree()(_right_mults);
      InternalVecFree()(_right_mults_inv);
      InternalVecFree()(_right_reps);
      this->internal_free(_tmp_element);
      this->internal_free(_tmp_element2);
      this->internal_free(_tmp_element3);
      this->internal_free(_tmp_element4);
    }

    ////////////////////////////////////////////////////////////////////////
    // BaseDClass - member functions - public
    ////////////////////////////////////////////////////////////////////////

    //! Returns the representative which defines \c this.
    //!
    //! The complete frame computed for \c this depends on the choice of
    //! representative. This function returns the representative used by \c
    //! this. This may not be the same representative as used to construct \c
    //! this, but is guaranteed to not change.
    const_reference rep() const {
      return this->to_external_const(_rep);
    }

    //! Returns whether the element \p x belongs to this
    //! \f$\mathscr{D}\f$-class.
    //!
    //! Given an element \p x of the semigroup represented by \c parent, this
    //! function returns whether \p x is an element of the
    //! \f$\mathscr{D}\f$-class represented by \c this. If \p x is not an
    //! element of the semigroup, then the behaviour is undefined.
    //! This member function involved computing most of the complete frame for
    //! \c this, if it is not already known.
    virtual bool contains(const_reference x) = 0;

    //! Returns whether the element \p x belongs to this
    //! \f$\mathscr{D}\f$-class.
    //!
    //! Given an element \p x of the semigroup represented by \c parent, this
    //! function returns whether \p x is an element of the
    //! \f$\mathscr{D}\f$-class represented by \c this. If \p x is not an
    //! element of the semigroup, then the behaviour is undefined. This overload
    //! of BaseDClass::contains is provided in order to avoid recalculating the
    //! rank of \p x when it is already known.
    //! This member function involves computing most of the complete frame for
    //! \c this, if it is not already known.
    bool contains(const_reference x, size_t rank) {
      return (rank == _rank && contains(x));
    }

    //! Returns the size of \c this.
    //!
    //! This member function involves computing most of the complete frame for
    //! \c this, if it is not already known.
    virtual size_t size() {
      init();
      return nr_L_classes() * nr_R_classes() * size_H_class();
    }

    //! Returns the number of L classes in \c this.
    //!
    //! This member function involves computing some of the complete frame for
    //! \c this, if it is not already known.
    size_t nr_L_classes() {
      compute_left_mults();
      return _left_mults.size();
    }

    //! Returns the number of L classes in \c this.
    //!
    //! This member function involves computing some of the complete frame for
    //! \c this, if it is not already known.
    size_t nr_R_classes() {
      compute_right_mults();
      return _right_mults.size();
    }

    //! Returns the number of L classes in \c this.
    //!
    //! This member function involves computing some of the complete frame for
    //! \c this, if it is not already known.
    size_t size_H_class() {
      compute_H_class();
      return _H_class.size();
    }

    // Returns a set of representatives of L- or R-classes covered by \c this.
    //
    // The \f$\mathscr{D}\f$-classes of the parent semigroup are enumerated
    // either by finding representatives of all L-classes or all R-classes. This
    // member function returns the representatives obtainable by multipliying
    // the representatives of \c this by generators on either the left or right.
    // uses _tmp_element, tmp_element2 _tmp_element3
    //! nodoc
    std::vector<internal_element_type>& covering_reps() {
      init();
      _tmp_internal_vec.clear();
      // TODO(later): how to best decide which side to calculate? One is often
      // faster
      if (_parent->_lambda_orb.size() < _parent->_rho_orb.size()) {
        for (internal_const_reference w : _left_reps) {
          for (auto it = _parent->cbegin_generators();
               it < _parent->cend_generators();
               ++it) {
            Product()(this->to_external(_tmp_element3),
                      this->to_external_const(w),
                      this->to_external_const(*it));
            // uses _tmp_element, _tmp_element2
            if (!contains(this->to_external(_tmp_element3))) {
              _tmp_internal_vec.push_back(this->internal_copy(_tmp_element3));
            }
          }
        }
      } else {
        for (internal_const_reference z : _right_reps) {
          for (auto it = _parent->cbegin_generators();
               it < _parent->cend_generators();
               ++it) {
            Product()(this->to_external(_tmp_element3),
                      this->to_external_const(*it),
                      this->to_external_const(z));
            // uses _tmp_element, _tmp_element2
            if (!contains(this->to_external(_tmp_element3))) {
              _tmp_internal_vec.push_back(this->internal_copy(_tmp_element3));
            }
          }
        }
      }
      std::sort(
          _tmp_internal_vec.begin(), _tmp_internal_vec.end(), InternalLess());
      auto it = std::unique(_tmp_internal_vec.begin(), _tmp_internal_vec.end());
      for (; it < _tmp_internal_vec.end(); ++it) {
        this->internal_free(*it);
      }
      _tmp_internal_vec.erase(it, _tmp_internal_vec.end());
      return _tmp_internal_vec;
    }

   protected:
    ////////////////////////////////////////////////////////////////////////
    // BaseDClass - iterators - protected
    ////////////////////////////////////////////////////////////////////////
    using const_iterator =
        typename std::vector<internal_element_type>::const_iterator;

    const_iterator cbegin_left_reps() {
      compute_left_reps();
      return _left_reps.cbegin();
    }

    const_iterator cend_left_reps() {
      compute_left_reps();
      return _left_reps.cend();
    }

    const_iterator cbegin_right_reps() {
      compute_right_reps();
      return _right_reps.cbegin();
    }

    const_iterator cend_right_reps() {
      compute_right_reps();
      return _right_reps.cend();
    }

    const_iterator cbegin_left_mults() {
      compute_left_mults();
      return _left_mults.cbegin();
    }

    const_iterator cend_left_mults() {
      compute_left_mults();
      return _left_mults.cend();
    }

    const_iterator cbegin_left_mults_inv() {
      compute_left_mults_inv();
      return _left_mults_inv.cbegin();
    }

    const_iterator cend_left_mults_inv() {
      compute_left_mults_inv();
      return _left_mults_inv.cend();
    }

    const_iterator cbegin_right_mults() {
      compute_right_mults();
      return _right_mults.cbegin();
    }

    const_iterator cend_right_mults() {
      compute_right_mults();
      return _right_mults.cend();
    }

    const_iterator cbegin_right_mults_inv() {
      compute_right_mults_inv();
      return _right_mults_inv.cbegin();
    }

    const_iterator cend_right_mults_inv() {
      compute_right_mults_inv();
      return _right_mults_inv.cend();
    }

    const_iterator cbegin_H_class() {
      compute_H_class();
      return _H_class.cbegin();
    }

    const_iterator cend_H_class() {
      compute_H_class();
      return _H_class.cend();
    }

    const_iterator cbegin_H_class_NC() const noexcept {
      return _H_class.cbegin();
    }

    const_iterator cend_H_class_NC() const noexcept {
      return _H_class.cend();
    }

    ////////////////////////////////////////////////////////////////////////
    // BaseDClass - initialisation member functions - protected
    ////////////////////////////////////////////////////////////////////////
    virtual void init()                    = 0;
    virtual void compute_left_mults()      = 0;
    virtual void compute_left_mults_inv()  = 0;
    virtual void compute_left_reps()       = 0;
    virtual void compute_right_mults()     = 0;
    virtual void compute_right_mults_inv() = 0;
    virtual void compute_right_reps()      = 0;
    virtual void compute_H_class()         = 0;

    ////////////////////////////////////////////////////////////////////////
    // BaseDClass - accessor member functions - protected
    ////////////////////////////////////////////////////////////////////////
    size_t nr_left_reps_NC() const noexcept {
      return _left_reps.size();
    }

    size_t nr_right_reps_NC() const noexcept {
      return _right_reps.size();
    }

    size_t size_H_class_NC() const noexcept {
      return _H_class.size();
    }

    void push_left_mult(internal_const_reference x) {
      _left_mults.push_back(this->internal_copy(x));
#ifdef LIBSEMIGROUPS_DEBUG
      if (_left_reps.size() >= _left_mults.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external_const(_rep),
                  this->to_external_const(x));
        LIBSEMIGROUPS_ASSERT(Lambda()(this->to_external(_tmp_element))
                             == Lambda()(this->to_external_const(
                                 _left_reps[_left_mults.size() - 1])));
      }
      if (_left_mults_inv.size() >= _left_mults.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external_const(_rep),
                  this->to_external_const(x));
        Product()(this->to_external(_tmp_element2),
                  this->to_external(_tmp_element),
                  this->to_external(_left_mults_inv[_left_mults.size() - 1]));
        LIBSEMIGROUPS_ASSERT(Lambda()(this->to_external_const(_rep))
                             == Lambda()(this->to_external(_tmp_element2)));
      }
#endif
    }

    void push_left_mult_inv(internal_const_reference x) {
      _left_mults_inv.push_back(this->internal_copy(x));
#ifdef LIBSEMIGROUPS_DEBUG
      if (_left_reps.size() >= _left_mults_inv.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external(_left_reps[_left_mults.size() - 1]),
                  this->to_external_const(x));
        LIBSEMIGROUPS_ASSERT(Lambda()(this->to_external_const(_rep))
                             == Lambda()(this->to_external(_tmp_element)));
      }
      if (_left_mults.size() >= _left_mults_inv.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external_const(_rep),
                  this->to_external(_left_mults[_left_mults_inv.size() - 1]));
        Product()(this->to_external(_tmp_element2),
                  this->to_external(_tmp_element),
                  this->to_external_const(x));
        LIBSEMIGROUPS_ASSERT(Lambda()(this->to_external_const(_rep))
                             == Lambda()(this->to_external(_tmp_element2)));
      }
#endif
    }

    void push_right_mult(internal_const_reference x) {
      _right_mults.push_back(this->internal_copy(x));
#ifdef LIBSEMIGROUPS_DEBUG
      if (_right_reps.size() >= _right_mults.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external_const(x),
                  this->to_external_const(_rep));
        LIBSEMIGROUPS_ASSERT(Rho()(this->to_external(_tmp_element))
                             == Rho()(this->to_external_const(
                                 _right_reps[_right_mults.size() - 1])));
      }
      if (_right_mults_inv.size() >= _right_mults.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external(_right_mults_inv[_right_mults.size() - 1]),
                  this->to_external_const(x));
        Product()(this->to_external(_tmp_element2),
                  this->to_external(_tmp_element),
                  this->to_external_const(_rep));
        LIBSEMIGROUPS_ASSERT(Rho()(this->to_external_const(_rep))
                             == Rho()(this->to_external(_tmp_element2)));
      }
#endif
    }

    void push_right_mult_inv(internal_const_reference x) {
      _right_mults_inv.push_back(this->internal_copy(x));
#ifdef LIBSEMIGROUPS_DEBUG
      if (_right_reps.size() >= _right_mults_inv.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external_const(x),
                  this->to_external(_right_reps[_right_mults.size() - 1]));
        LIBSEMIGROUPS_ASSERT(Rho()(this->to_external_const(_rep))
                             == Rho()(this->to_external(_tmp_element)));
      }
      if (_right_mults.size() >= _right_mults_inv.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external_const(x),
                  this->to_external(_right_mults[_right_mults_inv.size() - 1]));
        Product()(this->to_external(_tmp_element2),
                  this->to_external(_tmp_element),
                  this->to_external_const(_rep));
        LIBSEMIGROUPS_ASSERT(Rho()(this->to_external_const(_rep))
                             == Rho()(this->to_external(_tmp_element2)));
      }
#endif
    }

    void push_left_rep(internal_const_reference x) {
      _left_reps.push_back(this->internal_copy(x));
#ifdef LIBSEMIGROUPS_DEBUG
      if (_left_mults.size() >= _left_reps.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external_const(_rep),
                  this->to_external(_left_mults[_left_reps.size() - 1]));
        LIBSEMIGROUPS_ASSERT(Lambda()(this->to_external(_tmp_element))
                             == Lambda()(this->to_external_const(x)));
      }
      if (_left_mults_inv.size() >= _left_reps.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external_const(x),
                  this->to_external(_left_mults_inv[_left_reps.size() - 1]));
        LIBSEMIGROUPS_ASSERT(Lambda()(this->to_external_const(_rep))
                             == Lambda()(this->to_external(_tmp_element)));
      }
#endif
    }

    void push_right_rep(internal_const_reference x) {
      _right_reps.push_back(this->internal_copy(x));
#ifdef LIBSEMIGROUPS_DEBUG
      if (_right_mults.size() >= _right_reps.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external(_right_mults[_right_reps.size() - 1]),
                  this->to_external_const(_rep));
        LIBSEMIGROUPS_ASSERT(Rho()(this->to_external(_tmp_element))
                             == Rho()(this->to_external_const(x)));
      }
      if (_right_mults_inv.size() >= _right_reps.size()) {
        Product()(this->to_external(_tmp_element),
                  this->to_external(_right_mults_inv[_right_reps.size() - 1]),
                  this->to_external_const(x));
        LIBSEMIGROUPS_ASSERT(Rho()(this->to_external_const(_rep))
                             == Rho()(this->to_external(_tmp_element)));
      }
#endif
    }

    bool class_computed() const noexcept {
      return _class_computed;
    }

    bool mults_computed() const noexcept {
      return _mults_computed;
    }

    bool reps_computed() const noexcept {
      return _reps_computed;
    }

    bool H_class_computed() const noexcept {
      return _H_class_computed;
    }

    void set_class_computed(bool x) noexcept {
      _class_computed = x;
    }

    void set_mults_computed(bool x) noexcept {
      _mults_computed = x;
    }

    void set_reps_computed(bool x) noexcept {
      _reps_computed = x;
    }

    void set_H_class_computed(bool x) noexcept {
      _H_class_computed = x;
    }

    Konieczny* parent() const noexcept {
      return _parent;
    }

    // Watch out! Doesn't copy its argument
    void push_back_H_class(internal_element_type x) {
      _H_class.push_back(x);
    }

    lambda_value_type& tmp_lambda_value() const noexcept {
      return _tmp_lambda_value;
    }

    rho_value_type& tmp_rho_value() const noexcept {
      return _tmp_rho_value;
    }

    internal_element_type& tmp_element() const noexcept {
      return _tmp_element;
    }

    internal_element_type& tmp_element2() const noexcept {
      return _tmp_element2;
    }

    internal_element_type& tmp_element3() const noexcept {
      return _tmp_element3;
    }

    internal_element_type& tmp_element4() const noexcept {
      return _tmp_element4;
    }

    std::unordered_set<internal_element_type,
                       InternalElementHash,
                       InternalEqualTo>&
    internal_set() const noexcept {
      return _tmp_internal_set;
    }

    std::vector<internal_element_type>& internal_vec() const noexcept {
      return _tmp_internal_vec;
    }

    internal_reference unsafe_rep() noexcept {
      return _rep;
    }

   private:
    ////////////////////////////////////////////////////////////////////////
    // BaseDClass - data - private
    ////////////////////////////////////////////////////////////////////////
    bool                               _class_computed;
    std::vector<internal_element_type> _H_class;
    bool                               _H_class_computed;
    std::vector<internal_element_type> _left_mults;
    std::vector<internal_element_type> _left_mults_inv;
    std::vector<internal_element_type> _left_reps;
    bool                               _mults_computed;
    Konieczny*                         _parent;
    size_t                             _rank;
    internal_element_type              _rep;
    bool                               _reps_computed;
    std::vector<internal_element_type> _right_mults;
    std::vector<internal_element_type> _right_mults_inv;
    std::vector<internal_element_type> _right_reps;
    mutable internal_element_type      _tmp_element;
    mutable internal_element_type      _tmp_element2;
    mutable internal_element_type      _tmp_element3;
    mutable internal_element_type      _tmp_element4;
    mutable std::unordered_set<internal_element_type,
                               InternalElementHash,
                               InternalEqualTo>
                                               _tmp_internal_set;
    mutable std::vector<internal_element_type> _tmp_internal_vec;
    mutable lambda_value_type                  _tmp_lambda_value;
    mutable rho_value_type                     _tmp_rho_value;
  };

  /////////////////////////////////////////////////////////////////////////////
  // RegularDClass
  /////////////////////////////////////////////////////////////////////////////

  //! Defined in ``konieczny.hpp``.
  //!
  //! The nested class Konieczny::RegularDClass inherits from BaseDClass and
  //! represents a regular \f$\mathscr{D}\f$-class via a complete frame as
  //! computed in %Konieczny's algorithm. See [here] for more details.
  //!
  //! A RegularDClass is defined by a pointer to the corresponding Konieczny
  //! object, together with a representative of the \f$\mathscr{D}\f$-class.
  //!
  //! Note that the values returned by calls to member functions of
  //! RegularDClass are unlikely to be correct unless the parent semigroup has
  //! been sufficiently enumerated.
  //!
  //! \sa Konieczny, BaseDClass, and NonRegularDClass
  //!
  //! [here]:  https://link.springer.com/article/10.1007/BF02573672
  template <typename TElementType, typename TTraits>
  class Konieczny<TElementType, TTraits>::RegularDClass
      : public Konieczny<TElementType, TTraits>::BaseDClass {
    friend class Konieczny<TElementType, TTraits>::NonRegularDClass;

   private:
    ////////////////////////////////////////////////////////////////////////
    // RegularDClass - aliases - private
    ////////////////////////////////////////////////////////////////////////
    using konieczny_type = Konieczny<element_type>;
    using left_indices_index_type =
        typename konieczny_type::BaseDClass::left_indices_index_type;
    using right_indices_index_type =
        typename konieczny_type::BaseDClass::right_indices_index_type;
    using const_index_iterator =
        typename std::vector<lambda_orb_index_type>::const_iterator;
    using const_internal_iterator =
        typename std::vector<internal_element_type>::const_iterator;

   public:
    ////////////////////////////////////////////////////////////////////////
    // RegularDClass - constructor and destructor - public
    ////////////////////////////////////////////////////////////////////////

    //! Construct from a pointer to a Konieczny object and an element of the
    //! semigroup represented by the Konieczny object.
    //!
    //! The representative \p rep is not copied by the constructor, and so must
    //! not be modified by the user after constructing the RegularDClass. The
    //! behaviour of RegularDClass when \p rep is not an element of the
    //! semigroup represented by \p parent is undefined.
    //!
    //! \param parent a pointer to the Konieczny object representing the
    //! semigroup of which \c this represents a \f$\mathscr{D}\f$-class.
    //!
    //! \param rep a regular element of the semigroup represented by \p parent.
    //!
    //! \throws LibsemigroupsException if \p rep is an element of the semigroup
    //! represented by \p parent but is not regular.
    RegularDClass(Konieczny* parent, element_type& rep)
        : Konieczny::BaseDClass(parent, rep),
          _H_gens(),
          _H_gens_computed(false),
          _idem_reps_computed(false),
          _lambda_index_positions(),
          _left_idem_reps(),
          _left_indices(),
          _left_indices_computed(false),
          _rho_index_positions(),
          _right_idem_reps(),
          _right_indices(),
          _right_indices_computed(false) {
      if (!parent->is_regular_element(this->to_internal(rep))) {
        LIBSEMIGROUPS_EXCEPTION("RegularDClass: the representative "
                                "given should be regular");
      }
      parent->make_idem(this->unsafe_rep());
      Product()(
          this->to_external(this->tmp_element()), this->rep(), this->rep());
      LIBSEMIGROUPS_ASSERT(
          EqualTo()(this->to_external(this->tmp_element()), this->rep()));
    }

    virtual ~RegularDClass() {
      // _H_gens is contained in _H_class which is freed in ~BaseDClass
      InternalVecFree()(_left_idem_reps);
      InternalVecFree()(_right_idem_reps);
    }

    //! \copydoc BaseDClass::contains
    bool contains(const_reference bm) override {
      init();
      std::pair<lambda_orb_index_type, rho_orb_index_type> x
          = index_positions(bm);
      return x.first != UNDEFINED;
    }

    //! Returns the indices of the L and R classes of \c this that \p bm is in.
    //!
    //! Returns the indices of the L and R classes of \c this that \p bm is in,
    //! unless bm is not in \c this, in which case returns the pair (UNDEFINED,
    //! UNDEFINED). Requires computing part of the complete frame of \c this.
    std::pair<lambda_orb_index_type, rho_orb_index_type>
    index_positions(const_reference bm) {
      compute_left_indices();
      compute_right_indices();
      Lambda()(this->tmp_lambda_value(), bm);
      auto l_it = _lambda_index_positions.find(
          this->parent()->_lambda_orb.position(this->tmp_lambda_value()));
      if (l_it != _lambda_index_positions.end()) {
        Rho()(this->tmp_rho_value(), bm);
        auto r_it = _rho_index_positions.find(
            this->parent()->_rho_orb.position(this->tmp_rho_value()));
        if (r_it != _rho_index_positions.end()) {
          return std::make_pair(l_it->second, r_it->second);
        }
      }
      return std::make_pair(UNDEFINED, UNDEFINED);
    }

    //! Returns the number of idempotents in \c this.
    //!
    //! This member function involves computing most of the complete frame for
    //! \c this, if it is not already known.
    size_t nr_idempotents() {
      compute_idem_reps();
      size_t count = 0;
      for (auto it = _left_idem_reps.cbegin(); it < _left_idem_reps.cend();
           ++it) {
        for (auto it2 = _right_idem_reps.cbegin();
             it2 < _right_idem_reps.cend();
             ++it2) {
          if (this->parent()->is_group_index(*it2, *it)) {
            count++;
          }
        }
      }
      LIBSEMIGROUPS_ASSERT(count > 0);
      return count;
    }

   private:
    ////////////////////////////////////////////////////////////////////////
    // RegularDClass - initialisation member functions - private
    ////////////////////////////////////////////////////////////////////////

    // this is annoyingly a bit more complicated than the right indices
    // because the find_group_index method fixes the rval and loops
    // through the scc of the lval
    void compute_left_indices() {
      if (_left_indices_computed) {
        return;
      }
      _left_indices.clear();
      Lambda()(this->tmp_lambda_value(), this->rep());
      lambda_orb_index_type lval_pos
          = this->parent()->_lambda_orb.position(this->tmp_lambda_value());

      Rho()(this->tmp_rho_value(), this->rep());
      rho_orb_index_type rval_pos
          = this->parent()->_rho_orb.position(this->tmp_rho_value());
      lambda_orb_scc_index_type lval_scc_id
          = this->parent()->_lambda_orb.digraph().scc_id(lval_pos);
      rho_orb_scc_index_type rval_scc_id
          = this->parent()->_rho_orb.digraph().scc_id(rval_pos);

      std::pair<rho_orb_scc_index_type, lambda_orb_index_type> key
          = std::make_pair(rval_scc_id, 0);
      for (auto it
           = this->parent()->_lambda_orb.digraph().cbegin_scc(lval_scc_id);
           it < this->parent()->_lambda_orb.digraph().cend_scc(lval_scc_id);
           it++) {
        key.second = *it;
        if (this->parent()->_group_indices_rev.find(key)
            == this->parent()->_group_indices_rev.end()) {
          Product()(this->to_external(this->tmp_element()),
                    this->parent()->_rho_orb.multiplier_to_scc_root(rval_pos),
                    this->rep());
          Product()(
              this->to_external(this->tmp_element3()),
              this->rep(),
              this->parent()->_lambda_orb.multiplier_to_scc_root(lval_pos));

          for (auto it2
               = this->parent()->_rho_orb.digraph().cbegin_scc(rval_scc_id);
               it2 < this->parent()->_rho_orb.digraph().cend_scc(rval_scc_id);
               it2++) {
            Product()(this->to_external(this->tmp_element2()),
                      this->parent()->_rho_orb.multiplier_from_scc_root(*it2),
                      this->to_external(this->tmp_element()));
            Product()(
                this->to_external(this->tmp_element4()),
                this->to_external(this->tmp_element3()),
                this->parent()->_lambda_orb.multiplier_from_scc_root(*it));

            if (this->parent()->is_group_index(
                    this->to_external(this->tmp_element2()),
                    this->to_external(this->tmp_element4()))) {
              this->parent()->_group_indices_rev.emplace(key, *it2);
              break;
            }
          }
        }
        // TODO(later) prove this works
        LIBSEMIGROUPS_ASSERT(this->parent()->_group_indices_rev.at(key)
                             != UNDEFINED);
        _lambda_index_positions.emplace(*it, _left_indices.size());
        _left_indices.push_back(*it);
      }
#ifdef LIBSEMIGROUPS_DEBUG
      for (lambda_orb_index_type i : _left_indices) {
        LIBSEMIGROUPS_ASSERT(i < this->parent()->_lambda_orb.size());
      }
#endif
      this->_left_indices_computed = true;
    }

    void compute_right_indices() {
      if (_right_indices_computed) {
        return;
      }
      _right_indices.clear();

      Rho()(this->tmp_rho_value(), this->rep());
      rho_orb_index_type rval_pos
          = this->parent()->_rho_orb.position(this->tmp_rho_value());
      rho_orb_scc_index_type rval_scc_id
          = this->parent()->_rho_orb.digraph().scc_id(rval_pos);
      for (auto it = this->parent()->_rho_orb.digraph().cbegin_scc(rval_scc_id);
           it < this->parent()->_rho_orb.digraph().cend_scc(rval_scc_id);
           it++) {
        _rho_index_positions.emplace(*it, _right_indices.size());
        _right_indices.push_back(*it);
        Product()(this->to_external(this->tmp_element()),
                  this->parent()->_rho_orb.multiplier_from_scc_root(*it),
                  this->parent()->_rho_orb.multiplier_to_scc_root(rval_pos));

        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->rep());
        this->parent()->find_group_index(this->tmp_element2());
        LIBSEMIGROUPS_ASSERT(
            this->parent()->find_group_index(this->tmp_element2())
            != UNDEFINED);
      }
#ifdef LIBSEMIGROUPS_DEBUG
      for (rho_orb_index_type i : _right_indices) {
        LIBSEMIGROUPS_ASSERT(i < this->parent()->_rho_orb.size());
      }
#endif
      this->_right_indices_computed = true;
    }

    void compute_left_mults() override {
      compute_mults();
    }

    void compute_left_mults_inv() override {
      compute_mults();
    }

    void compute_left_reps() override {
      compute_reps();
    }

    void compute_right_mults() override {
      compute_mults();
    }

    void compute_right_mults_inv() override {
      compute_reps();
    }

    void compute_right_reps() override {
      compute_reps();
    }

    void compute_mults() {
      if (this->mults_computed()) {
        return;
      }
      compute_left_indices();
      compute_right_indices();

      Lambda()(this->tmp_lambda_value(), this->rep());
      Rho()(this->tmp_rho_value(), this->rep());
      lambda_value_type&    lval = this->tmp_lambda_value();
      lambda_orb_index_type lval_pos
          = this->parent()->_lambda_orb.position(lval);
      rho_value_type     rval     = this->tmp_rho_value();
      rho_orb_index_type rval_pos = this->parent()->_rho_orb.position(rval);

      for (lambda_orb_index_type idx : _left_indices) {
        // push_left_mult and push_left_mult_inv use tmp_element and
        // tmp_element2
        Product()(this->to_external(this->tmp_element3()),
                  this->parent()->_lambda_orb.multiplier_to_scc_root(lval_pos),
                  this->parent()->_lambda_orb.multiplier_from_scc_root(idx));
        this->push_left_mult(this->tmp_element3());
        Product()(
            this->to_external(this->tmp_element3()),
            this->parent()->_lambda_orb.multiplier_to_scc_root(idx),
            this->parent()->_lambda_orb.multiplier_from_scc_root(lval_pos));
        this->push_left_mult_inv(this->tmp_element3());
      }

      for (rho_orb_index_type idx : _right_indices) {
        // push_right_mult and push_right_mult_inv use tmp_element and
        // tmp_element2
        Product()(this->to_external(this->tmp_element3()),
                  this->parent()->_rho_orb.multiplier_from_scc_root(idx),
                  this->parent()->_rho_orb.multiplier_to_scc_root(rval_pos));
        this->push_right_mult(this->tmp_element3());
        Product()(this->to_external(this->tmp_element3()),
                  this->parent()->_rho_orb.multiplier_from_scc_root(rval_pos),
                  this->parent()->_rho_orb.multiplier_to_scc_root(idx));
        this->push_right_mult_inv(this->tmp_element3());
      }
      this->set_mults_computed(true);
    }

    void compute_reps() {
      if (this->reps_computed()) {
        return;
      }

      compute_mults();

      // push_left_rep and push_right_rep use tmp_element and tmp_element2
      for (auto it = this->cbegin_left_mults(); it < this->cend_left_mults();
           ++it) {
        Product()(this->to_external(this->tmp_element3()),
                  this->rep(),
                  this->to_external_const(*it));
        this->push_left_rep(this->tmp_element3());
      }

      for (auto it = this->cbegin_right_mults(); it < this->cend_right_mults();
           ++it) {
        Product()(this->to_external(this->tmp_element3()),
                  this->to_external_const(*it),
                  this->rep());
        this->push_right_rep(this->tmp_element3());
      }
      this->set_reps_computed(true);
    }

    void compute_H_gens() {
      if (_H_gens_computed) {
        return;
      }

      Rho()(this->tmp_rho_value(), this->rep());
      rho_value_type&        rval     = this->tmp_rho_value();
      rho_orb_index_type     rval_pos = this->parent()->_rho_orb.position(rval);
      rho_orb_scc_index_type rval_scc_id
          = this->parent()->_rho_orb.digraph().scc_id(rval_pos);

      // internal vec represents right inverses
      this->internal_vec().clear();

      for (size_t i = 0; i < _left_indices.size(); ++i) {
        std::pair<rho_orb_scc_index_type, lambda_orb_index_type> key
            = std::make_pair(rval_scc_id, _left_indices[i]);
        rho_orb_index_type       k = this->parent()->_group_indices_rev.at(key);
        right_indices_index_type j = _rho_index_positions.at(k);

        // for p a left rep and q an appropriate right rep,
        // find the product of q with the inverse of pq in H_rep
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(this->cbegin_left_reps()[i]),
                  this->to_external_const(this->cbegin_right_reps()[j]));

        this->parent()->group_inverse(this->tmp_element3(),
                                      this->to_internal_const(this->rep()),
                                      this->tmp_element());
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external_const(this->cbegin_right_reps()[j]),
                  this->to_external_const(this->tmp_element3()));
        this->internal_vec().push_back(
            this->internal_copy(this->tmp_element2()));
      }

      this->internal_set().clear();
      for (size_t i = 0; i < _left_indices.size(); ++i) {
        for (internal_const_reference g : this->parent()->_gens) {
          Product()(this->to_external(this->tmp_element()),
                    this->to_external_const(this->cbegin_left_reps()[i]),
                    this->to_external_const(g));
          Lambda()(this->tmp_lambda_value(),
                   this->to_external(this->tmp_element()));
          for (size_t j = 0; j < _left_indices.size(); ++j) {
            if (this->parent()->_lambda_orb.at(_left_indices[j])
                == this->tmp_lambda_value()) {
              Product()(this->to_external(this->tmp_element2()),
                        this->to_external(this->tmp_element()),
                        this->to_external_const(this->internal_vec()[j]));
              if (this->internal_set().find(this->tmp_element2())
                  == this->internal_set().end()) {
                internal_element_type x
                    = this->internal_copy(this->tmp_element2());
                this->internal_set().insert(x);
                _H_gens.push_back(x);
                break;
              }
            }
          }
        }
      }
      InternalVecFree()(this->internal_vec());
      this->_H_gens_computed = true;
    }

    void compute_idem_reps() {
      if (_idem_reps_computed) {
        return;
      }
      _left_idem_reps.clear();
      _right_idem_reps.clear();
      compute_left_indices();
      compute_right_indices();
      compute_mults();

      Lambda()(this->tmp_lambda_value(), this->rep());
      rho_value_type        rval = Rho()(this->rep());
      lambda_orb_index_type lval_pos
          = this->parent()->_lambda_orb.position(this->tmp_lambda_value());
      rho_orb_index_type rval_pos = this->parent()->_rho_orb.position(rval);
      lambda_orb_scc_index_type lval_scc_id
          = this->parent()->_lambda_orb.digraph().scc_id(lval_pos);
      rho_orb_scc_index_type rval_scc_id
          = this->parent()->_rho_orb.digraph().scc_id(rval_pos);

      // TODO(later): use information from the looping through the left indices
      // in the loop through the right indices
      for (size_t i = 0; i < _left_indices.size(); ++i) {
        auto               key = std::make_pair(rval_scc_id, _left_indices[i]);
        rho_orb_index_type k   = this->parent()->_group_indices_rev.at(key);
        size_t             j   = 0;
        while (_right_indices[j] != k) {
          ++j;
        }
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(this->cbegin_right_mults()[j]),
                  this->rep());
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->to_external_const(this->cbegin_left_mults()[i]));
        this->parent()->idem_in_H_class(this->tmp_element3(),
                                        this->tmp_element2());

        _left_idem_reps.push_back(this->internal_copy(this->tmp_element3()));
      }

      for (size_t j = 0; j < _right_indices.size(); ++j) {
        auto key = std::make_pair(_right_indices[j], lval_scc_id);
        lambda_orb_index_type k = this->parent()->_group_indices.at(key);
        size_t                i = 0;
        while (_left_indices[i] != k) {
          ++i;
        }
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(this->cbegin_right_mults()[j]),
                  this->rep());
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->to_external_const(this->cbegin_left_mults()[i]));

        this->parent()->idem_in_H_class(this->tmp_element3(),
                                        this->tmp_element2());

        _right_idem_reps.push_back(this->internal_copy(this->tmp_element3()));
      }
      this->_idem_reps_computed = true;
    }

    // there should be some way of getting rid of this
    void compute_H_class() override {
      if (this->H_class_computed()) {
        return;
      }
      compute_H_gens();

      LIBSEMIGROUPS_ASSERT(_H_gens.begin() != _H_gens.end());

      this->internal_set().clear();

      for (auto it = _H_gens.begin(); it < _H_gens.end(); ++it) {
        this->internal_set().insert(*it);
        this->push_back_H_class(*it);
      }

      for (size_t i = 0; i < this->size_H_class_NC(); ++i) {
        for (internal_const_reference g : _H_gens) {
          Product()(this->to_external(this->tmp_element()),
                    this->to_external_const(this->cbegin_H_class_NC()[i]),
                    this->to_external_const(g));
          if (this->internal_set().find(this->tmp_element())
              == this->internal_set().end()) {
            internal_element_type x = this->internal_copy(this->tmp_element());
            this->internal_set().insert(x);
            this->push_back_H_class(x);
          }
        }
      }
      this->set_H_class_computed(true);
    }

    void init() override {
      if (this->class_computed()) {
        return;
      }
      compute_left_indices();
      compute_right_indices();
      compute_mults();
      compute_reps();
      compute_idem_reps();
      compute_H_gens();
      compute_H_class();
      this->set_class_computed(true);
    }

    ////////////////////////////////////////////////////////////////////////
    // RegularDClass - accessor member functions - private (friend NonRegular)
    ////////////////////////////////////////////////////////////////////////
    const_index_iterator cbegin_left_indices() {
      compute_left_indices();
      return _left_indices.cbegin();
    }

    const_index_iterator cend_left_indices() {
      compute_left_indices();
      return _left_indices.cend();
    }

    const_index_iterator cbegin_right_indices() {
      compute_right_indices();
      return _right_indices.cbegin();
    }

    const_index_iterator cend_right_indices() {
      compute_right_indices();
      return _right_indices.cend();
    }

    const_internal_iterator cbegin_left_idem_reps() {
      compute_idem_reps();
      return _left_idem_reps.cbegin();
    }

    const_internal_iterator cend_left_idem_reps() {
      compute_idem_reps();
      return _left_idem_reps.cend();
    }

    const_internal_iterator cbegin_right_idem_reps() {
      compute_idem_reps();
      return _right_idem_reps.cbegin();
    }

    const_internal_iterator cend_right_idem_reps() {
      compute_idem_reps();
      return _right_idem_reps.cend();
    }

    ////////////////////////////////////////////////////////////////////////
    // RegularDClass - data - private
    ////////////////////////////////////////////////////////////////////////
    std::vector<internal_element_type> _H_gens;
    bool                               _H_gens_computed;
    bool                               _idem_reps_computed;
    std::unordered_map<lambda_orb_index_type, left_indices_index_type>
                                       _lambda_index_positions;
    std::vector<internal_element_type> _left_idem_reps;
    std::vector<lambda_orb_index_type> _left_indices;
    bool                               _left_indices_computed;
    std::unordered_map<rho_orb_index_type, right_indices_index_type>
                                       _rho_index_positions;
    std::vector<internal_element_type> _right_idem_reps;
    std::vector<rho_orb_index_type>    _right_indices;
    bool                               _right_indices_computed;
  };

  /////////////////////////////////////////////////////////////////////////////
  // NonRegularDClass
  /////////////////////////////////////////////////////////////////////////////

  //! Defined in ``konieczny.hpp``.
  //!
  //! The nested class Konieczny::NonRegularDClass inherits from BaseDClass
  //! and represents a regular \f$\mathscr{D}\f$-class via a complete frame as
  //! computed in %Konieczny's algorithm. See [here] for more details.
  //!
  //! A NonRegularDClass is defined by a pointer to the corresponding
  //! Konieczny object, together with a representative of the
  //! \f$\mathscr{D}\f$-class.
  //!
  //! Note that the values returned by calls to member functions of
  //! RegularDClass are unlikely to be correct unless the parent semigroup has
  //! been sufficiently enumerated.
  //!
  //! \sa Konieczny, BaseDClass, and RegularDClass
  //!
  //! [here]:  https://link.springer.com/article/10.1007/BF02573672
  template <typename TElementType, typename TTraits>
  class Konieczny<TElementType, TTraits>::NonRegularDClass
      : public Konieczny<TElementType, TTraits>::BaseDClass {
   private:
    ////////////////////////////////////////////////////////////////////////
    // NonRegularDClass - aliases - private
    ////////////////////////////////////////////////////////////////////////
    using konieczny_type = Konieczny<element_type>;
    using left_indices_index_type =
        typename konieczny_type::BaseDClass::left_indices_index_type;
    using right_indices_index_type =
        typename konieczny_type::BaseDClass::right_indices_index_type;

   public:
    ////////////////////////////////////////////////////////////////////////
    // NonRegularDClass - constructor and destructor - public
    ////////////////////////////////////////////////////////////////////////

    //! Construct from a pointer to a Konieczny object and an element of the
    //! semigroup represented by the Konieczny object.
    //!
    //! The representative \p rep is not copied by the constructor, and so must
    //! not be modified by the user after constructing the NonRegularDClass. The
    //! behaviour of NonRegularDClass when \p rep is not an element of the
    //! semigroup represented by \p parent is undefined.
    //!
    //! \param parent a pointer to the Konieczny object representing the
    //! semigroup of which \c this represents a \f$\mathscr{D}\f$-class.
    //!
    //! \param rep an element of the semigroup represented by \p parent.
    //!
    //! \throws LibsemigroupsException if \p rep is a regular element of the
    //! semigroup represented by \p parent.
    // TODO(later): should be a const reference
    NonRegularDClass(Konieczny* parent, element_type& rep)
        : Konieczny::BaseDClass(parent, rep),
          _H_set(),
          _lambda_index_positions(),
          _left_idem_above(this->to_internal(rep)),
          _left_idem_class(),
          _left_idem_H_class(),
          _left_idem_left_reps(),
          _rho_index_positions(),
          _right_idem_above(this->to_internal(rep)),
          _right_idem_class(),
          _right_idem_H_class(),
          _right_idem_right_reps() {
      if (parent->is_regular_element(this->to_internal(rep))) {
        LIBSEMIGROUPS_EXCEPTION("NonRegularDClass: the representative "
                                "given should not be idempotent");
      }
    }

    virtual ~NonRegularDClass() {
      InternalVecFree()(_left_idem_H_class);
      InternalVecFree()(_right_idem_H_class);
      InternalVecFree()(_left_idem_left_reps);
      InternalVecFree()(_right_idem_right_reps);
    }

    // uses _tmp_element, _tmp_element2
    // uses _tmp_lambda, _tmp_rho
    //! \copydoc BaseDClass::contains
    bool contains(const_reference bm) override {
      init();
      Lambda()(this->tmp_lambda_value(), bm);
      lambda_orb_index_type lpos
          = this->parent()->_lambda_orb.position(this->tmp_lambda_value());
      if (_lambda_index_positions[lpos].size() == 0) {
        return false;
      }
      Rho()(this->tmp_rho_value(), bm);
      rho_orb_index_type rpos
          = this->parent()->_rho_orb.position(this->tmp_rho_value());
      if (_rho_index_positions[rpos].size() == 0) {
        return false;
      }
      for (left_indices_index_type i : _lambda_index_positions[lpos]) {
        Product()(this->to_external(this->tmp_element()),
                  bm,
                  this->to_external_const(this->cbegin_left_mults_inv()[i]));
        for (right_indices_index_type j : _rho_index_positions[rpos]) {
          Product()(this->to_external(this->tmp_element2()),
                    this->to_external_const(this->cbegin_right_mults_inv()[j]),
                    this->to_external(this->tmp_element()));
          if (_H_set.find(this->tmp_element2()) != _H_set.end()) {
            return true;
          }
        }
      }
      return false;
    }

   private:
    ////////////////////////////////////////////////////////////////////////
    // NonRegularDClass - initialisation member functions - private
    ////////////////////////////////////////////////////////////////////////
    void init() override {
      if (this->class_computed()) {
        return;
      }
      find_idems_above();
      compute_H_class();
      compute_mults();
      construct_H_set();
      this->set_class_computed(true);
    }

    void find_idems_above() {
      // assumes that all D classes above this have already been calculated!
      bool left_found  = false;
      bool right_found = false;
      for (auto it = this->parent()->_regular_D_classes.rbegin();
           (!left_found || !right_found)
           && it != this->parent()->_regular_D_classes.rend();
           it++) {
        RegularDClass* D = *it;
        if (!left_found) {
          for (auto idem_it = D->cbegin_left_idem_reps();
               idem_it < D->cend_left_idem_reps();
               idem_it++) {
            Product()(this->to_external(this->tmp_element()),
                      this->rep(),
                      this->to_external_const(*idem_it));
            if (this->to_external(this->tmp_element()) == this->rep()) {
              _left_idem_above = *idem_it;
              _left_idem_class = D;
              left_found       = true;
              break;
            }
          }
        }

        if (!right_found) {
          for (auto idem_it = D->cbegin_right_idem_reps();
               idem_it < D->cend_right_idem_reps();
               idem_it++) {
            Product()(this->to_external(this->tmp_element()),
                      this->to_external_const(*idem_it),
                      this->rep());
            if (this->to_external(this->tmp_element()) == this->rep()) {
              _right_idem_above = *idem_it;
              _right_idem_class = D;
              right_found       = true;
              break;
            }
          }
        }
      }

#ifdef LIBSEMIGROUPS_DEBUG
      LIBSEMIGROUPS_ASSERT(
          _left_idem_class->contains(this->to_external(_left_idem_above)));
      LIBSEMIGROUPS_ASSERT(
          _right_idem_class->contains(this->to_external(_right_idem_above)));
      LIBSEMIGROUPS_ASSERT(left_found && right_found);
      Product()(this->to_external(this->tmp_element()),
                this->rep(),
                this->to_external(_left_idem_above));
      LIBSEMIGROUPS_ASSERT(
          EqualTo()(this->to_external(this->tmp_element()), this->rep()));
      Product()(this->to_external(this->tmp_element()),
                this->to_external(_right_idem_above),
                this->rep());
      LIBSEMIGROUPS_ASSERT(
          EqualTo()(this->to_external(this->tmp_element()), this->rep()));
#endif
    }

    void compute_H_class() override {
      if (this->H_class_computed()) {
        return;
      }
      std::pair<lambda_orb_index_type, rho_orb_index_type> left_idem_indices
          = _left_idem_class->index_positions(
              this->to_external(_left_idem_above));
      internal_const_element_type left_idem_left_mult
          = _left_idem_class->cbegin_left_mults()[left_idem_indices.first];
      internal_const_element_type left_idem_right_mult
          = _left_idem_class->cbegin_right_mults()[left_idem_indices.second];

      std::pair<lambda_orb_index_type, rho_orb_index_type> right_idem_indices
          = _right_idem_class->index_positions(
              this->to_external(_right_idem_above));
      internal_const_element_type right_idem_left_mult
          = _right_idem_class->cbegin_left_mults()[right_idem_indices.first];
      internal_const_element_type right_idem_right_mult
          = _right_idem_class->cbegin_right_mults()[right_idem_indices.second];

      for (auto it = _left_idem_class->cbegin_H_class();
           it < _left_idem_class->cend_H_class();
           it++) {
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(left_idem_right_mult),
                  this->to_external_const(*it));
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->to_external_const(left_idem_left_mult));
        _left_idem_H_class.push_back(this->internal_copy(this->tmp_element2()));
      }

      for (auto it = _right_idem_class->cbegin_H_class();
           it < _right_idem_class->cend_H_class();
           it++) {
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(right_idem_right_mult),
                  this->to_external_const(*it));
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->to_external_const(right_idem_left_mult));
        _right_idem_H_class.push_back(
            this->internal_copy(this->tmp_element2()));
      }

      for (auto it = _left_idem_class->cbegin_left_mults();
           it < _left_idem_class->cend_left_mults();
           it++) {
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(left_idem_right_mult),
                  _left_idem_class->rep());
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->to_external_const(*it));
        _left_idem_left_reps.push_back(
            this->internal_copy((this->tmp_element2())));
      }

      for (auto it = _right_idem_class->cbegin_right_mults();
           it < _right_idem_class->cend_right_mults();
           it++) {
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(*it),
                  _right_idem_class->rep());
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->to_external_const(right_idem_left_mult));
        _right_idem_right_reps.push_back(
            this->internal_copy((this->tmp_element2())));
      }

      static std::vector<internal_element_type> Hex;
      static std::vector<internal_element_type> xHf;

      for (internal_const_reference s : _left_idem_H_class) {
        Product()(this->to_external(this->tmp_element()),
                  this->rep(),
                  this->to_external_const(s));
        xHf.push_back(this->internal_copy(this->tmp_element()));
      }

      for (internal_const_reference t : _right_idem_H_class) {
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(t),
                  this->rep());
        Hex.push_back(this->internal_copy(this->tmp_element()));
      }

      static std::unordered_set<internal_element_type,
                                InternalElementHash,
                                InternalEqualTo>
          s;
      this->internal_set().clear();
      for (auto it = Hex.begin(); it < Hex.end(); ++it) {
        if (!this->internal_set().insert(*it).second) {
          this->internal_free(*it);
        }
      }
      Hex.clear();
      Hex.assign(this->internal_set().begin(), this->internal_set().end());

      this->internal_set().clear();
      for (auto it = xHf.begin(); it < xHf.end(); ++it) {
        if (!this->internal_set().insert(*it).second) {
          this->internal_free(*it);
        }
      }
      xHf.clear();
      xHf.assign(this->internal_set().begin(), this->internal_set().end());

      std::sort(Hex.begin(), Hex.end(), InternalLess());
      std::sort(xHf.begin(), xHf.end(), InternalLess());

      this->internal_vec().clear();
      std::set_intersection(Hex.begin(),
                            Hex.end(),
                            xHf.begin(),
                            xHf.end(),
                            std::back_inserter(this->internal_vec()),
                            InternalLess());

      for (auto it = this->internal_vec().cbegin();
           it < this->internal_vec().cend();
           ++it) {
        this->push_back_H_class(this->internal_copy(*it));
      }

      InternalVecFree()(xHf);
      InternalVecFree()(Hex);
      Hex.clear();
      xHf.clear();

      this->set_H_class_computed(true);
    }

    void compute_mults() {
      if (this->mults_computed()) {
        return;
      }
      std::pair<lambda_orb_index_type, rho_orb_index_type> left_idem_indices
          = _left_idem_class->index_positions(
              this->to_external(_left_idem_above));
      internal_const_element_type left_idem_left_mult
          = _left_idem_class->cbegin_left_mults()[left_idem_indices.first];

      std::pair<lambda_orb_index_type, rho_orb_index_type> right_idem_indices
          = _right_idem_class->index_positions(
              this->to_external(_right_idem_above));
      internal_const_element_type right_idem_right_mult
          = _right_idem_class->cbegin_right_mults()[right_idem_indices.second];

      static std::unordered_set<std::vector<internal_element_type>,
                                InternalVecHash,
                                InternalVecEqualTo>
          Hxhw_set;
      Hxhw_set.clear();

      static std::unordered_set<std::vector<internal_element_type>,
                                InternalVecHash,
                                InternalVecEqualTo>
          Hxh_set;
      Hxh_set.clear();

      static std::unordered_set<std::vector<internal_element_type>,
                                InternalVecHash,
                                InternalVecEqualTo>
          zhHx_set;
      zhHx_set.clear();

      static std::unordered_set<std::vector<internal_element_type>,
                                InternalVecHash,
                                InternalVecEqualTo>
          hHx_set;
      hHx_set.clear();

      for (internal_const_reference h : _left_idem_H_class) {
        static std::vector<internal_element_type> Hxh;
        LIBSEMIGROUPS_ASSERT(Hxh.empty());
        for (auto it = this->cbegin_H_class(); it < this->cend_H_class();
             ++it) {
          Product()(this->to_external(this->tmp_element()),
                    this->to_external_const(*it),
                    this->to_external_const(h));
          Hxh.push_back(this->internal_copy(this->tmp_element()));
        }

        std::sort(Hxh.begin(), Hxh.end(), InternalLess());
        if (Hxh_set.find(Hxh) == Hxh_set.end()) {
          for (size_t i = 0; i < _left_idem_left_reps.size(); ++i) {
            static std::vector<internal_element_type> Hxhw;
            Hxhw.clear();

            for (auto it = Hxh.cbegin(); it < Hxh.cend(); ++it) {
              Product()(this->to_external(this->tmp_element()),
                        this->to_external_const(*it),
                        this->to_external_const(_left_idem_left_reps[i]));
              Hxhw.push_back(this->internal_copy(this->tmp_element()));
            }

            std::sort(Hxhw.begin(), Hxhw.end(), InternalLess());
            if (Hxhw_set.find(Hxhw) == Hxhw_set.end()) {
              Hxhw_set.insert(std::move(Hxhw));

              Product()(this->to_external(this->tmp_element3()),
                        this->to_external_const(h),
                        this->to_external_const(_left_idem_left_reps[i]));
              Product()(this->to_external(this->tmp_element4()),
                        this->rep(),
                        this->to_external(this->tmp_element3()));
              Lambda()(this->tmp_lambda_value(),
                       this->to_external(this->tmp_element4()));
              lambda_orb_index_type lpos = this->parent()->_lambda_orb.position(
                  this->tmp_lambda_value());
              auto it = _lambda_index_positions.find(lpos);
              if (it == _lambda_index_positions.end()) {
                _lambda_index_positions.emplace(
                    lpos, std::vector<left_indices_index_type>());
              }
              _lambda_index_positions[lpos].push_back(this->nr_left_reps_NC());

              // push_left_rep and push_left_mult use tmp_element and
              // tmp_element2
              this->push_left_rep(this->tmp_element4());
              this->push_left_mult(this->tmp_element3());

              Product()(this->to_external(this->tmp_element()),
                        this->to_external_const(_left_idem_left_reps[i]),
                        this->to_external_const(
                            _left_idem_class->cbegin_left_mults_inv()[i]));
              Product()(this->to_external(this->tmp_element2()),
                        this->to_external(this->tmp_element()),
                        this->to_external_const(left_idem_left_mult));
              this->parent()->group_inverse(
                  this->tmp_element3(), _left_idem_above, this->tmp_element2());
              this->parent()->group_inverse(
                  this->tmp_element4(), _left_idem_above, h);
              Product()(this->to_external(this->tmp_element()),
                        this->to_external(this->tmp_element3()),
                        this->to_external(this->tmp_element4()));

              Product()(this->to_external(this->tmp_element2()),
                        this->to_external_const(
                            _left_idem_class->cbegin_left_mults_inv()[i]),
                        this->to_external_const(left_idem_left_mult));
              Product()(this->to_external(this->tmp_element3()),
                        this->to_external(this->tmp_element2()),
                        this->to_external(this->tmp_element()));
              this->push_left_mult_inv(this->tmp_element3());
            } else {
              InternalVecFree()(Hxhw);
            }
          }
          Hxh_set.insert(std::move(Hxh));
        } else {
          InternalVecFree()(Hxh);
        }
        Hxh.clear();
      }

      for (auto it = Hxh_set.begin(); it != Hxh_set.end(); ++it) {
        InternalVecFree()(*it);
      }

      for (auto it = Hxhw_set.begin(); it != Hxhw_set.end(); ++it) {
        InternalVecFree()(*it);
      }

      for (internal_const_reference h : _right_idem_H_class) {
        static std::vector<internal_element_type> hHx;
        LIBSEMIGROUPS_ASSERT(hHx.empty());

        for (auto it = this->cbegin_H_class(); it < this->cend_H_class();
             ++it) {
          Product()(this->to_external(this->tmp_element()),
                    this->to_external_const(h),
                    this->to_external_const(*it));
          hHx.push_back(this->internal_copy(this->tmp_element()));
        }

        std::sort(hHx.begin(), hHx.end(), InternalLess());
        if (hHx_set.find(hHx) == hHx_set.end()) {
          for (size_t i = 0; i < _right_idem_right_reps.size(); ++i) {
            static std::vector<internal_element_type> zhHx;
            zhHx.clear();
            for (auto it = hHx.cbegin(); it < hHx.cend(); ++it) {
              Product()(this->to_external(this->tmp_element()),
                        this->to_external_const(_right_idem_right_reps[i]),
                        this->to_external_const(*it));
              zhHx.push_back(this->internal_copy(this->tmp_element()));
            }

            std::sort(zhHx.begin(), zhHx.end(), InternalLess());
            if (zhHx_set.find(zhHx) == zhHx_set.end()) {
              zhHx_set.insert(std::move(zhHx));
              // push_right_rep and push_right_mult use tmp_element and
              // tmp_element2
              Product()(this->to_external(this->tmp_element3()),
                        this->to_external_const(_right_idem_right_reps[i]),
                        this->to_external_const(h));
              Product()(this->to_external(this->tmp_element4()),
                        this->to_external(this->tmp_element3()),
                        this->rep());

              Rho()(this->tmp_rho_value(),
                    this->to_external(this->tmp_element4()));
              rho_orb_index_type rpos
                  = this->parent()->_rho_orb.position(this->tmp_rho_value());
              auto it = _rho_index_positions.find(rpos);
              if (it == _rho_index_positions.end()) {
                _rho_index_positions.emplace(
                    rpos, std::vector<right_indices_index_type>());
              }
              _rho_index_positions[rpos].push_back(this->nr_right_reps_NC());
              this->push_right_rep(this->tmp_element4());
              this->push_right_mult(this->tmp_element3());

              Product()(this->to_external(this->tmp_element()),
                        this->to_external_const(right_idem_right_mult),
                        this->to_external_const(
                            _right_idem_class->cbegin_right_mults_inv()[i]));
              Product()(this->to_external(this->tmp_element2()),
                        this->to_external(this->tmp_element()),
                        this->to_external_const(_right_idem_right_reps[i]));

              this->parent()->group_inverse(
                  this->tmp_element3(), _right_idem_above, h);
              this->parent()->group_inverse(this->tmp_element4(),
                                            _right_idem_above,
                                            this->tmp_element2());
              Product()(this->to_external(this->tmp_element()),
                        this->to_external(this->tmp_element3()),
                        this->to_external(this->tmp_element4()));

              Product()(this->to_external(this->tmp_element2()),
                        this->to_external_const(right_idem_right_mult),
                        this->to_external_const(
                            _right_idem_class->cbegin_right_mults_inv()[i]));
              Product()(this->to_external(this->tmp_element3()),
                        this->to_external(this->tmp_element()),
                        this->to_external(this->tmp_element2()));
              this->push_right_mult_inv(this->tmp_element3());
            } else {
              InternalVecFree()(zhHx);
            }
          }
          hHx_set.insert(std::move(hHx));
        } else {
          InternalVecFree()(hHx);
        }
        hHx.clear();
      }

      for (auto it = hHx_set.begin(); it != hHx_set.end(); ++it) {
        InternalVecFree()(*it);
      }

      for (auto it = zhHx_set.begin(); it != zhHx_set.end(); ++it) {
        InternalVecFree()(*it);
      }
      this->set_mults_computed(true);
    }

    void construct_H_set() {
      _H_set.clear();
      for (auto it = this->cbegin_H_class(); it < this->cend_H_class(); ++it) {
        _H_set.insert(*it);
      }
    }

    void compute_left_mults() override {
      compute_mults();
    }

    void compute_left_mults_inv() override {
      compute_mults();
    }

    void compute_left_reps() override {
      compute_mults();
    }

    void compute_right_mults() override {
      compute_mults();
    }

    void compute_right_mults_inv() override {
      compute_mults();
    }

    void compute_right_reps() override {
      compute_mults();
    }

    ////////////////////////////////////////////////////////////////////////
    // NonRegularDClass - data - private
    ////////////////////////////////////////////////////////////////////////
    std::unordered_set<internal_element_type,
                       InternalElementHash,
                       InternalEqualTo>
        _H_set;
    std::unordered_map<lambda_orb_index_type,
                       std::vector<left_indices_index_type>>
                                       _lambda_index_positions;
    internal_element_type              _left_idem_above;
    RegularDClass*                     _left_idem_class;
    std::vector<internal_element_type> _left_idem_H_class;
    std::vector<internal_element_type> _left_idem_left_reps;
    std::unordered_map<rho_orb_index_type,
                       std::vector<right_indices_index_type>>
                                       _rho_index_positions;
    internal_element_type              _right_idem_above;
    RegularDClass*                     _right_idem_class;
    std::vector<internal_element_type> _right_idem_H_class;
    std::vector<internal_element_type> _right_idem_right_reps;
  };

  template <typename TElementType, typename TTraits>
  Konieczny<TElementType, TTraits>::~Konieczny() {
    for (BaseDClass* D : _D_classes) {
      delete D;
    }
    // _one is included in _gens
    for (internal_element_type x : _gens) {
      this->internal_free(x);
    }
    this->internal_free(_tmp_element1);
    this->internal_free(_tmp_element2);
    this->internal_free(_tmp_element3);
  }

  template <typename TElementType, typename TTraits>
  void
  Konieczny<TElementType, TTraits>::add_D_class(Konieczny::RegularDClass* D) {
    _regular_D_classes.push_back(D);
    _D_classes.push_back(D);
    _D_rels.push_back(std::vector<D_class_index_type>());
  }

  template <typename TElementType, typename TTraits>
  void Konieczny<TElementType, TTraits>::add_D_class(
      Konieczny<TElementType, TTraits>::NonRegularDClass* D) {
    _D_classes.push_back(D);
    _D_rels.push_back(std::vector<D_class_index_type>());
  }

  template <typename TElementType, typename TTraits>
  size_t Konieczny<TElementType, TTraits>::size() {
    run();
    size_t out = 0;
    auto   it  = _D_classes.begin();
    if (!_adjoined_identity_contained) {
      it++;
    }
    for (; it < _D_classes.end(); it++) {
      out += (*it)->size();
    }
    return out;
  }

  template <typename TElementType, typename TTraits>
  bool Konieczny<TElementType, TTraits>::finished_impl() const {
    return _computed_all_classes;
  }

  template <typename TElementType, typename TTraits>
  void Konieczny<TElementType, TTraits>::init() {
    if (_initialised) {
      return;
    }
    // compute orbits (can stop during these enumerations)
    compute_orbs();
    // we might have stopped; then we shouldn't attempt to anything else since
    // the orbs may not have been fully enumerated and hence we cannot compute D
    // classes
    if (stopped()) {
      return;
    }
    // initialise the _ranks set
    _ranks.insert(0);
    // compute the D class of the adjoined identity and its covering reps
    internal_element_type y   = this->internal_copy(_one);
    RegularDClass*        top = new RegularDClass(this, this->to_external(y));
    add_D_class(top);
    for (internal_reference x : top->covering_reps()) {
      size_t rnk = Rank()(this->to_external_const(x));
      _ranks.insert(rnk);
      if (is_regular_element(x)) {
        _reg_reps[rnk].emplace_back(x, 0);
      } else {
        _nonregular_reps[rnk].emplace_back(x, 0);
      }
    }
    // Set whether the adjoined one is in the semigroup or not
    // i.e. whether the generators contain multiple elements in the top D
    // class
    bool flag = false;
    for (internal_const_element_type x : _gens) {
      if (_D_classes[0]->contains(this->to_external_const(x))) {
        if (flag) {
          _adjoined_identity_contained = true;
          break;
        } else {
          flag = true;
        }
      }
    }

    _initialised = true;
  }

  template <typename TElementType, typename TTraits>
  void Konieczny<TElementType, TTraits>::run_impl() {
    // initialise the required data
    init();
    // if we haven't initialised, it should be because we stopped() during
    // init(), and hence we should not continue
    if (!_initialised) {
      LIBSEMIGROUPS_ASSERT(stopped());
      return;
    }

    std::vector<std::pair<internal_element_type, D_class_index_type>> next_reps;
    std::vector<std::pair<internal_element_type, D_class_index_type>> tmp_next;
    std::vector<std::pair<internal_element_type, D_class_index_type>> tmp;
    while (!stopped() && *_ranks.rbegin() > 0) {
      next_reps.clear();
      bool   reps_are_reg = false;
      size_t max_rank     = *_ranks.rbegin();
      if (!_reg_reps[max_rank].empty()) {
        reps_are_reg = true;
        next_reps    = std::move(_reg_reps[max_rank]);
        _reg_reps[max_rank].clear();
      } else {
        next_reps = std::move(_nonregular_reps[max_rank]);
        _nonregular_reps[max_rank].clear();
      }

      tmp_next.clear();
      for (auto it = next_reps.begin(); it < next_reps.end(); it++) {
        bool contained = false;
        // TODO(later) we can do better than this
        for (size_t i = 0; i < _D_classes.size(); ++i) {
          if (_D_classes[i]->contains(this->to_external_const(it->first),
                                      max_rank)) {
            _D_rels[i].push_back(it->second);
            contained = true;
            break;
          }
        }
        if (contained) {
          this->internal_free(it->first);
        } else {
          tmp_next.push_back(*it);
        }
      }
      next_reps = std::move(tmp_next);

      while (!next_reps.empty()) {
        if (report()) {
          REPORT_DEFAULT("computed %d D classes, so far\n", _D_classes.size());
        }
        BaseDClass*                                          D;
        std::pair<internal_element_type, D_class_index_type> tup(_one, 0);

        if (reps_are_reg) {
          tup = next_reps.back();
          D   = new RegularDClass(this, this->to_external(tup.first));
          add_D_class(static_cast<RegularDClass*>(D));
          for (internal_reference x : D->covering_reps()) {
            size_t rnk = Rank()(this->to_external_const(x));
            _ranks.insert(rnk);
            if (is_regular_element(x)) {
              _reg_reps[rnk].emplace_back(x, _D_classes.size() - 1);
            } else {
              _nonregular_reps[rnk].emplace_back(x, _D_classes.size() - 1);
            }
          }
          next_reps.pop_back();
        } else {
          tup = next_reps.back();
          D   = new NonRegularDClass(this, this->to_external(tup.first));
          add_D_class(static_cast<NonRegularDClass*>(D));
          for (internal_reference x : D->covering_reps()) {
            size_t rnk = Rank()(this->to_external_const(x));
            _ranks.insert(rnk);
            if (is_regular_element(x)) {
              _reg_reps[rnk].emplace_back(x, _D_classes.size() - 1);
            } else {
              _nonregular_reps[rnk].emplace_back(x, _D_classes.size() - 1);
            }
          }
          next_reps.pop_back();
        }

        tmp.clear();
        for (auto& x : next_reps) {
          if (D->contains(this->to_external_const(x.first))) {
            _D_rels[_D_classes.size() - 1].push_back(x.second);
            this->internal_free(x.first);
          } else {
            tmp.push_back(std::move(x));
          }
        }
        next_reps = std::move(tmp);
      }
      LIBSEMIGROUPS_ASSERT(_reg_reps[max_rank].empty());
      if (_nonregular_reps[max_rank].empty()) {
        _ranks.erase(max_rank);
        max_rank = *_ranks.rbegin();
      }
    }

    if (*_ranks.rbegin() == 0) {
      _computed_all_classes = true;
    }

    report_why_we_stopped();
  }
}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_KONIECZNY_HPP_
