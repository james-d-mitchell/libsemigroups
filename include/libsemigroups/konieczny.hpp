//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019 Finn Smith
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
// This file contains an implementation of Konieczny's algorithm for computing
// subsemigroups of the boolean matrix monoid.

// TODO(later):
// 1) exception safety!
// 2) IWYU
//
// TODO(now):
// 1) more reporting
// 2) BruidhinnTraits
// 3) free everything that needs to be freed!

#ifndef LIBSEMIGROUPS_INCLUDE_KONIECZNY_HPP_
#define LIBSEMIGROUPS_INCLUDE_KONIECZNY_HPP_

#include <algorithm>
#include <map>
#include <set>
#include <tuple>
#include <unordered_set>
#include <vector>

#include <iostream>

#include "action.hpp"
#include "bruidhinn-traits.hpp"  // for BruidhinnTraits
#include "constants.hpp"
#include "libsemigroups-config.hpp"     // for LIBSEMIGROUPS_ASSERT
#include "libsemigroups-debug.hpp"      // for LIBSEMIGROUPS_ASSERT
#include "libsemigroups-exception.hpp"  // for LIBSEMIGROUPS_ASSERT

// TODO: copying?
// TODO: profiling

namespace libsemigroups {

  namespace konieczny_helpers {

    // TODO: it must be possible to do better than this
    template <typename TElementType>
    TElementType idem_in_H_class(TElementType const& bm) {
      TElementType tmp = bm;
      while (tmp * tmp != tmp) {
        tmp = tmp * bm;
      }
      return tmp;
    }
  }  // namespace konieczny_helpers

  //! Provides a call operator returning a hash value for a pair of size_t.
  //!
  //! This struct provides a call operator for obtaining a hash value for the
  //! pair.
  // TODO(now) Replace this with specalization of Hash for pairs
  struct PairHash {
    //! Hashes a pair of size_t.
    size_t operator()(std::pair<size_t, size_t> x) const {
      return std::get<0>(x) + std::get<1>(x) + 0x9e3779b97f4a7c16;
    }
  };

  template <typename TElementType>
  struct KoniecznyTraits {
    using element_type =
        typename detail::BruidhinnTraits<TElementType>::value_type;

    using Lambda = ::libsemigroups::Lambda<element_type>;
    using Rho    = ::libsemigroups::Rho<element_type>;

    using lambda_value_type =
        typename ::libsemigroups::Lambda<element_type>::result_type;
    using rho_value_type =
        typename ::libsemigroups::Rho<element_type>::result_type;

    using LambdaAction = ImageRightAction<element_type, lambda_value_type>;
    using RhoAction    = ImageLeftAction<element_type, rho_value_type>;

    using lambda_orb_type
        = RightAction<element_type, lambda_value_type, LambdaAction>;
    using rho_orb_type = LeftAction<element_type, rho_value_type, RhoAction>;

    using Product     = ::libsemigroups::Product<element_type>;
    using Rank        = ::libsemigroups::Rank<element_type>;
    using One         = ::libsemigroups::One<element_type>;
    using VecHash     = ::libsemigroups::VecHash<element_type>;
    using ElementHash = ::libsemigroups::Hash<element_type>;
    using EqualTo     = ::libsemigroups::EqualTo<element_type>;
    using Swap        = ::libsemigroups::Swap<element_type>;
    using Less        = ::libsemigroups::Less<element_type>;
  };

  template <typename TElementType,
            typename TTraits = KoniecznyTraits<TElementType>>
  class Konieczny : public Runner,
                    private detail::BruidhinnTraits<TElementType> {
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
        if (x.size() != y.size()) {
          return false;
        }
        return std::equal(x.cbegin(), x.cend(), y.cbegin(), InternalEqualTo());
      }
    };

    //TODO: merge the following structs
    struct InternalVecFree : private detail::BruidhinnTraits<TElementType> {
      void operator()(std::vector<internal_element_type> const & x) { 
        for (auto it = x.cbegin(); it < x.cend(); ++it) {
          this->internal_free(*it);
        }
      }
    };
    
    struct InternalSetFree : private detail::BruidhinnTraits<TElementType> {
      void operator()(std::unordered_set<internal_element_type,
                                         InternalElementHash,
                                         InternalEqualTo> const& x) {
        for (auto it = x.cbegin(); it != x.cend(); ++it) {
          this->internal_free(*it);
        }
      }
    };

   public:
    using element_type    = typename TTraits::element_type;
    using const_reference = element_type const&;

    using lambda_value_type = typename TTraits::lambda_value_type;
    using rho_value_type    = typename TTraits::rho_value_type;

    using lambda_orb_type = typename TTraits::lambda_orb_type;
    using rho_orb_type    = typename TTraits::rho_orb_type;

    using Product = typename TTraits::Product;
    using Lambda  = typename TTraits::Lambda;
    using Rho     = typename TTraits::Rho;
    using Rank    = typename TTraits::Rank;
    using One     = typename TTraits::One;
    using EqualTo = typename TTraits::EqualTo;
    using Swap    = typename TTraits::Swap;
    using Less    = typename TTraits::Less;

    // TODO(now) replace with aliases into lambda_orb_type/rho_orb_type
    using rho_orb_index_type        = size_t;
    using rho_orb_scc_index_type    = size_t;
    using lambda_orb_index_type     = size_t;
    using lambda_orb_scc_index_type = size_t;
    using D_class_index_type        = size_t;

    explicit Konieczny(std::vector<element_type> const& gens)
        : _adjoined_identity_contained(false),
          _computed_all_classes(false),
          _D_classes(),
          _D_rels(),
          _gens(),
          _group_indices(),
          _group_indices_alt(),
          _lambda_orb(),
          _nonregular_reps(),
          _one(),
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
      // TODO(FLS): add more argument checks here!

      for (const_reference x : gens) {
        _gens.push_back(this->internal_copy(this->to_internal_const(x)));
      }

      if (_gens.empty()) {
        LIBSEMIGROUPS_EXCEPTION(
            "expected a positive number of generators, but got 0");
      }

      _one = this->to_internal(One()(gens[0]));

      _tmp_element1 = this->internal_copy(_one);
      _tmp_element2 = this->internal_copy(_one);
      _tmp_element3 = this->internal_copy(_one);

      // TODO(now): use internal/external for lambda/rho values too
      _tmp_lambda_value1 = Lambda()(gens[0]);
      _tmp_lambda_value2 = Lambda()(gens[0]);

      // TODO(now): use internal/external for lambda/rho values too
      _tmp_rho_value1 = Lambda()(gens[0]);
      _tmp_rho_value2 = Lambda()(gens[0]);

      _gens.push_back(_one);  // TODO: maybe not this

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

    void run_impl() override;
    bool finished_impl() const override;

    //! Finds a group index of a H class in the R class of \p bm
    // modifies _tmp_element1, _tmp_element2, _tmp_element3
    // modifies _tmp_lambda_value1
    // modifies _tmp_rho_value1
    lambda_orb_index_type find_group_index(internal_const_reference bm) {
      Rho()(_tmp_rho_value1, this->to_external_const(bm));
      Lambda()(_tmp_lambda_value1, this->to_external_const(bm));
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
                  this->to_external_const(bm),
                  _lambda_orb.multiplier_to_scc_root(lpos));
        for (auto it = _lambda_orb.digraph().cbegin_scc(lval_scc_id);
             it < _lambda_orb.digraph().cend_scc(lval_scc_id);
             it++) {
          Product()(this->to_external(_tmp_element3),
                    this->to_external(_tmp_element2),
                    _lambda_orb.multiplier_from_scc_root(*it));
          if (is_group_index(this->to_external_const(bm),
                             this->to_external(_tmp_element3))) {
            _group_indices.emplace(key, *it);
            return *it;
          }
        }
      }
      _group_indices.emplace(key, UNDEFINED);
      return UNDEFINED;
    }

    bool is_regular_element(internal_const_reference bm) {
      if (find_group_index(bm) != UNDEFINED) {
        return true;
      }
      return false;
    }

    // modifies _tmp_element1
    // modifies _tmp_lambda_value and _tmp_rho_value
    bool is_group_index(const_reference x, const_reference y) {
      Product()(this->to_external(_tmp_element1), y, x);
      Lambda()(_tmp_lambda_value1, this->to_external(_tmp_element1));
      Rho()(_tmp_rho_value1, this->to_external(_tmp_element1));
      Lambda()(_tmp_lambda_value2, x);
      Rho()(_tmp_rho_value2, y);
      return _tmp_lambda_value1 == _tmp_lambda_value2
             && _tmp_rho_value1 == _tmp_rho_value2;
    }

    // TODO(now) have this modify an argument in place
    //! Finds an idempotent in the D class of \c bm, if \c bm is regular
    // modifies _tmp_element1 and _tmp_element2
    // modifies _tmp_lambda_value1
    internal_element_type find_idem(internal_const_reference bm) {
      LIBSEMIGROUPS_ASSERT(
          Degree<element_type>()(this->to_external_const(bm))
          == Degree<element_type>()(this->to_external_const(_tmp_element1)));
      LIBSEMIGROUPS_ASSERT(
          Degree<element_type>()(this->to_external_const(bm))
          == Degree<element_type>()(this->to_external_const(_tmp_element2)));
      Product()(this->to_external(_tmp_element1),
                this->to_external_const(bm),
                this->to_external_const(bm));
      if (EqualTo()(this->to_external(_tmp_element1),
                    this->to_external_const(bm))) {
        return this->internal_copy(bm);
      }
      if (!is_regular_element(bm)) {
        // TODO: exception/assertion
      }
      lambda_orb_index_type i = find_group_index(bm);
      Lambda()(_tmp_lambda_value1, this->to_external_const(bm));
      lambda_orb_index_type pos = _lambda_orb.position(_tmp_lambda_value1);

      Product()(this->to_external(_tmp_element1),
                this->to_external_const(bm),
                _lambda_orb.multiplier_to_scc_root(pos));
      Product()(this->to_external(_tmp_element2),
                this->to_external(_tmp_element1),
                _lambda_orb.multiplier_from_scc_root(i));

      return this->to_internal(konieczny_helpers::idem_in_H_class<element_type>(
          this->to_external(_tmp_element2)));
    }

    void group_inverse(internal_element_type&   res,
                       internal_const_reference id,
                       internal_const_reference bm) {
      this->to_external(_tmp_element1) = this->to_external_const(bm);
      do {
        Swap()(this->to_external(res), this->to_external(_tmp_element1));
        Product()(this->to_external(_tmp_element1),
                  this->to_external_const(res),
                  this->to_external_const(bm));
      } while (!InternalEqualTo()(_tmp_element1, id));
    }

    class BaseDClass;
    class RegularDClass;
    class NonRegularDClass;

    // TODO: these shouldn't be accessible like this
    // and they shouldn't include the top D class if it's not contained!
    std::vector<RegularDClass*> regular_D_classes() {
      return _regular_D_classes;
    }

    std::vector<BaseDClass*> D_classes() {
      return _D_classes;
    }

    size_t size();

   private:
    void add_D_class(Konieczny::RegularDClass* D);
    void add_D_class(Konieczny::NonRegularDClass* D);

    void compute_orbs() {
      detail::Timer t;
      REPORT_DEFAULT("Computing orbits . . .\n");

      _lambda_orb.add_seed(Lambda()(this->to_external_const(_one)));
      _rho_orb.add_seed(Rho()(this->to_external_const(_one)));
      for (internal_const_element_type g : _gens) {
        _lambda_orb.add_generator(this->to_external_const(g));
        _rho_orb.add_generator(this->to_external_const(g));
      }
      // TODO(now) the following also need to be sensitive to being stopped()
      _lambda_orb.run();
      _rho_orb.run();
      REPORT_DEFAULT("Found %llu lambda-values and %llu rho-values in %s\n",
                     _lambda_orb.size(),
                     _rho_orb.size(),
                     t.string());
    }

    typename std::vector<internal_element_type>::const_iterator
    cbegin_generators() const {
      return _gens.cbegin();
    }

    typename std::vector<internal_element_type>::const_iterator
    cend_generators() const {
      return _gens.cend();
    }

    bool                     _adjoined_identity_contained;
    bool                     _computed_all_classes;
    std::vector<BaseDClass*> _D_classes;
    // contains in _D_rels[i] the indices of the D classes which lie above
    // _D_classes[i]
    std::vector<std::vector<D_class_index_type>> _D_rels;
    std::vector<internal_element_type>           _gens;
    std::unordered_map<std::pair<rho_orb_index_type, lambda_orb_scc_index_type>,
                       lambda_orb_index_type,
                       PairHash>
        _group_indices;
    std::unordered_map<std::pair<rho_orb_scc_index_type, lambda_orb_index_type>,
                       rho_orb_index_type,
                       PairHash>
                    _group_indices_alt;  // TODO better name
    lambda_orb_type _lambda_orb;
    std::vector<
        std::vector<std::pair<internal_element_type, D_class_index_type>>>
                                _nonregular_reps;
    internal_element_type       _one;
    std::vector<RegularDClass*> _regular_D_classes;
    std::vector<
        std::vector<std::pair<internal_element_type, D_class_index_type>>>
                                  _reg_reps;
    rho_orb_type                  _rho_orb;
    mutable internal_element_type _tmp_element1;
    mutable internal_element_type _tmp_element2;
    mutable internal_element_type _tmp_element3;
    lambda_value_type             _tmp_lambda_value1;
    lambda_value_type             _tmp_lambda_value2;
    rho_value_type                _tmp_rho_value1;
    rho_value_type                _tmp_rho_value2;
  };

  /////////////////////////////////////////////////////////////////////////////
  // BaseDClass
  /////////////////////////////////////////////////////////////////////////////

  template <typename TElementType, typename TTraits>
  class Konieczny<TElementType, TTraits>::BaseDClass
      : protected detail::BruidhinnTraits<TElementType> {
   private:
    ////////////////////////////////////////////////////////////////////////
    // Konieczny::BaseDClass - aliases - private
    ////////////////////////////////////////////////////////////////////////
    // TODO(now): check if all of these are used
    using internal_element_type =
        typename detail::BruidhinnTraits<TElementType>::internal_value_type;
    using internal_const_element_type = typename detail::BruidhinnTraits<
        TElementType>::internal_const_value_type;
    using internal_const_reference = typename detail::BruidhinnTraits<
        TElementType>::internal_const_reference;

   public:
    using konieczny_type    = Konieczny<TElementType, TTraits>;
    using element_type      = konieczny_type::element_type;
    using lambda_value_type = konieczny_type::lambda_value_type;

    using left_indices_index_type  = size_t;
    using right_indices_index_type = size_t;

    using Rank = konieczny_type::Rank;

    BaseDClass(Konieczny* parent, internal_const_reference rep)
        : _class_computed(false),
          _H_class(),
          _H_class_computed(false),
          _internal_set(),
          _internal_vec(),
          _left_mults(),
          _left_mults_inv(),
          _left_reps(),
          _mults_computed(false),
          _parent(parent),
          _rank(Rank()(this->to_external_const(rep))),
          _rep(this->internal_copy(rep)),
          _reps_computed(false),
          _right_mults(),
          _right_mults_inv(),
          _right_reps(),
          _tmp_element(this->internal_copy(rep)),
          _tmp_element2(this->internal_copy(rep)),
          _tmp_element3(this->internal_copy(rep)),
          _tmp_element4(this->internal_copy(rep)),
          _tmp_lambda_value(Lambda()(this->to_external_const(_rep))),
          _tmp_rho_value(Rho()(this->to_external_const(_rep))) {}

    virtual ~BaseDClass() {
      // the user of _internal_vec/_internal_set is responsible for freeing any
      // necessary elements
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

    // TODO(now): remove unused iterators / clean up

    const_reference rep() const noexcept {
      return this->to_external_const(_rep);
    }

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

    const_iterator cbegin_H_class_NC() const {
      return _H_class.cbegin();
    }

    const_iterator cend_H_class_NC() const {
      return _H_class.cend();
    }

    virtual bool contains(const_reference bm) = 0;

    bool contains(const_reference bm, size_t rank) {
      return (rank == _rank && contains(bm));
    }

    virtual size_t size() {
      init();
      return _H_class.size() * _left_reps.size() * _right_reps.size();
    }

    // TODO: this is dangerous and will fall over if multi-threaded
    // uses _tmp_element, tmp_element2 _tmp_element3
    std::vector<internal_element_type>& covering_reps() {
      init();
      _internal_vec.clear();
      // TODO: how to decide which side to calculate? One is often faster
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
              _internal_vec.push_back(this->internal_copy(_tmp_element3));
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
              _internal_vec.push_back(this->internal_copy(_tmp_element3));
            }
          }
        }
      }
      std::sort(_internal_vec.begin(), _internal_vec.end(), InternalLess());
      auto it = std::unique(_internal_vec.begin(), _internal_vec.end());
      _internal_vec.erase(it, _internal_vec.end());
      return _internal_vec;
    }

   protected:
    virtual void compute_left_mults()     = 0;
    virtual void compute_left_mults_inv() = 0;
    virtual void compute_left_reps()      = 0;

    virtual void compute_right_mults()     = 0;
    virtual void compute_right_mults_inv() = 0;
    virtual void compute_right_reps()      = 0;

    virtual void compute_H_class() = 0;

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
        ;
        LIBSEMIGROUPS_ASSERT(Rho()(this->to_external_const(_rep))
                             == Rho()(this->to_external(_tmp_element)));
      }
#endif
    }

    size_t left_reps_size() {
      return _left_reps.size();
    }

    size_t right_reps_size() {
      return _right_reps.size();
    }

    bool class_computed() const {
      return _class_computed;
    }

    bool mults_computed() const {
      return _mults_computed;
    }

    bool reps_computed() const {
      return _reps_computed;
    }

    bool H_class_computed() const {
      return _H_class_computed;
    }

    void set_class_computed(bool x) {
      _class_computed = x;
    }

    void set_mults_computed(bool x) {
      _mults_computed = x;
    }

    void set_reps_computed(bool x) {
      _reps_computed = x;
    }

    void set_H_class_computed(bool x) {
      _H_class_computed = x;
    }

    Konieczny* parent() const {
      return _parent;
    }

    // Watch out! Doesn't copy its argument
    void push_back_H_class(internal_element_type x) {
      _H_class.push_back(x);
    }

    virtual void init() = 0;

    lambda_value_type& tmp_lambda_value() {
      return _tmp_lambda_value;
    }

    rho_value_type& tmp_rho_value() {
      return _tmp_rho_value;
    }

    internal_element_type& tmp_element() {
      return _tmp_element;
    }

    internal_element_type& tmp_element2() {
      return _tmp_element2;
    }

    internal_element_type& tmp_element3() {
      return _tmp_element3;
    }

    internal_element_type& tmp_element4() {
      return _tmp_element4;
    }

    size_t size_H_class() const {
      return _H_class.size();
    }

    std::unordered_set<internal_element_type, InternalElementHash, InternalEqualTo>&
    internal_set() {
      return _internal_set;
    }

    std::vector<internal_element_type>& internal_vec() {
      return _internal_vec;
    }

   private:
    bool                               _class_computed;
    std::vector<internal_element_type> _H_class;
    bool                               _H_class_computed;
    std::unordered_set<internal_element_type, InternalElementHash, InternalEqualTo>
                                       _internal_set;
    std::vector<internal_element_type> _internal_vec;
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
    internal_element_type              _tmp_element;
    internal_element_type              _tmp_element2;
    internal_element_type              _tmp_element3;
    internal_element_type              _tmp_element4;
    lambda_value_type                  _tmp_lambda_value;
    rho_value_type                     _tmp_rho_value;
  };

  /////////////////////////////////////////////////////////////////////////////
  // RegularDClass
  /////////////////////////////////////////////////////////////////////////////

  template <typename TElementType, typename TTraits>
  class Konieczny<TElementType, TTraits>::RegularDClass
      : public Konieczny<TElementType, TTraits>::BaseDClass {
    using konieczny_type    = Konieczny<TElementType, TTraits>;
    using element_type      = konieczny_type::element_type;
    using lambda_value_type = konieczny_type::lambda_value_type;
    using rho_value_type    = konieczny_type::lambda_value_type;
    using EqualTo           = konieczny_type::EqualTo;

    using InternalElementHash = konieczny_type::InternalElementHash;
    using InternalEqualTo     = konieczny_type::InternalEqualTo;

    using lambda_orb_index_type = konieczny_type::lambda_orb_index_type;
    using rho_orb_index_type    = konieczny_type::rho_orb_index_type;

    using left_indices_index_type =
        typename konieczny_type::BaseDClass::left_indices_index_type;
    using right_indices_index_type =
        typename konieczny_type::BaseDClass::right_indices_index_type;

   public:
    RegularDClass(Konieczny* parent, internal_const_reference idem_rep)
        : Konieczny::BaseDClass(parent, idem_rep),
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
      Product()(this->to_external(this->tmp_element()),
                this->to_external_const(idem_rep),
                this->to_external_const(idem_rep));
      if (!EqualTo()(this->to_external(this->tmp_element()),
                     this->to_external_const(idem_rep))) {
        LIBSEMIGROUPS_EXCEPTION(
            "the representative given should be idempotent");
      }
    }

    virtual ~RegularDClass() {
      // _H_gens is contained in _H_class which is freed in ~BaseDClass
      InternalVecFree()(_left_idem_reps);
      InternalVecFree()(_right_idem_reps);
    }

    using const_index_iterator =
        typename std::vector<lambda_orb_index_type>::const_iterator;
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

    using const_internal_iterator =
        typename std::vector<internal_element_type>::const_iterator;

    const_internal_iterator cbegin_left_idem_reps() {
      init();
      return _left_idem_reps.cbegin();
    }

    const_internal_iterator cend_left_idem_reps() {
      init();
      return _left_idem_reps.cend();
    }

    const_internal_iterator cbegin_right_idem_reps() {
      init();
      return _right_idem_reps.cbegin();
    }

    const_internal_iterator cend_right_idem_reps() {
      init();
      return _right_idem_reps.cend();
    }

    // TODO: this is the wrong function! contains shouldn't assume argument is
    //        in semigroup!
    //! Tests whether an element \p bm of the semigroup is in this D class
    //!
    //! Watch out! The element \bm must be known to be in the semigroup for
    //! this to be valid!
    bool contains(const_reference bm) override {
      init();
      std::pair<lambda_orb_index_type, rho_orb_index_type> x
          = index_positions(bm);
      return x.first != UNDEFINED;
    }

    // Returns the indices of the L and R classes of \c this that \p bm is in,
    // unless bm is not in \c this, in which case returns the pair (UNDEFINED,
    // UNDEFINED)
    std::pair<lambda_orb_index_type, rho_orb_index_type>
    index_positions(const_reference bm) {
      init();
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

    size_t nr_idempotents() {
      init();
      size_t count = 0;
      for (auto it = cbegin_left_indices(); it < cend_left_indices(); ++it) {
        for (auto it2 = cbegin_right_indices(); it2 < cend_right_indices();
             ++it2) {
          if (this->parent->is_group_index(*it2, *it)) {
            count++;
          }
        }
      }
      LIBSEMIGROUPS_ASSERT(count > 0);
      return count;
    }

   private:
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
        if (this->parent()->_group_indices_alt.find(key)
            == this->parent()->_group_indices_alt.end()) {
          bool found = false;
          Product()(this->to_external(this->tmp_element()),
                    this->parent()->_rho_orb.multiplier_to_scc_root(rval_pos),
                    this->rep());
          Product()(
              this->to_external(this->tmp_element3()),
              this->rep(),
              this->parent()->_lambda_orb.multiplier_to_scc_root(lval_pos));

          for (auto it2
               = this->parent()->_rho_orb.digraph().cbegin_scc(rval_scc_id);
               !found
               && it2 < this->parent()->_rho_orb.digraph().cend_scc(
                            rval_scc_id);
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
              this->parent()->_group_indices_alt.emplace(key, *it2);
              found = true;
            }
          }
          if (!found) {
            this->parent()->_group_indices_alt.emplace(key, UNDEFINED);
          }
        }
        if (this->parent()->_group_indices_alt.at(key) != UNDEFINED) {
          _lambda_index_positions.emplace(*it, _left_indices.size());
          _left_indices.push_back(*it);
        }
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
        // TODO: will need two temporary elements for this product etc.

        Product()(this->to_external(this->tmp_element()),
                  this->parent()->_rho_orb.multiplier_from_scc_root(*it),
                  this->parent()->_rho_orb.multiplier_to_scc_root(rval_pos));

        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->rep());
        if (this->parent()->find_group_index(this->tmp_element2())
            != UNDEFINED) {
          _rho_index_positions.emplace(*it, _right_indices.size());
          _right_indices.push_back(*it);
        }
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
      _H_gens.clear();
      // TODO: remove these
      compute_left_indices();
      compute_right_indices();
      compute_mults();
      compute_reps();

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
        rho_orb_index_type       k = this->parent()->_group_indices_alt.at(key);
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

      // this all relies on the indices having been computed already

      // TODO: use information from the looping through the left indices in
      // the loop through the right indices
      for (size_t i = 0; i < _left_indices.size(); ++i) {
        auto               key = std::make_pair(rval_scc_id, _left_indices[i]);
        rho_orb_index_type k   = this->parent()->_group_indices_alt.at(key);
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
        _left_idem_reps.push_back(this->internal_copy(
            this->to_internal(konieczny_helpers::idem_in_H_class<element_type>(
                this->to_external(this->tmp_element2())))));
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
        _right_idem_reps.push_back(this->internal_copy(
            this->to_internal(konieczny_helpers::idem_in_H_class<element_type>(
                this->to_external(this->tmp_element2())))));
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

      for (size_t i = 0; i < this->size_H_class(); ++i) {
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

  template <typename TElementType, typename TTraits>
  class Konieczny<TElementType, TTraits>::NonRegularDClass
      : public Konieczny<TElementType, TTraits>::BaseDClass {
    using konieczny_type    = Konieczny<TElementType, TTraits>;
    using element_type      = konieczny_type::element_type;
    using lambda_value_type = konieczny_type::lambda_value_type;
    using rho_value_type    = konieczny_type::lambda_value_type;

    using lambda_orb_index_type = konieczny_type::lambda_orb_index_type;
    using rho_orb_index_type    = konieczny_type::rho_orb_index_type;

    using left_indices_index_type =
        typename konieczny_type::BaseDClass::left_indices_index_type;
    using right_indices_index_type =
        typename konieczny_type::BaseDClass::right_indices_index_type;

   public:
    NonRegularDClass(Konieczny* parent, internal_const_reference rep)
        : Konieczny::BaseDClass(parent, rep),
          _H_set(),
          _lambda_index_positions(),
          _left_idem_above(this->internal_copy(rep)),
          _left_idem_class(),
          _rho_index_positions(),
          _right_idem_above(this->internal_copy(rep)),
          _right_idem_class() {
      Product()(this->to_external(this->tmp_element()),
                this->to_external_const(rep),
                this->to_external_const(rep));
      if (EqualTo()(this->to_external(this->tmp_element()),
                    this->to_external_const(rep))) {
        LIBSEMIGROUPS_EXCEPTION("NonRegularDClass: the representative "
                                "given should not be idempotent");
      }
    }

    // NonRegularDClass doesn't need to free anything
    virtual ~NonRegularDClass() {}

    // uses _tmp_element, _tmp_element2
    // uses _tmp_lambda, _tmp_rho
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

    // TODO: this computes more than just the H class, and should be split
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

      static std::vector<internal_element_type> left_idem_H_class;
      static std::vector<internal_element_type> right_idem_H_class;

      left_idem_H_class.clear();
      right_idem_H_class.clear();

      for (auto it = _left_idem_class->cbegin_H_class();
           it < _left_idem_class->cend_H_class();
           it++) {
        // TODO: don't really need both tmps here, given we're copying it
        // anyway?
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(left_idem_right_mult),
                  this->to_external_const(*it));
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->to_external_const(left_idem_left_mult));
        left_idem_H_class.push_back(this->internal_copy(this->tmp_element2()));
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
        right_idem_H_class.push_back(this->internal_copy(this->tmp_element2()));
      }

      static std::vector<internal_element_type> left_idem_left_reps;
      static std::vector<internal_element_type> right_idem_right_reps;

      left_idem_left_reps.clear();
      right_idem_right_reps.clear();

      for (auto it = _left_idem_class->cbegin_left_mults();
           it < _left_idem_class->cend_left_mults();
           it++) {
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(left_idem_right_mult),
                  _left_idem_class->rep());
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->to_external_const(*it));
        left_idem_left_reps.push_back(
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
        right_idem_right_reps.push_back(
            this->internal_copy((this->tmp_element2())));
      }

      static std::vector<internal_element_type> Hex;
      static std::vector<internal_element_type> xHf;

      Hex.clear();
      xHf.clear();

      for (internal_const_reference s : left_idem_H_class) {
        Product()(this->to_external(this->tmp_element()),
                  this->rep(),
                  this->to_external_const(s));
        xHf.push_back(this->internal_copy(this->tmp_element()));
      }

      for (internal_const_reference t : right_idem_H_class) {
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
        this->internal_set().insert(*it);
      }
      Hex.clear();
      Hex.assign(this->internal_set().begin(), this->internal_set().end());

      this->internal_set().clear();
      for (auto it = xHf.begin(); it < xHf.end(); ++it) {
        this->internal_set().insert(*it);
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

      InternalVecFree()(left_idem_H_class);
      InternalVecFree()(right_idem_H_class);
      InternalVecFree()(left_idem_left_reps);
      InternalVecFree()(right_idem_right_reps);
      InternalVecFree()(xHf);
      InternalVecFree()(Hex);

      this->set_H_class_computed(true);
    }

    void compute_mults() {
      if (this->mults_computed()) {
        return;
      }

      // TODO: this data is the same as that computed in the compute_H_class
      // function, and should be reused from there.
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

      static std::vector<internal_element_type> left_idem_H_class;
      static std::vector<internal_element_type> right_idem_H_class;

      left_idem_H_class.clear();
      right_idem_H_class.clear();

      for (auto it = _left_idem_class->cbegin_H_class();
           it < _left_idem_class->cend_H_class();
           it++) {
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(left_idem_right_mult),
                  this->to_external_const(*it));
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->to_external_const(left_idem_left_mult));
        left_idem_H_class.push_back(this->internal_copy(this->tmp_element2()));
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
        right_idem_H_class.push_back(this->internal_copy(this->tmp_element2()));
      }

      static std::vector<internal_element_type> left_idem_left_reps;
      static std::vector<internal_element_type> right_idem_right_reps;

      left_idem_left_reps.clear();
      right_idem_right_reps.clear();

      for (auto it = _left_idem_class->cbegin_left_mults();
           it < _left_idem_class->cend_left_mults();
           it++) {
        Product()(this->to_external(this->tmp_element()),
                  this->to_external_const(left_idem_right_mult),
                  _left_idem_class->rep());
        Product()(this->to_external(this->tmp_element2()),
                  this->to_external(this->tmp_element()),
                  this->to_external_const(*it));
        left_idem_left_reps.push_back(
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
        right_idem_right_reps.push_back(
            this->internal_copy((this->tmp_element2())));
      }

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

      for (internal_const_reference h : left_idem_H_class) {

        static std::vector<internal_element_type> Hxh;
        Hxh.clear();

        for (auto it = this->cbegin_H_class(); it < this->cend_H_class();
             ++it) {
          Product()(this->to_external(this->tmp_element()),
                    this->to_external_const(*it),
                    this->to_external_const(h));
          Hxh.push_back(this->internal_copy(this->tmp_element()));
        }

        std::sort(Hxh.begin(), Hxh.end(), InternalLess());
        if (Hxh_set.find(Hxh) == Hxh_set.end()) {
          Hxh_set.insert(Hxh);
        } else {
          continue;
        }

        for (size_t i = 0; i < left_idem_left_reps.size(); ++i) {
          // TODO: enforce uniqueness here?
          static std::vector<internal_element_type> Hxhw;
          Hxhw.clear();

          for (auto it = Hxh.cbegin(); it < Hxh.cend(); ++it) {
            Product()(this->to_external(this->tmp_element()),
                      this->to_external_const(*it),
                      this->to_external_const(left_idem_left_reps[i]));
            Hxhw.push_back(this->internal_copy(this->tmp_element()));
          }

          std::sort(Hxhw.begin(), Hxhw.end(), InternalLess());
          if (Hxhw_set.find(Hxhw) == Hxhw_set.end()) {
            Hxhw_set.insert(std::move(Hxhw));

            Product()(this->to_external(this->tmp_element3()),
                      this->to_external_const(h),
                      this->to_external_const(left_idem_left_reps[i]));
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
            _lambda_index_positions[lpos].push_back(this->left_reps_size());

            // push_left_rep and push_left_mult use tmp_element and
            // tmp_element2
            this->push_left_rep(this->tmp_element4());
            this->push_left_mult(this->tmp_element3());

            Product()(this->to_external(this->tmp_element()),
                      this->to_external_const(left_idem_left_reps[i]),
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
          }
        }
        InternalVecFree()(Hxh);
      }

      for (auto it = Hxhw_set.begin(); it != Hxhw_set.end(); ++it) {
        InternalVecFree()(*it);
      }

      for (internal_const_reference h : right_idem_H_class) {
        static std::vector<internal_element_type> hHx;
        hHx.clear();

        for (auto it = this->cbegin_H_class(); it < this->cend_H_class();
             ++it) {
          Product()(this->to_external(this->tmp_element()),
                    this->to_external_const(h),
                    this->to_external_const(*it));
          hHx.push_back(this->internal_copy(this->tmp_element()));
        }

        std::sort(hHx.begin(), hHx.end(), InternalLess());
        if (hHx_set.find(hHx) == hHx_set.end()) {
          hHx_set.insert(hHx);
        } else {
          continue;
        }

        for (size_t i = 0; i < right_idem_right_reps.size(); ++i) {
          static std::vector<internal_element_type> zhHx;
          zhHx.clear();
          for (auto it = hHx.cbegin(); it < hHx.cend(); ++it) {
            Product()(this->to_external(this->tmp_element()),
                      this->to_external_const(right_idem_right_reps[i]),
                      this->to_external_const(*it));
            zhHx.push_back(this->internal_copy(this->tmp_element()));
          }

          std::sort(zhHx.begin(), zhHx.end(), InternalLess());
          if (zhHx_set.find(zhHx) == zhHx_set.end()) {
            zhHx_set.insert(std::move(zhHx));
            // push_right_rep and push_right_mult use tmp_element and
            // tmp_element2
            Product()(this->to_external(this->tmp_element3()),
                      this->to_external_const(right_idem_right_reps[i]),
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
            _rho_index_positions[rpos].push_back(this->right_reps_size());
            this->push_right_rep(this->tmp_element4());
            this->push_right_mult(this->tmp_element3());

            Product()(this->to_external(this->tmp_element()),
                      this->to_external_const(right_idem_right_mult),
                      this->to_external_const(
                          _right_idem_class->cbegin_right_mults_inv()[i]));
            Product()(this->to_external(this->tmp_element2()),
                      this->to_external(this->tmp_element()),
                      this->to_external_const(right_idem_right_reps[i]));

            this->parent()->group_inverse(
                this->tmp_element3(), _right_idem_above, h);
            this->parent()->group_inverse(
                this->tmp_element4(), _right_idem_above, this->tmp_element2());
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
          }
        }
        InternalVecFree()(hHx);
      }

      for (auto it = zhHx_set.begin(); it != zhHx_set.end(); ++it) {
        InternalVecFree()(*it);
      }
      /*
      InternalVecFree()(left_idem_H_class);
      InternalVecFree()(right_idem_H_class);
      */
      InternalVecFree()(left_idem_left_reps);
      InternalVecFree()(right_idem_right_reps);
      this->set_mults_computed(true);
    }

    // TODO(now) things will break if this function is called twice
    void construct_H_set() {
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

    std::unordered_set<internal_element_type,
                       InternalElementHash,
                       InternalEqualTo>
        _H_set;
    std::unordered_map<lambda_orb_index_type,
                       std::vector<left_indices_index_type>>
                          _lambda_index_positions;
    internal_element_type _left_idem_above;
    RegularDClass*        _left_idem_class;
    std::unordered_map<rho_orb_index_type,
                       std::vector<right_indices_index_type>>
                          _rho_index_positions;
    internal_element_type _right_idem_above;
    RegularDClass*        _right_idem_class;
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
  void Konieczny<TElementType, TTraits>::run_impl() {
    compute_orbs();

    // TODO: reserve?
    std::set<size_t> ranks;
    size_t           max_rank = 0;
    ranks.insert(0);

    RegularDClass* top = new RegularDClass(this, _one);
    add_D_class(top);
    for (internal_const_reference x : top->covering_reps()) {
      size_t rnk = Rank()(this->to_external_const(x));
      ranks.insert(rnk);
      if (is_regular_element(x)) {
        _reg_reps[rnk].emplace_back(this->internal_copy(x), 0);
      } else {
        _nonregular_reps[rnk].emplace_back(this->internal_copy(x), 0);
      }
    }
    std::vector<std::pair<internal_element_type, D_class_index_type>> next_reps;
    std::vector<std::pair<internal_element_type, D_class_index_type>> tmp_next;
    std::vector<std::pair<internal_element_type, D_class_index_type>> tmp;
    // TODO(now): use stopped
    while (*ranks.rbegin() > 0) {
      next_reps.clear();
      size_t reps_are_reg = false;
      max_rank            = *ranks.rbegin();
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
        for (size_t i = 0; i < _D_classes.size(); ++i) {
          if (_D_classes[i]->contains(this->to_external_const(it->first),
                                      max_rank)) {
            _D_rels[i].push_back(it->second);
            contained = true;
            break;
          }
        }
        if (!contained) {
          tmp_next.push_back(*it);
        }
      }
      next_reps = std::move(tmp_next);

      // TODO(now): use stopped
      while (!next_reps.empty()) {
        if (report()) {
          REPORT_DEFAULT("computed %d D classes, so far\n", _D_classes.size());
        }

        BaseDClass*                                          D;
        std::pair<internal_element_type, D_class_index_type> tup(
            this->internal_copy(_one), 0);

        if (reps_are_reg) {
          tup = next_reps.back();
          D   = new RegularDClass(this, this->find_idem(tup.first));
          add_D_class(static_cast<RegularDClass*>(D));
          this->internal_free(tup.first);
          for (internal_const_reference x : D->covering_reps()) {
            size_t rnk = Rank()(this->to_external_const(x));
            ranks.insert(rnk);
            if (is_regular_element(x)) {
              _reg_reps[rnk].emplace_back(this->internal_copy(x),
                                          _D_classes.size() - 1);
            } else {
              _nonregular_reps[rnk].emplace_back(this->internal_copy(x),
                                              _D_classes.size() - 1);
            }
          }
          next_reps.pop_back();

        } else {
          tup = next_reps.back();
          D   = new NonRegularDClass(this, tup.first);
          this->internal_free(tup.first);
          add_D_class(static_cast<NonRegularDClass*>(D));
          for (internal_const_reference x : D->covering_reps()) {
            size_t rnk = Rank()(this->to_external_const(x));
            ranks.insert(rnk);
            if (is_regular_element(x)) {
              _reg_reps[rnk].emplace_back(this->internal_copy(x),
                                          _D_classes.size() - 1);
            } else {
              _nonregular_reps[rnk].emplace_back(this->internal_copy(x),
                                              _D_classes.size() - 1);
            }
          }
          next_reps.pop_back();
        }

        tmp.clear();
        for (auto& x : next_reps) {
          if (D->contains(this->to_external_const(x.first))) {
            _D_rels[_D_classes.size() - 1].push_back(x.second);
          } else {
            tmp.push_back(std::move(x));
          }
        }
        next_reps = std::move(tmp);
      }
      LIBSEMIGROUPS_ASSERT(_reg_reps[max_rank].empty());
      if (_nonregular_reps[max_rank].empty()) {
        ranks.erase(max_rank);
        max_rank = *ranks.rbegin();
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
    _computed_all_classes = true;
  }
}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_INCLUDE_KONIECZNY_HPP_
