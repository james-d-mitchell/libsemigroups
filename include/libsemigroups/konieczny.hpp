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
    using element_type = TElementType;

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
    using LambdaHash  = ::libsemigroups::Hash<lambda_value_type>;
    using RhoHash     = ::libsemigroups::Hash<rho_value_type>;
  };

  template <typename TElementType,
            typename TTraits = KoniecznyTraits<TElementType>>
  class Konieczny : public Runner {
   public:
    using element_type    = typename TTraits::element_type;
    using const_reference = element_type const&;

    using lambda_value_type = typename TTraits::lambda_value_type;
    using rho_value_type    = typename TTraits::rho_value_type;

    using lambda_orb_type = typename TTraits::lambda_orb_type;
    using rho_orb_type    = typename TTraits::rho_orb_type;

    using Product     = typename TTraits::Product;
    using Lambda      = typename TTraits::Lambda;
    using Rho         = typename TTraits::Rho;
    using Rank        = typename TTraits::Rank;
    using One         = typename TTraits::One;
    using VecHash     = typename TTraits::VecHash;
    using ElementHash = typename TTraits::ElementHash;
    using LambdaHash  = typename TTraits::LambdaHash;
    using RhoHash     = typename TTraits::RhoHash;

    // TODO(now) replace with aliases into lambda_orb_type/rho_orb_type
    using rho_orb_index_type        = size_t;
    using rho_orb_scc_index_type    = size_t;
    using lambda_orb_index_type     = size_t;
    using lambda_orb_scc_index_type = size_t;
    using D_class_index_type        = size_t;

    explicit Konieczny(std::vector<element_type> const& gens)
        : _rho_orb(),
          _D_classes(),
          _D_rels(),
          _gens(gens),
          _group_indices(),
          _group_indices_alt(),
          _regular_D_classes(),
          _lambda_orb(),
          _adjoined_identity_contained(false),
          _computed_all_classes(false),
          _one(One()(_gens[0])),

          _tmp_lambda_value1(Lambda()(_one)),
          _tmp_lambda_value2(Lambda()(_one)),
          _tmp_rho_value1(Rho()(_one)),
          _tmp_rho_value2(Rho()(_one)),

          _tmp_element1(_one),
          _tmp_element2(_one),
          _tmp_element3(_one)

    {
      if (_gens.empty()) {
        LIBSEMIGROUPS_EXCEPTION(
            "expected a positive number of generators, but got 0");
      }
      // TODO: pointer badness

      _gens.push_back(_one);  // TODO: maybe not this
    }

    ~Konieczny();

    void run_impl() override;
    bool finished_impl() const override;

    //! Finds a group index of a H class in the R class of \p bm
    // modifies _tmp_element 1, _tmp_element2, _tmp_element3
    // modifies _tmp_lambda_value1
    // modifies _tmp_rho_value1
    lambda_orb_index_type find_group_index(const_reference bm) {
      Rho()(_tmp_rho_value1, bm);
      Lambda()(_tmp_lambda_value1, bm);
      lambda_orb_index_type     lpos = _lambda_orb.position(_tmp_lambda_value1);
      lambda_orb_scc_index_type lval_scc_id
          = _lambda_orb.digraph().scc_id(lpos);
      std::pair<rho_orb_index_type, lambda_orb_scc_index_type> key
          = std::make_pair(_rho_orb.position(_tmp_rho_value1), lval_scc_id);

      if (_group_indices.find(key) != _group_indices.end()) {
        return _group_indices.at(key);
      } else {
        // use _tmp_element2 since is_group_index modifies 1
        Product()(_tmp_element2, bm, _lambda_orb.multiplier_to_scc_root(lpos));
        for (auto it = _lambda_orb.digraph().cbegin_scc(lval_scc_id);
             it < _lambda_orb.digraph().cend_scc(lval_scc_id);
             it++) {
          Product()(_tmp_element3,
                    _tmp_element2,
                    _lambda_orb.multiplier_from_scc_root(*it));
          if (is_group_index(bm, _tmp_element3)) {
            _group_indices.emplace(key, *it);
            return *it;
          }
        }
      }
      _group_indices.emplace(key, UNDEFINED);
      return UNDEFINED;
    }

    bool is_regular_element(const_reference bm) {
      if (find_group_index(bm) != UNDEFINED) {
        return true;
      }
      return false;
    }

    // modifies _tmp_element1
    // modifies _tmp_lambda_value and _tmp_rho_value
    bool is_group_index(const_reference x, const_reference y) {
      Product()(_tmp_element1, y, x);
      Lambda()(_tmp_lambda_value1, _tmp_element1);
      Rho()(_tmp_rho_value1, _tmp_element1);
      Lambda()(_tmp_lambda_value2, x);
      Rho()(_tmp_rho_value2, y);
      return _tmp_lambda_value1 == _tmp_lambda_value2
             && _tmp_rho_value1 == _tmp_rho_value2;
    }

    //! Finds an idempotent in the D class of \c bm, if \c bm is regular
    // modifies _tmp_element1 and _tmp_element2
    // modifies _tmp_lambda_value1
    element_type find_idem(const_reference bm) {
      LIBSEMIGROUPS_ASSERT(Degree<element_type>()(bm)
                           == Degree<element_type>()(_tmp_element1));
      LIBSEMIGROUPS_ASSERT(Degree<element_type>()(bm)
                           == Degree<element_type>()(_tmp_element2));
      Product()(_tmp_element1, bm, bm);
      if (_tmp_element1 == bm) {
        return bm;
      }
      if (!is_regular_element(bm)) {
        // TODO: exception/assertion
      }
      lambda_orb_index_type i = find_group_index(bm);
      Lambda()(_tmp_lambda_value1, bm);
      lambda_orb_index_type pos = _lambda_orb.position(_tmp_lambda_value1);

      Product()(_tmp_element1, bm, _lambda_orb.multiplier_to_scc_root(pos));
      Product()(_tmp_element2,
                _tmp_element1,
                _lambda_orb.multiplier_from_scc_root(i));

      // BMat8(UNDEFINED) happens to be idempotent...
      return konieczny_helpers::idem_in_H_class<element_type>(_tmp_element2);
    }

    element_type group_inverse(const_reference id, const_reference bm) {
      _tmp_element1 = bm;
      do {
        _tmp_element2 = _tmp_element1;
        Product()(_tmp_element1, _tmp_element2, bm);
      } while (_tmp_element1 != id);
      return _tmp_element2;
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

      _lambda_orb.add_seed(Lambda()(_one));
      _rho_orb.add_seed(Rho()(_one));
      for (const_reference g : _gens) {
        _lambda_orb.add_generator(g);
        _rho_orb.add_generator(g);
      }
      _lambda_orb.run();
      _rho_orb.run();
      REPORT_DEFAULT("Found %llu lambda-values and %llu rho-values in %s\n",
                     _lambda_orb.size(),
                     _rho_orb.size(),
                     t.string());
    }

    typename std::vector<element_type>::const_iterator
    cbegin_generators() const {
      return _gens.cbegin();
    }

    typename std::vector<element_type>::const_iterator cend_generators() const {
      return _gens.cend();
    }

    rho_orb_type             _rho_orb;
    std::vector<BaseDClass*> _D_classes;
    // contains in _D_rels[i] the indices of the D classes which lie above
    // _D_classes[i]
    std::vector<std::vector<D_class_index_type>> _D_rels;
    std::vector<element_type>                    _gens;
    std::unordered_map<std::pair<rho_orb_index_type, lambda_orb_scc_index_type>,
                       lambda_orb_index_type,
                       PairHash>
        _group_indices;
    std::unordered_map<std::pair<rho_orb_scc_index_type, lambda_orb_index_type>,
                       rho_orb_index_type,
                       PairHash>
                                _group_indices_alt;
    element_type                _one;
    std::vector<RegularDClass*> _regular_D_classes;
    lambda_orb_type             _lambda_orb;
    bool                        _adjoined_identity_contained;
    bool                        _computed_all_classes;
    lambda_value_type           _tmp_lambda_value1;
    lambda_value_type           _tmp_lambda_value2;
    rho_value_type              _tmp_rho_value1;
    rho_value_type              _tmp_rho_value2;
    element_type                _tmp_element1;
    element_type                _tmp_element2;
    element_type                _tmp_element3;
  };

  /////////////////////////////////////////////////////////////////////////////
  // BaseDClass
  /////////////////////////////////////////////////////////////////////////////

  template <typename TElementType, typename TTraits>
  class Konieczny<TElementType, TTraits>::BaseDClass {
   public:
    using konieczny_type    = Konieczny<TElementType, TTraits>;
    using element_type      = konieczny_type::element_type;
    using Rank              = konieczny_type::Rank;
    using lambda_value_type = konieczny_type::lambda_value_type;

    using left_indices_index_type  = size_t;
    using right_indices_index_type = size_t;

   public:
    BaseDClass(Konieczny* parent, const_reference rep)
        : _rank(Rank()(rep)),
          _parent(parent),
          _rep(rep),
          _class_computed(false),
          _mults_computed(false),
          _reps_computed(false),
          _H_class_computed(false),
          _left_mults(),
          _left_mults_inv(),
          _right_mults(),
          _right_mults_inv(),
          _left_reps(),
          _right_reps(),
          _H_class(),
          _tmp_lambda_value(Lambda()(_rep)),
          _tmp_rho_value(Rho()(_rep)),
          _tmp_element(_rep),
          _tmp_element2(_rep),
          _tmp_element3(_rep),
          _tmp_element4(_rep)

    {}

    virtual ~BaseDClass() {}

    const_reference rep() const noexcept {
      return _rep;
    }

    using const_iterator = typename std::vector<element_type>::const_iterator;

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

    virtual bool contains(const_reference bm) = 0;

    bool contains(const_reference bm, size_t rank) {
      return (rank == _rank && contains(bm));
    }

    virtual size_t size() {
      init();
      return _H_class.size() * _left_reps.size() * _right_reps.size();
    }

    // uses _tmp_element, tmp_element2 _tmp_element3
    std::vector<element_type> covering_reps() {
      init();
      std::vector<element_type> out;
      // TODO: how to decide which side to calculate? One is often faster
      if (_parent->_lambda_orb.size() < _parent->_rho_orb.size()) {
        for (const_reference w : _left_reps) {
          for (auto it = _parent->cbegin_generators();
               it < _parent->cend_generators();
               ++it) {
            Product()(_tmp_element3, w, *it);
            // uses _tmp_element, _tmp_element2
            if (!contains(_tmp_element3)) {
              out.push_back(_tmp_element3);
            }
          }
        }
      } else {
        for (const_reference z : _right_reps) {
          for (auto it = _parent->cbegin_generators();
               it < _parent->cend_generators();
               ++it) {
            Product()(_tmp_element3, *it, z);
            // uses _tmp_element, _tmp_element2
            if (!contains(_tmp_element3)) {
              out.push_back(_tmp_element3);
            }
          }
        }
      }
      std::sort(out.begin(), out.end());
      auto it = std::unique(out.begin(), out.end());
      out.erase(it, out.end());
      return out;
    }

   protected:
    virtual void compute_left_mults()     = 0;
    virtual void compute_left_mults_inv() = 0;
    virtual void compute_left_reps()      = 0;

    virtual void compute_right_mults()     = 0;
    virtual void compute_right_mults_inv() = 0;
    virtual void compute_right_reps()      = 0;

    virtual void compute_H_class() = 0;

    // TODO: these will all copy the element
    // TODO: remove the *
    void push_left_mult(element_type x) {
      _left_mults.push_back(x);
#ifdef LIBSEMIGROUPS_DEBUG
      if (_left_reps.size() >= _left_mults.size()) {
        LIBSEMIGROUPS_ASSERT(Lambda()(_rep * x)
                             == Lambda()(_left_reps[_left_mults.size() - 1]));
      }
      if (_left_mults_inv.size() >= _left_mults.size()) {
        LIBSEMIGROUPS_ASSERT(
            Lambda()(_rep)
            == Lambda()(_rep * x * _left_mults_inv[_left_mults.size() - 1]));
      }
#endif
    }

    void push_left_mult_inv(element_type x) {
      _left_mults_inv.push_back(x);
#ifdef LIBSEMIGROUPS_DEBUG
      if (_left_reps.size() >= _left_mults_inv.size()) {
        LIBSEMIGROUPS_ASSERT(
            Lambda()(_rep) == Lambda()(_left_reps[_left_mults.size() - 1] * x));
      }
      if (_left_mults.size() >= _left_mults_inv.size()) {
        LIBSEMIGROUPS_ASSERT(
            Lambda()(_rep)
            == Lambda()(_rep * _left_mults[_left_mults_inv.size() - 1] * x));
      }
#endif
    }

    void push_right_mult(element_type x) {
      _right_mults.push_back(x);
#ifdef LIBSEMIGROUPS_DEBUG
      if (_right_reps.size() >= _right_mults.size()) {
        LIBSEMIGROUPS_ASSERT(Rho()(x * _rep)
                             == Rho()(_right_reps[_right_mults.size() - 1]));
      }
      if (_right_mults_inv.size() >= _right_mults.size()) {
        LIBSEMIGROUPS_ASSERT(
            Rho()(_rep)
            == Rho()(_right_mults_inv[_right_mults.size() - 1] * x * _rep));
      }
#endif
    }

    void push_right_mult_inv(element_type x) {
      _right_mults_inv.push_back(x);
#ifdef LIBSEMIGROUPS_DEBUG
      if (_right_reps.size() >= _right_mults_inv.size()) {
        LIBSEMIGROUPS_ASSERT(
            Rho()(_rep) == Rho()(x * _right_reps[_right_mults.size() - 1]));
      }
      if (_right_mults.size() >= _right_mults_inv.size()) {
        LIBSEMIGROUPS_ASSERT(
            Rho()(_rep)
            == Rho()(x * _right_mults[_right_mults_inv.size() - 1] * _rep));
      }
#endif
    }

    void push_left_rep(element_type x) {
      _left_reps.push_back(x);
#ifdef LIBSEMIGROUPS_DEBUG
      if (_left_mults.size() >= _left_reps.size()) {
        LIBSEMIGROUPS_ASSERT(Lambda()(_rep * _left_mults[_left_reps.size() - 1])
                             == Lambda()(x));
      }
      if (_left_mults_inv.size() >= _left_reps.size()) {
        LIBSEMIGROUPS_ASSERT(
            Lambda()(_rep)
            == Lambda()(x * _left_mults_inv[_left_reps.size() - 1]));
      }
#endif
    }

    void push_right_rep(element_type x) {
      _right_reps.push_back(x);
#ifdef LIBSEMIGROUPS_DEBUG
      if (_right_mults.size() >= _right_reps.size()) {
        LIBSEMIGROUPS_ASSERT(Rho()(_right_mults[_right_reps.size() - 1] * _rep)
                             == Rho()(x));
      }
      if (_right_mults_inv.size() >= _right_reps.size()) {
        LIBSEMIGROUPS_ASSERT(
            Rho()(_rep) == Rho()(_right_mults_inv[_right_reps.size() - 1] * x));
      }
#endif
    }

    void push_H_class_elm(element_type x) {
      _H_class.push_back(x);
      // TODO: sensible assertions here
    }

    std::back_insert_iterator<std::vector<element_type>> _H_back_inserter() {
      return std::back_inserter(_H_class);
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

    // TODO: Once again I have deeply confused myself with move semantics
    void set_H_class(std::vector<element_type>&& vec) {
      // TODO: assertions
      _H_class = vec;
    }

    virtual void init() = 0;

    lambda_value_type& tmp_lambda_value() {
      return _tmp_lambda_value;
    }

    rho_value_type& tmp_rho_value() {
      return _tmp_rho_value;
    }

    element_type& tmp_element() {
      return _tmp_element;
    }

    element_type& tmp_element2() {
      return _tmp_element2;
    }

    element_type& tmp_element3() {
      return _tmp_element3;
    }

    element_type& tmp_element4() {
      return _tmp_element4;
    }

   private:
    size_t                    _rank;
    Konieczny*                _parent;
    element_type              _rep;
    bool                      _class_computed;
    bool                      _mults_computed;
    bool                      _reps_computed;
    bool                      _H_class_computed;
    std::vector<element_type> _left_mults;
    std::vector<element_type> _left_mults_inv;
    std::vector<element_type> _right_mults;
    std::vector<element_type> _right_mults_inv;
    std::vector<element_type> _left_reps;
    std::vector<element_type> _right_reps;
    std::vector<element_type> _H_class;
    lambda_value_type         _tmp_lambda_value;
    rho_value_type            _tmp_rho_value;
    element_type              _tmp_element;
    element_type              _tmp_element2;
    element_type              _tmp_element3;
    element_type              _tmp_element4;
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
    using ElementHash       = konieczny_type::ElementHash;
    using LambdaHash        = konieczny_type::LambdaHash;
    using RhoHash           = konieczny_type::RhoHash;

    using lambda_orb_index_type = konieczny_type::lambda_orb_index_type;
    using rho_orb_index_type    = konieczny_type::rho_orb_index_type;

    using left_indices_index_type =
        typename konieczny_type::BaseDClass::left_indices_index_type;
    using right_indices_index_type =
        typename konieczny_type::BaseDClass::right_indices_index_type;

   public:
    RegularDClass(Konieczny* parent, const_reference idem_rep)
        : Konieczny::BaseDClass(parent, idem_rep),
          _rho_val_positions(),
          _H_gens(),
          _left_idem_reps(),
          _left_indices(),
          _right_idem_reps(),
          _right_indices(),
          _lambda_val_positions(),
          _H_gens_computed(false),
          _idem_reps_computed(false),
          _left_indices_computed(false),
          _right_indices_computed(false) {
      Product()(this->tmp_element(), idem_rep, idem_rep);
      if (this->tmp_element() != idem_rep) {
        LIBSEMIGROUPS_EXCEPTION(
            "the representative given should be idempotent");
      }
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

    using const_element_iterator =
        typename std::vector<element_type>::const_iterator;

    const_element_iterator cbegin_left_idem_reps() {
      init();
      return _left_idem_reps.cbegin();
    }

    const_element_iterator cend_left_idem_reps() {
      init();
      return _left_idem_reps.cend();
    }

    const_element_iterator cbegin_right_idem_reps() {
      init();
      return _right_idem_reps.cbegin();
    }

    const_element_iterator cend_right_idem_reps() {
      init();
      return _right_idem_reps.cend();
    }

    // TODO: this is the wrong function! contains shouldn't assume argument is
    //        in semigroup!
    //! Tests whether an element \p bm of the semigroup is in this D class
    //!
    //! Watch out! The element \bm must be known to be in the semigroup for this
    //! to be valid!
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
      auto l_it = _lambda_val_positions.find(this->tmp_lambda_value());
      if (l_it != _lambda_val_positions.end()) {
        Rho()(this->tmp_rho_value(), bm);
        auto r_it = _rho_val_positions.find(this->tmp_rho_value());
        if (r_it != _rho_val_positions.end()) {
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
      if (this->_left_indices_computed) {
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
          Product()(this->tmp_element(),
                    this->parent()->_rho_orb.multiplier_to_scc_root(rval_pos),
                    this->rep());
          Product()(
              this->tmp_element3(),
              this->rep(),
              this->parent()->_lambda_orb.multiplier_to_scc_root(lval_pos));

          for (auto it2
               = this->parent()->_rho_orb.digraph().cbegin_scc(rval_scc_id);
               !found
               && it2 < this->parent()->_rho_orb.digraph().cend_scc(
                            rval_scc_id);
               it2++) {
            Product()(this->tmp_element2(),
                      this->parent()->_rho_orb.multiplier_from_scc_root(*it2),
                      this->tmp_element());

            Product()(
                this->tmp_element4(),
                this->tmp_element3(),
                this->parent()->_lambda_orb.multiplier_from_scc_root(*it));

            if (this->parent()->is_group_index(this->tmp_element2(),
                                               this->tmp_element4())) {
              this->parent()->_group_indices_alt.emplace(key, *it2);
              found = true;
            }
          }
          if (!found) {
            this->parent()->_group_indices_alt.emplace(key, UNDEFINED);
          }
        }
        if (this->parent()->_group_indices_alt.at(key) != UNDEFINED) {
          _lambda_val_positions.emplace(this->parent()->_lambda_orb.at(*it),
                                        _left_indices.size());
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
      if (this->_right_indices_computed) {
        return;
      }
      this->_right_indices.clear();

      Rho()(this->tmp_rho_value(), this->rep());
      rho_orb_index_type rval_pos
          = this->parent()->_rho_orb.position(this->tmp_rho_value());
      rho_orb_scc_index_type rval_scc_id
          = this->parent()->_rho_orb.digraph().scc_id(rval_pos);
      for (auto it = this->parent()->_rho_orb.digraph().cbegin_scc(rval_scc_id);
           it < this->parent()->_rho_orb.digraph().cend_scc(rval_scc_id);
           it++) {
        // TODO: will need two temporary elements for this product etc.

        Product()(this->tmp_element(),
                  this->parent()->_rho_orb.multiplier_from_scc_root(*it),
                  this->parent()->_rho_orb.multiplier_to_scc_root(rval_pos));

        Product()(this->tmp_element2(), this->tmp_element(), this->rep());
        if (this->parent()->find_group_index(this->tmp_element2())
            != UNDEFINED) {
          _rho_val_positions.emplace(this->parent()->_rho_orb.at(*it),
                                     _right_indices.size());
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
        Product()(this->tmp_element(),
                  this->parent()->_lambda_orb.multiplier_to_scc_root(lval_pos),
                  this->parent()->_lambda_orb.multiplier_from_scc_root(idx));
        this->push_left_mult(this->tmp_element());
        Product()(
            this->tmp_element(),
            this->parent()->_lambda_orb.multiplier_to_scc_root(idx),
            this->parent()->_lambda_orb.multiplier_from_scc_root(lval_pos));
        this->push_left_mult_inv(this->tmp_element());
      }

      for (rho_orb_index_type idx : _right_indices) {
        Product()(this->tmp_element(),
                  this->parent()->_rho_orb.multiplier_from_scc_root(idx),
                  this->parent()->_rho_orb.multiplier_to_scc_root(rval_pos));
        this->push_right_mult(this->tmp_element());
        Product()(this->tmp_element(),
                  this->parent()->_rho_orb.multiplier_from_scc_root(rval_pos),
                  this->parent()->_rho_orb.multiplier_to_scc_root(idx));
        this->push_right_mult_inv(this->tmp_element());
      }
      this->set_mults_computed(true);
    }

    void compute_reps() {
      if (this->reps_computed()) {
        return;
      }

      compute_mults();

      // TODO: these (and everything else like them) should be const references
      // to avoid copying
      for (auto it = this->cbegin_left_mults(); it < this->cend_left_mults();
           ++it) {
        Product()(this->tmp_element(), this->rep(), *it);
        this->push_left_rep(this->tmp_element());
      }

      for (auto it = this->cbegin_right_mults(); it < this->cend_right_mults();
           ++it) {
        Product()(this->tmp_element(), *it, this->rep());
        this->push_right_rep(this->tmp_element());
      }
      this->set_reps_computed(true);
    }

    void compute_H_gens() {
      if (_H_gens_computed) {
        return;
      }
      _H_gens.clear();
      compute_left_indices();
      compute_right_indices();
      compute_mults();
      compute_reps();

      Rho()(this->tmp_rho_value(), this->rep());
      rho_value_type&        rval     = this->tmp_rho_value();
      rho_orb_index_type     rval_pos = this->parent()->_rho_orb.position(rval);
      rho_orb_scc_index_type rval_scc_id
          = this->parent()->_rho_orb.digraph().scc_id(rval_pos);
      std::vector<element_type> right_invs;

      for (size_t i = 0; i < _left_indices.size(); ++i) {
        std::pair<rho_orb_scc_index_type, lambda_orb_index_type> key
            = std::make_pair(rval_scc_id, _left_indices[i]);
        rho_orb_index_type       k = this->parent()->_group_indices_alt.at(key);
        right_indices_index_type j
            = _rho_val_positions.at(this->parent()->_rho_orb.at(k));

        // for p a left rep and q an appropriate right rep,
        // find the product of q with the inverse of pq in H_rep
        Product()(this->tmp_element(),
                  this->cbegin_left_reps()[i],
                  this->cbegin_right_reps()[j]);
        Product()(
            this->tmp_element2(),
            this->cbegin_right_reps()[j],
            this->parent()->group_inverse(this->rep(), this->tmp_element()));

        right_invs.push_back(this->tmp_element2());
      }

      for (size_t i = 0; i < _left_indices.size(); ++i) {
        for (const_reference g : this->parent()->_gens) {
          Product()(this->tmp_element(), this->cbegin_left_reps()[i], g);
          Lambda()(this->tmp_lambda_value(), this->tmp_element());
          for (size_t j = 0; j < _left_indices.size(); ++j) {
            if (this->parent()->_lambda_orb.at(_left_indices[j])
                == this->tmp_lambda_value()) {
              Product()(
                  this->tmp_element2(), this->tmp_element(), right_invs[j]);
              _H_gens.push_back(this->tmp_element2());
              break;
            }
          }
        }
      }
      std::unordered_set<element_type, ElementHash> set(_H_gens.begin(),
                                                        _H_gens.end());
      _H_gens.assign(set.begin(), set.end());
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
        Product()(
            this->tmp_element(), this->cbegin_right_mults()[j], this->rep());
        Product()(this->tmp_element2(),
                  this->tmp_element(),
                  this->cbegin_left_mults()[i]);
        _left_idem_reps.push_back(
            konieczny_helpers::idem_in_H_class<element_type>(
                this->tmp_element2()));
      }

      for (size_t j = 0; j < _right_indices.size(); ++j) {
        auto key = std::make_pair(_right_indices[j], lval_scc_id);
        lambda_orb_index_type k = this->parent()->_group_indices.at(key);
        size_t                i = 0;
        while (_left_indices[i] != k) {
          ++i;
        }
        Product()(
            this->tmp_element(), this->cbegin_right_mults()[j], this->rep());
        Product()(this->tmp_element2(),
                  this->tmp_element(),
                  this->cbegin_left_mults()[i]);
        _right_idem_reps.push_back(
            konieczny_helpers::idem_in_H_class<element_type>(
                this->tmp_element2()));
      }
      this->_idem_reps_computed = true;
    }

    // there should be some way of getting rid of this
    void compute_H_class() override {
      if (this->H_class_computed()) {
        return;
      }
      compute_H_gens();
      std::vector<element_type> vec(_H_gens.begin(), _H_gens.end());

      std::unordered_set<element_type, ElementHash> set(vec.begin(), vec.end());
      for (size_t i = 0; i < vec.size(); ++i) {
        for (const_reference g : _H_gens) {
          Product()(this->tmp_element(), vec[i], g);
          if (set.find(this->tmp_element()) == set.end()) {
            set.insert(this->tmp_element());
            vec.push_back(this->tmp_element());
          }
        }
      }
      this->set_H_class(std::move(vec));
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

    std::unordered_map<rho_value_type, right_indices_index_type, RhoHash>
                                       _rho_val_positions;
    std::vector<element_type>          _H_gens;
    std::vector<element_type>          _left_idem_reps;
    std::vector<lambda_orb_index_type> _left_indices;
    std::vector<element_type>          _right_idem_reps;
    std::vector<rho_orb_index_type>    _right_indices;
    std::unordered_map<lambda_value_type, left_indices_index_type, LambdaHash>
         _lambda_val_positions;
    bool _H_gens_computed;
    bool _idem_reps_computed;
    bool _left_indices_computed;
    bool _right_indices_computed;
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
    using VecHash           = konieczny_type::VecHash;
    using ElementHash       = konieczny_type::ElementHash;
    using LambdaHash        = konieczny_type::LambdaHash;
    using RhoHash           = konieczny_type::RhoHash;

    using lambda_orb_index_type = konieczny_type::lambda_orb_index_type;
    using rho_orb_index_type    = konieczny_type::rho_orb_index_type;

    using left_indices_index_type =
        typename konieczny_type::BaseDClass::left_indices_index_type;
    using right_indices_index_type =
        typename konieczny_type::BaseDClass::right_indices_index_type;

   public:
    NonRegularDClass(Konieczny* parent, element_type rep)
        : Konieczny::BaseDClass(parent, rep),
          _rho_val_positions(),
          _left_idem_above(rep),
          _left_idem_class(),
          _H_set(),
          _right_idem_above(rep),
          _right_idem_class(),
          _lambda_val_positions() {
      Product()(this->tmp_element(), rep, rep);
      if (this->tmp_element() == rep) {
        LIBSEMIGROUPS_EXCEPTION("NonRegularDClass: the representative "
                                "given should not be idempotent");
      }
    }

    // uses _tmp_element, _tmp_element2
    bool contains(const_reference bm) override {
      init();
      Lambda()(this->tmp_lambda_value(), bm);
      if (_lambda_val_positions[this->tmp_lambda_value()].size() == 0) {
        return false;
      }
      auto y = Rho()(bm);
      for (left_indices_index_type i :
           _lambda_val_positions[this->tmp_lambda_value()]) {
        Product()(this->tmp_element(), bm, this->cbegin_left_mults_inv()[i]);
        for (right_indices_index_type j : _rho_val_positions[y]) {
          Product()(this->tmp_element2(),
                    this->cbegin_right_mults_inv()[j],
                    this->tmp_element());
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
            Product()(this->tmp_element(), this->rep(), *idem_it);
            if (this->tmp_element() == this->rep()) {
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
            Product()(this->tmp_element(), *idem_it, this->rep());
            if (this->tmp_element() == this->rep()) {
              _right_idem_above = (*idem_it);
              _right_idem_class = D;
              right_found       = true;
              break;
            }
          }
        }
      }

#ifdef LIBSEMIGROUPS_DEBUG
      LIBSEMIGROUPS_ASSERT(_left_idem_class->contains(_left_idem_above));
      LIBSEMIGROUPS_ASSERT(_right_idem_class->contains(_right_idem_above));
      LIBSEMIGROUPS_ASSERT(left_found && right_found);
      LIBSEMIGROUPS_ASSERT(this->rep() * _left_idem_above == this->rep());
      LIBSEMIGROUPS_ASSERT(_right_idem_above * this->rep() == this->rep());
#endif
    }

    // TODO: this computes more than just the H class, and should be split
    void compute_H_class() override {
      if (this->H_class_computed()) {
        return;
      }
      std::pair<lambda_orb_index_type, rho_orb_index_type> left_idem_indices
          = _left_idem_class->index_positions(_left_idem_above);
      element_type left_idem_left_mult
          = _left_idem_class
                ->cbegin_left_mults()[std::get<0>(left_idem_indices)];
      element_type left_idem_right_mult
          = _left_idem_class
                ->cbegin_right_mults()[std::get<1>(left_idem_indices)];

      std::pair<lambda_orb_index_type, rho_orb_index_type> right_idem_indices
          = _right_idem_class->index_positions(_right_idem_above);
      element_type right_idem_left_mult
          = _right_idem_class
                ->cbegin_left_mults()[std::get<0>(right_idem_indices)];
      element_type right_idem_right_mult
          = _right_idem_class
                ->cbegin_right_mults()[std::get<1>(right_idem_indices)];

      std::vector<element_type> left_idem_H_class;
      std::vector<element_type> right_idem_H_class;

      for (auto it = _left_idem_class->cbegin_H_class();
           it < _left_idem_class->cend_H_class();
           it++) {
        // TODO: don't really need both tmps here, given we're copying it
        // anyway?
        Product()(this->tmp_element(), left_idem_right_mult, *it);
        Product()(
            this->tmp_element2(), this->tmp_element(), left_idem_left_mult);
        left_idem_H_class.push_back(this->tmp_element2());
      }

      for (auto it = _right_idem_class->cbegin_H_class();
           it < _right_idem_class->cend_H_class();
           it++) {
        Product()(this->tmp_element(), right_idem_right_mult, *it);
        Product()(
            this->tmp_element2(), this->tmp_element(), right_idem_left_mult);
        right_idem_H_class.push_back(this->tmp_element2());
      }

      std::vector<element_type> left_idem_left_reps;
      std::vector<element_type> right_idem_right_reps;

      for (auto it = _left_idem_class->cbegin_left_mults();
           it < _left_idem_class->cend_left_mults();
           it++) {
        Product()(
            this->tmp_element(), left_idem_right_mult, _left_idem_class->rep());
        Product()(this->tmp_element2(), this->tmp_element(), *it);
        left_idem_left_reps.push_back(this->tmp_element2());
      }

      for (auto it = _right_idem_class->cbegin_right_mults();
           it < _right_idem_class->cend_right_mults();
           it++) {
        Product()(this->tmp_element(), *it, _right_idem_class->rep());
        Product()(
            this->tmp_element2(), this->tmp_element(), right_idem_left_mult);
        right_idem_right_reps.push_back(this->tmp_element2());
      }

      std::vector<element_type> Hex;
      std::vector<element_type> xHf;

      for (const_reference s : left_idem_H_class) {
        Product()(this->tmp_element(), this->rep(), s);
        xHf.push_back(this->tmp_element());
      }

      for (const_reference t : right_idem_H_class) {
        Product()(this->tmp_element(), t, this->rep());
        Hex.push_back(this->tmp_element());
      }

      std::unordered_set<element_type, ElementHash> s(Hex.begin(), Hex.end());
      Hex.assign(s.begin(), s.end());

      s = std::unordered_set<element_type, ElementHash>(xHf.begin(), xHf.end());
      xHf.assign(s.begin(), s.end());

      std::sort(Hex.begin(), Hex.end());
      std::sort(xHf.begin(), xHf.end());

      std::set_intersection(Hex.begin(),
                            Hex.end(),
                            xHf.begin(),
                            xHf.end(),
                            this->_H_back_inserter());

      this->set_H_class_computed(true);
    }

    void compute_mults() {
      if (this->mults_computed()) {
        return;
      }

      // TODO: this data is the same as that computed in the compute_H_class
      // function, and should be reused from there.
      std::pair<lambda_orb_index_type, rho_orb_index_type> left_idem_indices
          = _left_idem_class->index_positions(_left_idem_above);
      element_type left_idem_left_mult
          = _left_idem_class
                ->cbegin_left_mults()[std::get<0>(left_idem_indices)];
      element_type left_idem_right_mult
          = _left_idem_class
                ->cbegin_right_mults()[std::get<1>(left_idem_indices)];

      std::pair<lambda_orb_index_type, rho_orb_index_type> right_idem_indices
          = _right_idem_class->index_positions(_right_idem_above);
      element_type right_idem_left_mult
          = _right_idem_class
                ->cbegin_left_mults()[std::get<0>(right_idem_indices)];
      element_type right_idem_right_mult
          = _right_idem_class
                ->cbegin_right_mults()[std::get<1>(right_idem_indices)];

      std::vector<element_type> left_idem_H_class;
      std::vector<element_type> right_idem_H_class;

      for (auto it = _left_idem_class->cbegin_H_class();
           it < _left_idem_class->cend_H_class();
           it++) {
        // TODO: don't really need both tmps here, given we're copying it
        // anyway?
        Product()(this->tmp_element(), left_idem_right_mult, *it);
        Product()(
            this->tmp_element2(), this->tmp_element(), left_idem_left_mult);
        left_idem_H_class.push_back(this->tmp_element2());
      }

      for (auto it = _right_idem_class->cbegin_H_class();
           it < _right_idem_class->cend_H_class();
           it++) {
        Product()(this->tmp_element(), right_idem_right_mult, *it);
        Product()(
            this->tmp_element2(), this->tmp_element(), right_idem_left_mult);
        right_idem_H_class.push_back(this->tmp_element2());
      }

      std::vector<element_type> left_idem_left_reps;
      std::vector<element_type> right_idem_right_reps;

      for (auto it = _left_idem_class->cbegin_left_mults();
           it < _left_idem_class->cend_left_mults();
           it++) {
        Product()(
            this->tmp_element(), left_idem_right_mult, _left_idem_class->rep());
        Product()(this->tmp_element2(), this->tmp_element(), *it);
        left_idem_left_reps.push_back(this->tmp_element2());
      }

      for (auto it = _right_idem_class->cbegin_right_mults();
           it < _right_idem_class->cend_right_mults();
           it++) {
        Product()(this->tmp_element(), *it, _right_idem_class->rep());
        Product()(
            this->tmp_element2(), this->tmp_element(), right_idem_left_mult);
        right_idem_right_reps.push_back(this->tmp_element2());
      }

      std::unordered_set<std::vector<element_type>, VecHash> Hxhw_set;
      std::unordered_set<std::vector<element_type>, VecHash> zhHx_set;

      for (const_reference h : left_idem_H_class) {
        for (size_t i = 0; i < left_idem_left_reps.size(); ++i) {
          // TODO: enforce uniqueness here?
          std::vector<element_type> Hxhw;

          for (auto it = this->cbegin_H_class(); it < this->cend_H_class();
               ++it) {
            Product()(this->tmp_element(), *it, h);
            Product()(this->tmp_element2(),
                      this->tmp_element(),
                      left_idem_left_reps[i]);

            Hxhw.push_back(this->tmp_element2());
          }

          std::sort(Hxhw.begin(), Hxhw.end());
          if (Hxhw_set.find(Hxhw) == Hxhw_set.end()) {
            Hxhw_set.insert(Hxhw);

            Product()(this->tmp_element(), h, left_idem_left_reps[i]);
            Product()(this->tmp_element2(), this->rep(), this->tmp_element());
            Lambda()(this->tmp_lambda_value(), this->tmp_element2());
            auto it = _lambda_val_positions.find(this->tmp_lambda_value());
            if (it == _lambda_val_positions.end()) {
              _lambda_val_positions.emplace(
                  this->tmp_lambda_value(),
                  std::vector<left_indices_index_type>());
            }
            _lambda_val_positions[this->tmp_lambda_value()].push_back(
                this->left_reps_size());
            this->push_left_rep(this->tmp_element2());
            this->push_left_mult(this->tmp_element());

            Product()(this->tmp_element(),
                      left_idem_left_reps[i],
                      _left_idem_class->cbegin_left_mults_inv()[i]);
            Product()(
                this->tmp_element2(), this->tmp_element(), left_idem_left_mult);
            Product()(this->tmp_element(),
                      this->parent()->group_inverse(_left_idem_above,
                                                    this->tmp_element2()),
                      this->parent()->group_inverse(_left_idem_above, h));

            Product()(this->tmp_element2(),
                      _left_idem_class->cbegin_left_mults_inv()[i],
                      left_idem_left_mult);
            Product()(this->tmp_element3(),
                      this->tmp_element2(),
                      this->tmp_element());
            this->push_left_mult_inv(this->tmp_element3());
          }
        }
      }

      for (const_reference h : right_idem_H_class) {
        for (size_t i = 0; i < right_idem_right_reps.size(); ++i) {
          element_type              z = right_idem_right_reps[i];
          std::vector<element_type> zhHx;
          for (auto it = this->cbegin_H_class(); it < this->cend_H_class();
               ++it) {
            Product()(this->tmp_element(), right_idem_right_reps[i], h);
            Product()(this->tmp_element2(), this->tmp_element(), *it);
            zhHx.push_back(this->tmp_element2());
          }

          std::sort(zhHx.begin(), zhHx.end());
          if (zhHx_set.find(zhHx) == zhHx_set.end()) {
            zhHx_set.insert(zhHx);

            Product()(this->tmp_element(), right_idem_right_reps[i], h);
            Product()(this->tmp_element2(), this->tmp_element(), this->rep());

            Rho()(this->tmp_rho_value(), this->tmp_element2());
            auto it = _rho_val_positions.find(this->tmp_rho_value());
            if (it == _rho_val_positions.end()) {
              _rho_val_positions.emplace(
                  this->tmp_rho_value(),
                  std::vector<right_indices_index_type>());
            }
            _rho_val_positions[this->tmp_rho_value()].push_back(
                this->right_reps_size());
            this->push_right_rep(this->tmp_element2());
            this->push_right_mult(this->tmp_element());

            Product()(this->tmp_element(),
                      right_idem_right_mult,
                      _right_idem_class->cbegin_right_mults_inv()[i]);
            Product()(this->tmp_element2(),
                      this->tmp_element(),
                      right_idem_right_reps[i]);
            Product()(this->tmp_element(),
                      this->parent()->group_inverse(_right_idem_above, h),
                      this->parent()->group_inverse(_right_idem_above,
                                                    this->tmp_element2()));
            Product()(this->tmp_element2(),
                      right_idem_right_mult,
                      _right_idem_class->cbegin_right_mults_inv()[i]);
            Product()(this->tmp_element3(),
                      this->tmp_element(),
                      this->tmp_element2());
            this->push_right_mult_inv(this->tmp_element3());
          }
        }
      }
      this->set_mults_computed(true);
    }

    // TODO: more copying... can this be avoided?
    void construct_H_set() {
      _H_set = std::unordered_set<element_type, ElementHash>(
          this->cbegin_H_class(), this->cend_H_class());
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

    std::unordered_map<rho_value_type,
                       std::vector<right_indices_index_type>,
                       RhoHash>
                                                  _rho_val_positions;
    element_type                                  _left_idem_above;
    RegularDClass*                                _left_idem_class;
    std::unordered_set<element_type, ElementHash> _H_set;
    element_type                                  _right_idem_above;
    RegularDClass*                                _right_idem_class;
    std::unordered_map<lambda_value_type,
                       std::vector<left_indices_index_type>,
                       LambdaHash>
        _lambda_val_positions;
  };

  template <typename TElementType, typename TTraits>
  Konieczny<TElementType, TTraits>::~Konieczny() {
    for (BaseDClass* D : _D_classes) {
      delete D;
    }
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

    std::vector<std::vector<std::pair<element_type, D_class_index_type>>>
        reg_reps(Rank()(_one) + 1,
                 std::vector<std::pair<element_type, D_class_index_type>>());
    std::vector<std::vector<std::pair<element_type, D_class_index_type>>>
        non_reg_reps(
            Rank()(_one) + 1,
            std::vector<std::pair<element_type, D_class_index_type>>());
    // TODO: reserve?
    std::set<size_t> ranks;
    size_t           max_rank = 0;
    ranks.insert(0);

    RegularDClass* top = new RegularDClass(this, _one);
    add_D_class(top);
    for (element_type x : top->covering_reps()) {
      size_t rank = Rank()(x);
      ranks.insert(rank);
      if (is_regular_element(x)) {
        reg_reps[rank].push_back(std::make_pair(x, 0));
      } else {
        non_reg_reps[rank].push_back(std::make_pair(x, 0));
      }
    }

    while (*ranks.rbegin() > 0 && !stopped()) {
      size_t reps_are_reg = false;
      std::vector<std::pair<element_type, D_class_index_type>> next_reps;

      max_rank = *ranks.rbegin();
      if (!reg_reps[max_rank].empty()) {
        reps_are_reg = true;
        next_reps    = std::move(reg_reps[max_rank]);
        reg_reps[max_rank].clear();
      } else {
        next_reps = std::move(non_reg_reps[max_rank]);
        non_reg_reps[max_rank].clear();
      }

      std::vector<std::pair<element_type, D_class_index_type>> tmp_next;
      for (auto it = next_reps.begin(); it < next_reps.end(); it++) {
        bool contained = false;
        for (size_t i = 0; i < _D_classes.size(); ++i) {
          if (_D_classes[i]->contains(std::get<0>(*it), max_rank)) {
            _D_rels[i].push_back(std::get<1>(*it));
            contained = true;
            break;
          }
        }
        if (!contained) {
          tmp_next.push_back(*it);
        }
      }
      next_reps = std::move(tmp_next);

      while (!next_reps.empty() && !stopped()) {
        if (report()) {
          REPORT_DEFAULT("computed %d D classes, so far\n", _D_classes.size());
        }

        BaseDClass*                                  D;
        std::tuple<element_type, D_class_index_type> tup(_one, 0);

        if (reps_are_reg) {
          tup = next_reps.back();
          D   = new RegularDClass(this, find_idem(std::get<0>(tup)));
          add_D_class(static_cast<RegularDClass*>(D));
          for (const_reference x : D->covering_reps()) {
            size_t rank = Rank()(x);
            ranks.insert(rank);
            if (is_regular_element(x)) {
              reg_reps[rank].push_back(
                  std::make_pair(x, _D_classes.size() - 1));
            } else {
              non_reg_reps[rank].push_back(
                  std::make_pair(x, _D_classes.size() - 1));
            }
          }
          next_reps.pop_back();

        } else {
          tup = next_reps.back();
          D   = new NonRegularDClass(this, std::get<0>(tup));
          add_D_class(static_cast<NonRegularDClass*>(D));
          for (const_reference x : D->covering_reps()) {
            size_t rank = Rank()(x);
            ranks.insert(rank);
            if (is_regular_element(x)) {
              reg_reps[rank].push_back(
                  std::make_pair(x, _D_classes.size() - 1));
            } else {
              non_reg_reps[rank].push_back(
                  std::make_pair(x, _D_classes.size() - 1));
            }
          }
          next_reps.pop_back();
        }

        std::vector<std::pair<element_type, D_class_index_type>> tmp;
        for (std::pair<element_type, D_class_index_type>& x : next_reps) {
          if (D->contains(std::get<0>(x))) {
            _D_rels[_D_classes.size() - 1].push_back(x.second);
          } else {
            tmp.push_back(std::move(x));
          }
        }
        next_reps = std::move(tmp);
      }
      LIBSEMIGROUPS_ASSERT(reg_reps[max_rank].empty());
      if (non_reg_reps[max_rank].empty()) {
        ranks.erase(max_rank);
        max_rank = *ranks.rbegin();
      }
    }

    // Set whether the adjoined one is in the semigroup or not
    // i.e. whether the generators contain multiple elements in the top D class
    bool flag = false;
    for (element_type x : _gens) {
      if (_D_classes[0]->contains(x)) {
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
