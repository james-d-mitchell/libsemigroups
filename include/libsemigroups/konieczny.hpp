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

// TODO: exception safety!

#ifndef LIBSEMIGROUPS_INCLUDE_KONIECZNY_HPP_
#define LIBSEMIGROUPS_INCLUDE_KONIECZNY_HPP_

#include <algorithm>
#include <map>
#include <set>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "action.hpp"
#include "bmat8.hpp"
#include "constants.hpp"
#include "digraph.hpp"
#include "element.hpp"
#include "schreier-sims.hpp"

namespace libsemigroups {

  namespace konieczny_helpers {
    template <typename TElementType>
    bool is_group_index(TElementType const& x, TElementType const& y) {
      LIBSEMIGROUPS_ASSERT(Rho<TElementType>()(x) == x
                           && Lambda<TElementType>()(y) == y);
      return Lambda<TElementType>()(y * x) == Lambda<TElementType>()(x)
             && Rho<TElementType>()(y * x) == Rho<TElementType>()(y);
    }

  }  // namespace konieczny_helpers

  // TODO improve
  template <typename TElementType>
  TElementType group_inverse(TElementType id, TElementType bm) {
    TElementType tmp = bm;
    TElementType y;
    do {
      y   = tmp;
      tmp = bm * y;
    } while (tmp != id);
    return y;
  }

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
    using lambda_orb_type
        = RightAction<BMat8, BMat8, ImageRightAction<BMat8, BMat8>>;
    using rho_orb_type
        = LeftAction<BMat8, BMat8, ImageLeftAction<BMat8, BMat8>>;

    using Product = ::libsemigroups::Product<element_type>;
    using Lambda  = ::libsemigroups::Lambda<element_type>;
    using Rho     = ::libsemigroups::Rho<element_type>;
    using Rank    = ::libsemigroups::Rank<element_type>;
    using One     = ::libsemigroups::One<element_type>;
  };

  template <typename TElementType,
            typename TTraits = KoniecznyTraits<TElementType>>
  class Konieczny { // TODO subclass runner
   public:
    using element_type    = typename TTraits::element_type;
    using const_reference = element_type const&;

    using lambda_orb_type = typename TTraits::lambda_orb_type;
    using rho_orb_type    = typename TTraits::rho_orb_type;

    using Product = typename TTraits::Product;
    using Lambda  = typename TTraits::Lambda;
    using Rho     = typename TTraits::Rho;
    using Rank    = typename TTraits::Rank;
    using One    = typename TTraits::One;

    using lambda_value_type =
        typename std::result_of<Lambda(element_type)>::type;
    using rho_value_type = typename std::result_of<Rho(element_type)>::type;

    explicit Konieczny(std::vector<element_type> const& gens)
        : _rho_orb(),
          _D_classes(),
          _D_rels(),
          _dim(1),
          _gens(gens),
          _group_indices(),
          _group_indices_alt(),
          _regular_D_classes(),
          _lambda_orb() {}

    ~Konieczny();

    //! Finds a group index of a H class in the R class of \p bm
    size_t find_group_index(element_type const& bm) {
      rho_value_type            rv  = Rho()(bm);
      size_t                    pos = _lambda_orb.position(Lambda()(bm));
      size_t                    lval_scc_id = _lambda_orb.digraph().scc_id(pos);
      std::pair<size_t, size_t> key         = std::make_pair(
          ToInt<rho_value_type>()(rv), _lambda_orb.digraph().scc_id(pos));

      if (_group_indices.find(key) != _group_indices.end()) {
        return _group_indices.at(key);
      } else {
        for (auto it = _lambda_orb.digraph().cbegin_scc(lval_scc_id);
             it < _lambda_orb.digraph().cend_scc(lval_scc_id);
             it++) {
          if (konieczny_helpers::is_group_index(rv, _lambda_orb.at(*it))) {
            _group_indices.emplace(key, *it);
            return *it;
          }
        }
      }
      _group_indices.emplace(key, UNDEFINED);
      return UNDEFINED;
    }

    bool is_regular_element(element_type const& bm) {
      if (find_group_index(bm) != UNDEFINED) {
        return true;
      }
      return false;
    }

    // TODO: it must be possible to do better than this
    element_type idem_in_H_class(element_type const& bm) {
      element_type tmp = bm;
      while (tmp * tmp != tmp) {
        tmp = tmp * bm;
      }
      return tmp;
    }

    //! Finds an idempotent in the D class of \c bm, if \c bm is regular
    element_type find_idem(element_type const& bm) {
      if (bm * bm == bm) {
        return bm;
      }
      if (!is_regular_element(bm)) {
        // TODO: exception/assertion
      }
      size_t       i   = find_group_index(bm);
      size_t       pos = _lambda_orb.position(Lambda()(bm));
      element_type x   = bm * _lambda_orb.multiplier_to_scc_root(pos)
                       * _lambda_orb.multiplier_from_scc_root(i);
      // BMat8(UNDEFINED) happens to be idempotent...
      return idem_in_H_class(x);
    }

    class BaseDClass;
    class RegularDClass;
    class NonRegularDClass;

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

    //! Adds the identity element_type (of degree max of the degrees of the
    //! generators) if there is no permutation already in the generators, and
    //! sets the value of \c _unit_in_gens.
    void conditional_add_identity() {
     // _gens.push_back(One()(_gens[0]));
    }

    void compute_orbs() {
      detail::Timer t;
      REPORT_DEFAULT("Computing orbits . . .\n");
      _lambda_orb.add_seed(One()(_gens[0]));
      _rho_orb.add_seed(One()(_gens[0]));
      for (element_type g : _gens) {
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

    void compute_D_classes();

    rho_orb_type             _rho_orb;
    std::vector<BaseDClass*> _D_classes;
    // contains in _D_rels[i] the indices of the D classes which lie above
    // _D_classes[i]
    std::vector<std::vector<size_t>> _D_rels;
    size_t                           _dim;
    std::vector<element_type>        _gens;
    std::unordered_map<std::pair<size_t, size_t>, size_t, PairHash>
        _group_indices;
    std::unordered_map<std::pair<size_t, size_t>, size_t, PairHash>
                                _group_indices_alt;
    std::vector<RegularDClass*> _regular_D_classes;
    lambda_orb_type             _lambda_orb;
  };

  template <typename TElementType, typename TTraits>
  class Konieczny<TElementType, TTraits>::BaseDClass {
    friend class Konieczny<TElementType, TTraits>;
    using element_type = TElementType;
    using Rank         = Konieczny<TElementType, TTraits>::Rank;

   public:
    BaseDClass(Konieczny* parent, element_type rep)
        : _rank(Rank()(rep)),
          _computed(false),
          _H_class(),
          _left_mults(),
          _left_mults_inv(),
          _left_reps(),
          _parent(parent),
          _rep(rep),
          _right_mults(),
          _right_mults_inv(),
          _right_reps() {}

    virtual ~BaseDClass() {}

    element_type rep() const {
      return _rep;
    }

    using const_iterator = typename std::vector<element_type>::const_iterator;

    const_iterator cbegin_left_reps() {
      init();
      return _left_reps.cbegin();
    }

    const_iterator cend_left_reps() {
      init();
      return _left_reps.cend();
    }

    const_iterator cbegin_right_reps() {
      init();
      return _right_reps.cbegin();
    }

    const_iterator cend_right_reps() {
      init();
      return _right_reps.cend();
    }

    const_iterator cbegin_left_mults() {
      init();
      return _left_mults.cbegin();
    }

    const_iterator cend_left_mults() {
      init();
      return _left_mults.cend();
    }

    const_iterator cbegin_left_mults_inv() {
      init();
      return _left_mults_inv.cbegin();
    }

    const_iterator cend_left_mults_inv() {
      init();
      return _left_mults_inv.cend();
    }

    const_iterator cbegin_right_mults() {
      init();
      return _right_mults.cbegin();
    }

    const_iterator cend_right_mults() {
      init();
      return _right_mults.cend();
    }

    const_iterator cbegin_right_mults_inv() {
      init();
      return _right_mults_inv.cbegin();
    }

    const_iterator cend_right_mults_inv() {
      init();
      return _right_mults_inv.cend();
    }

    const_iterator cbegin_H_class() {
      init();
      return _H_class.cbegin();
    }

    const_iterator cend_H_class() {
      init();
      return _H_class.cend();
    }

    virtual bool contains(element_type bm) = 0;

    bool contains(element_type bm, size_t rank) {
      return (rank == _rank && contains(bm));
    }

    virtual size_t size() {
      init();
      return _H_class.size() * _left_reps.size() * _right_reps.size();
    }

    std::vector<element_type> covering_reps() {
      init();
      std::vector<element_type> out;
      // TODO: how to decide which side to calculate? One is often faster
      if (_parent->_lambda_orb.size() < _parent->_rho_orb.size()) {
        for (element_type w : _left_reps) {
          for (element_type g : _parent->_gens) {
            element_type x = w * g;
            if (!contains(x)) {
              out.push_back(x);
            }
          }
        }
      } else {
        for (element_type z : _right_reps) {
          for (element_type g : _parent->_gens) {
            element_type x = g * z;
            if (!contains(x)) {
              out.push_back(x);
            }
          }
        }
      }
      std::sort(out.begin(), out.end());
      auto it = std::unique(out.begin(), out.end());
      out.erase(it, out.end());
      return out;
    }

    // TODO(FLS): protected -> private
   protected:
    virtual void init() = 0;

    // TODO(FLS): member functions providing access to these
    size_t                    _rank;
    bool                      _computed;
    std::vector<element_type> _H_class;
    std::vector<element_type> _left_mults;
    std::vector<element_type> _left_mults_inv;
    std::vector<element_type> _left_reps;
    Konieczny*                _parent;
    element_type              _rep;
    std::vector<element_type> _right_mults;
    std::vector<element_type> _right_mults_inv;
    std::vector<element_type> _right_reps;
  };

  template <typename TElementType, typename TTraits>
  class Konieczny<TElementType, TTraits>::RegularDClass
      : public Konieczny<TElementType, TTraits>::BaseDClass {
    using element_type = TElementType;

   public:
    RegularDClass(Konieczny* parent, element_type idem_rep)
        : Konieczny::BaseDClass(parent, idem_rep),
          _rho_val_positions(),
          _H_gens(),
          _left_idem_reps(),
          _left_indices(),
          _right_idem_reps(),
          _right_indices(),
          _lambda_val_positions(),
          _stab_chain() {
      if (idem_rep * idem_rep != idem_rep) {
        LIBSEMIGROUPS_EXCEPTION(
            "RegularDClass: the representative given should be idempotent");
      }
    }

    using const_index_iterator = typename std::vector<size_t>::const_iterator;
    const_index_iterator cbegin_left_indices() {
      init();
      return _left_indices.cbegin();
    }

    const_index_iterator cend_left_indices() {
      init();
      return _left_indices.cend();
    }

    const_index_iterator cbegin_right_indices() {
      init();
      return _right_indices.cbegin();
    }

    const_index_iterator cend_right_indices() {
      init();
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

    /*
    SchreierSims<8, uint8_t, Permutation<uint8_t>> stab_chain() {
      init();
      return _stab_chain;
    }
    */

    // TODO: this is the wrong function! contains shouldn't assume argument is
    //        in semigroup!
    //! Tests whether an element \p bm of the semigroup is in this D class
    //!
    //! Watch out! The element \bm must be known to be in the semigroup for this
    //! to be valid!
    bool contains(element_type bm) override {
      init();
      std::pair<size_t, size_t> x = index_positions(bm);
      return x.first != UNDEFINED;
    }

    // Returns the indices of the L and R classes of \c this that \p bm is in,
    // unless bm is not in \c this, in which case returns the pair (UNDEFINED,
    // UNDEFINED)
    std::pair<size_t, size_t> index_positions(element_type bm) {
      init();
      auto l_it = _lambda_val_positions.find(
          ToInt<lambda_value_type>()(Lambda()(bm)));
      if (l_it != _lambda_val_positions.end()) {
        auto r_it = _rho_val_positions.find(ToInt<rho_value_type>()(Rho()(bm)));
        if (r_it != _rho_val_positions.end()) {
          return std::make_pair((*l_it).second, (*r_it).second);
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
          if (konieczny_helpers::is_group_index(
                  this->_parent->_rho_orb.at(*it2),
                  this->_parent->_lambda_orb.at(*it))) {
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
      if (_left_indices.size() > 0) {
        return;
      }
      size_t lval_pos
          = this->_parent->_lambda_orb.position(Lambda()(this->_rep));
      size_t rval_pos = this->_parent->_rho_orb.position(Rho()(this->_rep));
      size_t lval_scc_id
          = this->_parent->_lambda_orb.digraph().scc_id(lval_pos);
      size_t rval_scc_id = this->_parent->_rho_orb.digraph().scc_id(rval_pos);

      std::pair<size_t, size_t> key = std::make_pair(rval_scc_id, 0);
      for (auto it
           = this->_parent->_lambda_orb.digraph().cbegin_scc(lval_scc_id);
           it < this->_parent->_lambda_orb.digraph().cend_scc(lval_scc_id);
           it++) {
        std::get<1>(key) = *it;
        if (this->_parent->_group_indices_alt.find(key)
            == this->_parent->_group_indices_alt.end()) {
          bool found = false;
          for (auto it2
               = this->_parent->_rho_orb.digraph().cbegin_scc(rval_scc_id);
               !found
               && it2 < this->_parent->_rho_orb.digraph().cend_scc(rval_scc_id);
               it2++) {
            if (konieczny_helpers::is_group_index(
                    this->_parent->_rho_orb.at(*it2),
                    this->_parent->_lambda_orb.at(*it))) {
              this->_parent->_group_indices_alt.emplace(key, *it2);
              found = true;
            }
          }
          if (!found) {
            this->_parent->_group_indices_alt.emplace(key, UNDEFINED);
          }
        }
        if (this->_parent->_group_indices_alt.at(key) != UNDEFINED) {
          _lambda_val_positions.emplace(
              ToInt<lambda_value_type>()(this->_parent->_lambda_orb.at(*it)),
              _left_indices.size());
          _left_indices.push_back(*it);
        }
      }
#ifdef LIBSEMIGROUPS_DEBUG
      for (size_t i : _left_indices) {
        LIBSEMIGROUPS_ASSERT(i < this->_parent->_lambda_orb.size());
      }
#endif
    }

    void compute_right_indices() {
      if (_right_indices.size() > 0) {
        return;
      }
      size_t rval_pos    = this->_parent->_rho_orb.position(Rho()(this->_rep));
      size_t rval_scc_id = this->_parent->_rho_orb.digraph().scc_id(rval_pos);
      for (auto it = this->_parent->_rho_orb.digraph().cbegin_scc(rval_scc_id);
           it < this->_parent->_rho_orb.digraph().cend_scc(rval_scc_id);
           it++) {
        element_type x
            = this->_parent->_rho_orb.multiplier_from_scc_root(*it)
              * this->_parent->_rho_orb.multiplier_to_scc_root(rval_pos)
              * this->_rep;
        if (this->_parent->find_group_index(x) != UNDEFINED) {
          _rho_val_positions.emplace(
              ToInt<rho_value_type>()(this->_parent->_rho_orb.at(*it)),
              _right_indices.size());
          _right_indices.push_back(*it);
        }
      }
#ifdef LIBSEMIGROUPS_DEBUG
      for (size_t i : _right_indices) {
        LIBSEMIGROUPS_ASSERT(i < this->_parent->_rho_orb.size());
      }
#endif
    }

    void compute_mults() {
      if (this->_left_mults.size() > 0) {
        return;
      }
      element_type lval     = Lambda()(this->_rep);
      size_t       lval_pos = this->_parent->_lambda_orb.position(lval);
      element_type rval     = Rho()(this->_rep);
      size_t       rval_pos = this->_parent->_rho_orb.position(rval);

      for (size_t i = 0; i < _left_indices.size(); ++i) {
        element_type b
            = this->_parent->_lambda_orb.multiplier_to_scc_root(lval_pos)
              * this->_parent->_lambda_orb.multiplier_from_scc_root(
                  _left_indices[i]);
        element_type c
            = this->_parent->_lambda_orb.multiplier_to_scc_root(
                  _left_indices[i])
              * this->_parent->_lambda_orb.multiplier_from_scc_root(lval_pos);

        this->_left_mults.push_back(b);
        this->_left_mults_inv.push_back(c);
      }

      for (size_t i = 0; i < _right_indices.size(); ++i) {
        element_type c
            = this->_parent->_rho_orb.multiplier_from_scc_root(
                  _right_indices[i])
              * this->_parent->_rho_orb.multiplier_to_scc_root(rval_pos);
        element_type d
            = this->_parent->_rho_orb.multiplier_from_scc_root(rval_pos)
              * this->_parent->_rho_orb.multiplier_to_scc_root(
                  _right_indices[i]);

        this->_right_mults.push_back(c);
        this->_right_mults_inv.push_back(d);
      }
    }

    void compute_reps() {
      compute_mults();

      this->_left_reps.clear();
      this->_right_reps.clear();

      for (element_type b : this->_left_mults) {
        this->_left_reps.push_back(this->_rep * b);
      }

      for (element_type c : this->_right_mults) {
        this->_right_reps.push_back(c * this->_rep);
      }
    }

    void compute_H_gens() {
      _H_gens.clear();
      element_type rval     = Rho()(this->_rep);
      size_t       rval_pos = this->_parent->_rho_orb.position(rval);
      size_t rval_scc_id = this->_parent->_rho_orb.digraph().scc_id(rval_pos);
      std::vector<element_type> right_invs;

      for (size_t i = 0; i < _left_indices.size(); ++i) {
        element_type              p = this->_left_reps[i];
        std::pair<size_t, size_t> key
            = std::make_pair(rval_scc_id, _left_indices[i]);

        size_t k = this->_parent->_group_indices_alt.at(key);
        size_t j = _rho_val_positions.at(
            ToInt<rho_value_type>()(this->_parent->_rho_orb.at(k)));
        element_type q = this->_right_reps[j];
        // find the inverse of pq in H_rep
        element_type y = group_inverse<element_type>(this->_rep, p * q);
        right_invs.push_back(q * y);
      }

      for (size_t i = 0; i < _left_indices.size(); ++i) {
        element_type p = this->_left_reps[i];
        for (element_type g : this->_parent->_gens) {
          element_type x = p * g;
          element_type s = Lambda()(x);
          for (size_t j = 0; j < _left_indices.size(); ++j) {
            if (this->_parent->_lambda_orb.at(_left_indices[j]) == s) {
              _H_gens.push_back(x * right_invs[j]);
              break;
            }
          }
        }
      }
      std::unordered_set<element_type> set(_H_gens.begin(), _H_gens.end());
      _H_gens.assign(set.begin(), set.end());
    }

    /*
    void compute_stab_chain() {
      BMat8 row_basis = Lambda()(this->_rep);
      for (BMat8 x : _H_gens) {
        _stab_chain.add_generator(BMat8::perm_action_on_basis(row_basis, x));
      }
    }
    */

    void compute_idem_reps() {
      element_type lval     = Lambda()(this->_rep);
      element_type rval     = Rho()(this->_rep);
      size_t       lval_pos = this->_parent->_lambda_orb.position(lval);
      size_t       rval_pos = this->_parent->_rho_orb.position(rval);
      size_t       lval_scc_id
          = this->_parent->_lambda_orb.digraph().scc_id(lval_pos);
      size_t rval_scc_id = this->_parent->_rho_orb.digraph().scc_id(rval_pos);

      // this all relies on the indices having been computed already

      // TODO: use information from the looping through the left indices in
      // the loop through the right indices
      for (size_t i = 0; i < _left_indices.size(); ++i) {
        std::pair<size_t, size_t> key
            = std::make_pair(rval_scc_id, _left_indices[i]);
        size_t k = this->_parent->_group_indices_alt.at(key);
        size_t j = 0;
        while (_right_indices[j] != k) {
          ++j;
        }
        element_type x
            = this->_right_mults[j] * this->_rep * this->_left_mults[i];
        element_type y = x;
        // TODO: BMat8(UNDEFINED) happens to be idempotent... genericise!
        while (x * x != x) {
          x = x * y;
        }
        _left_idem_reps.push_back(x);
      }

      for (size_t j = 0; j < _right_indices.size(); ++j) {
        // TODO: make comprehensible
        std::pair<size_t, size_t> key
            = std::make_pair(ToInt<rho_value_type>()(
                                 this->_parent->_rho_orb.at(_right_indices[j])),
                             lval_scc_id);
        size_t k = this->_parent->_group_indices.at(key);
        size_t i = 0;
        while (_left_indices[i] != k) {
          ++i;
        }
        element_type x
            = this->_right_mults[j] * this->_rep * this->_left_mults[i];
        element_type y = x;
        // TODO: BMat8(UNDEFINED) happens to be idempotent... genericise!
        while (x * x != x) {
          x = x * y;
        }
        _right_idem_reps.push_back(x);
      }
    }

    // there should be some way of getting rid of this
    void compute_H_class() {
      this->_H_class
          = std::vector<element_type>(_H_gens.begin(), _H_gens.end());
      std::unordered_set<element_type> set(this->_H_class.begin(),
                                           this->_H_class.end());
      for (size_t i = 0; i < this->_H_class.size(); ++i) {
        for (element_type g : _H_gens) {
          element_type y = this->_H_class[i] * g;
          if (set.find(y) == set.end()) {
            set.insert(y);
            this->_H_class.push_back(y);
          }
        }
      }
    }

    void init() override {
      if (this->_computed) {
        return;
      }
      compute_left_indices();
      compute_right_indices();
      compute_mults();
      compute_reps();
      compute_idem_reps();
      compute_H_gens();
      compute_H_class();
      // compute_stab_chain();
      this->_computed = true;
    }

    std::unordered_map<size_t, size_t>             _rho_val_positions;
    std::vector<element_type>                      _H_gens;
    std::vector<element_type>                      _left_idem_reps;
    std::vector<size_t>                            _left_indices;
    std::vector<element_type>                      _right_idem_reps;
    std::vector<size_t>                            _right_indices;
    std::unordered_map<size_t, size_t>             _lambda_val_positions;
    SchreierSims<8, uint8_t, Permutation<uint8_t>> _stab_chain;
  };

  template <typename TElementType, typename TTraits>
  class Konieczny<TElementType, TTraits>::NonRegularDClass
      : public Konieczny<TElementType, TTraits>::BaseDClass {
    friend class Konieczny<TElementType, TTraits>;

   public:
    NonRegularDClass(Konieczny* parent, element_type rep)
        : Konieczny::BaseDClass(parent, rep),
          _rho_val_positions(),
          _left_idem_above(),
          _left_idem_class(),
          _H_set(),
          _right_idem_above(),
          _right_idem_class(),
          _lambda_val_positions() {
      if (rep * rep == rep) {
        LIBSEMIGROUPS_EXCEPTION("NonRegularDClass: the representative "
                                "given should not be idempotent");
      }
    }

    bool contains(element_type bm) override {
      init();
      size_t x = ToInt<lambda_value_type>()(Lambda()(bm));
      if (_lambda_val_positions[x].size() == 0) {
        return false;
      }
      size_t y = ToInt<rho_value_type>()(Rho()(bm));
      for (size_t i : _lambda_val_positions[x]) {
        for (size_t j : _rho_val_positions[y]) {
          if (_H_set.find(this->_right_mults_inv[j] * bm
                          * this->_left_mults_inv[i])
              != _H_set.end()) {
            return true;
          }
        }
      }
      return false;
    }

   private:
    void init() override {
      if (this->_computed) {
        return;
      }
      find_idems_above();
      compute_H_class();
      this->_computed = true;
    }

    void find_idems_above() {
      // assumes that all D classes above this have already been calculated!
      bool left_found  = false;
      bool right_found = false;
      for (auto it = this->_parent->_regular_D_classes.rbegin();
           (!left_found || !right_found)
           && it != this->_parent->_regular_D_classes.rend();
           it++) {
        RegularDClass* D = *it;
        if (!left_found) {
          for (auto idem_it = D->cbegin_left_idem_reps();
               idem_it < D->cend_left_idem_reps();
               idem_it++) {
            if (this->_rep * (*idem_it) == this->_rep) {
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
            if ((*idem_it) * this->_rep == this->_rep) {
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
      LIBSEMIGROUPS_ASSERT(this->_rep * _left_idem_above == this->_rep);
      LIBSEMIGROUPS_ASSERT(_right_idem_above * this->_rep == this->_rep);
#endif
    }

    // TODO: this computes more than just the H class, and should be split
    void compute_H_class() {
      this->_H_class = std::vector<element_type>();
      std::pair<size_t, size_t> left_idem_indices
          = _left_idem_class->index_positions(_left_idem_above);
      element_type left_idem_left_mult
          = _left_idem_class
                ->cbegin_left_mults()[std::get<0>(left_idem_indices)];
      element_type left_idem_right_mult
          = _left_idem_class
                ->cbegin_right_mults()[std::get<1>(left_idem_indices)];

      std::pair<size_t, size_t> right_idem_indices
          = _right_idem_class->index_positions(_right_idem_above);
      element_type right_idem_left_mult
          = _right_idem_class
                ->cbegin_left_mults()[std::get<0>(right_idem_indices)];
      element_type right_idem_right_mult
          = _right_idem_class
                ->cbegin_right_mults()[std::get<1>(right_idem_indices)];

      std::vector<element_type> _left_idem_H_class;
      std::vector<element_type> _right_idem_H_class;

      for (auto it = _left_idem_class->cbegin_H_class();
           it < _left_idem_class->cend_H_class();
           it++) {
        _left_idem_H_class.push_back(left_idem_right_mult * (*it)
                                     * left_idem_left_mult);
      }

      for (auto it = _right_idem_class->cbegin_H_class();
           it < _right_idem_class->cend_H_class();
           it++) {
        _right_idem_H_class.push_back(right_idem_right_mult * (*it)
                                      * right_idem_left_mult);
      }

      std::vector<element_type> left_idem_left_reps;
      std::vector<element_type> right_idem_right_reps;

      for (auto it = _left_idem_class->cbegin_left_mults();
           it < _left_idem_class->cend_left_mults();
           it++) {
        left_idem_left_reps.push_back(left_idem_right_mult
                                      * _left_idem_class->rep() * (*it));
      }

      for (auto it = _right_idem_class->cbegin_right_mults();
           it < _right_idem_class->cend_right_mults();
           it++) {
        right_idem_right_reps.push_back((*it) * _right_idem_class->rep()
                                        * right_idem_left_mult);
      }

      std::vector<element_type> Hex;
      std::vector<element_type> xHf;

      for (element_type s : _left_idem_H_class) {
        xHf.push_back(this->_rep * s);
      }

      for (element_type t : _right_idem_H_class) {
        Hex.push_back(t * this->_rep);
      }

      std::unordered_set<element_type> s(Hex.begin(), Hex.end());
      Hex.assign(s.begin(), s.end());

      s = std::unordered_set<element_type>(xHf.begin(), xHf.end());
      xHf.assign(s.begin(), s.end());

      std::sort(Hex.begin(), Hex.end());
      std::sort(xHf.begin(), xHf.end());

      std::set_intersection(Hex.begin(),
                            Hex.end(),
                            xHf.begin(),
                            xHf.end(),
                            std::back_inserter(this->_H_class));
      for (element_type x : this->_H_class) {
        _H_set.insert(x);
      }

      //////////////////////////////////////////
      // The rest of the function is multipliers and should be a difference
      // function... how to split without copying/storing unnecessary data?

      this->_left_reps.clear();
      this->_left_mults.clear();
      this->_right_reps.clear();
      this->_right_mults.clear();

      std::unordered_set<std::vector<element_type>, VecHash<element_type>>
          Hxhw_set;
      std::unordered_set<std::vector<element_type>, VecHash<element_type>>
          zhHx_set;

      for (element_type h : _left_idem_H_class) {
        for (size_t i = 0; i < left_idem_left_reps.size(); ++i) {
          element_type w = left_idem_left_reps[i];
          // TODO: enforce uniqueness here?
          std::vector<element_type> Hxhw;
          for (element_type s : this->_H_class) {
            Hxhw.push_back(s * h * w);
          }
          std::sort(Hxhw.begin(), Hxhw.end());
          if (Hxhw_set.find(Hxhw) == Hxhw_set.end()) {
            Hxhw_set.insert(Hxhw);
            element_type A = this->_rep * h * w;
            element_type inv
                = group_inverse<element_type>(
                      _left_idem_above,
                      w * _left_idem_class->cbegin_left_mults_inv()[i]
                          * left_idem_left_mult)
                  * group_inverse<element_type>(_left_idem_above, h);

            size_t x  = ToInt<lambda_value_type>()(Lambda()(A));
            auto   it = _lambda_val_positions.find(x);
            if (it == _lambda_val_positions.end()) {
              _lambda_val_positions.emplace(x, std::vector<size_t>());
            }
            _lambda_val_positions[x].push_back(this->_left_reps.size());
            this->_left_reps.push_back(A);
            this->_left_mults.push_back(h * w);
            this->_left_mults_inv.push_back(
                _left_idem_class->cbegin_left_mults_inv()[i]
                * left_idem_left_mult * inv);
          }
        }
      }

      for (element_type h : _right_idem_H_class) {
        for (size_t i = 0; i < right_idem_right_reps.size(); ++i) {
          element_type              z = right_idem_right_reps[i];
          std::vector<element_type> zhHx;
          for (element_type s : this->_H_class) {
            zhHx.push_back(z * h * s);
          }
          std::sort(zhHx.begin(), zhHx.end());
          if (zhHx_set.find(zhHx) == zhHx_set.end()) {
            zhHx_set.insert(zhHx);
            element_type B = z * h * this->_rep;
            element_type inv
                = group_inverse<element_type>(_right_idem_above, h)
                  * group_inverse<element_type>(
                      _right_idem_above,
                      right_idem_right_mult
                          * _right_idem_class->cbegin_right_mults_inv()[i] * z);

            size_t x  = ToInt<rho_value_type>()(Rho()(B));
            auto   it = _rho_val_positions.find(x);
            if (it == _rho_val_positions.end()) {
              _rho_val_positions.emplace(x, std::vector<size_t>());
            }
            _rho_val_positions[x].push_back(this->_right_reps.size());
            this->_right_reps.push_back(B);
            this->_right_mults.push_back(z * h);
            this->_right_mults_inv.push_back(
                inv * right_idem_right_mult
                * _right_idem_class->cbegin_right_mults_inv()[i]);
          }
        }
      }
    }

    std::unordered_map<size_t, std::vector<size_t>> _rho_val_positions;
    element_type                                    _left_idem_above;
    RegularDClass*                                  _left_idem_class;
    std::unordered_set<element_type>                _H_set;
    element_type                                    _right_idem_above;
    RegularDClass*                                  _right_idem_class;
    std::unordered_map<size_t, std::vector<size_t>> _lambda_val_positions;
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
    _D_rels.push_back(std::vector<size_t>());
  }

  template <typename TElementType, typename TTraits>
  void Konieczny<TElementType, TTraits>::add_D_class(
      Konieczny<TElementType, TTraits>::NonRegularDClass* D) {
    _D_classes.push_back(D);
    _D_rels.push_back(std::vector<size_t>());
  }

  template <typename TElementType, typename TTraits>
  size_t Konieczny<TElementType, TTraits>::size() {
    compute_D_classes();
    size_t out = 0;
    auto   it  = _D_classes.begin();
    for (; it < _D_classes.end(); it++) {
      out += (*it)->size();
    }
    return out;
  }

  template <typename TElementType, typename TTraits>
  void Konieczny<TElementType, TTraits>::compute_D_classes() {
    conditional_add_identity();
    compute_orbs();

    std::vector<std::vector<std::pair<element_type, size_t>>> reg_reps(
        257, std::vector<std::pair<element_type, size_t>>());
    std::vector<std::vector<std::pair<element_type, size_t>>> non_reg_reps(
        257, std::vector<std::pair<element_type, size_t>>());
    // TODO: reserve?
    std::set<size_t> ranks;
    size_t           max_rank = 0;
    ranks.insert(0);

    RegularDClass* top
        = new RegularDClass(this, bmat8_helpers::one<BMat8>(_dim));
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

    while (*ranks.rbegin() > 0) {
      size_t                                       reps_are_reg = false;
      std::vector<std::pair<element_type, size_t>> next_reps;

      max_rank = *ranks.rbegin();
      if (!reg_reps[max_rank].empty()) {
        reps_are_reg = true;
        next_reps    = std::move(reg_reps[max_rank]);
        reg_reps[max_rank].clear();
      } else {
        next_reps = std::move(non_reg_reps[max_rank]);
        non_reg_reps[max_rank].clear();
      }

      std::vector<std::pair<element_type, size_t>> tmp_next;
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

      while (!next_reps.empty()) {
        BaseDClass*                      D;
        std::tuple<element_type, size_t> tup;

        if (reps_are_reg) {
          tup = next_reps.back();
          D   = new RegularDClass(this, find_idem(std::get<0>(tup)));
          add_D_class(static_cast<RegularDClass*>(D));
          for (element_type x : D->covering_reps()) {
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
          for (element_type x : D->covering_reps()) {
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

        std::vector<std::pair<element_type, size_t>> tmp;
        for (std::pair<element_type, size_t>& x : next_reps) {
          if (D->contains(std::get<0>(x))) {
            _D_rels[_D_classes.size() - 1].push_back(std::get<1>(x));
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
  }
}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_INCLUDE_KONIECZNY_HPP_
