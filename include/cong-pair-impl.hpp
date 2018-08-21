//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2018 James D. Mitchell
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

// This file contains implementations of the methods for congruence::P.

// TODO(later):
//   1. the type of the congruence defined by class P could be a template
//      parameter
//   2. use shared_ptr rather than raw pointer to fpsemigroup::KnuthBendix in
//      KBP class.

#define TEMPLATE                    \
  template <typename TElementType,  \
            typename TElementHash,  \
            typename TElementEqual, \
            class TTraits>
#define P_CLASS P<TElementType, TElementHash, TElementEqual, TTraits>

#define VOID TEMPLATE void
#define SIZE_T TEMPLATE size_t
#define CLASS_INDEX_TYPE TEMPLATE class_index_type

namespace libsemigroups {
  namespace congruence {
    using class_index_type = CongBase::class_index_type;

    ////////////////////////////////////////////////////////////////////////
    // P - constructor - protected
    ////////////////////////////////////////////////////////////////////////

    TEMPLATE
    P_CLASS::P(congruence_type type)
        : CongBase(type),
          _class_lookup(),
          _found_pairs(),
          _init_done(false),
          _lookup(0),
          _map(),
          _map_next(0),
          _next_class(0),
          _nr_non_trivial_classes(UNDEFINED),
          _nr_non_trivial_elemnts(UNDEFINED),
          _pairs_to_mult(),
          _reverse_map(),
          _tmp1(),
          _tmp2() {}

    ////////////////////////////////////////////////////////////////////////
    // P - constructor + destructor - public
    ////////////////////////////////////////////////////////////////////////

    TEMPLATE
    P_CLASS::P(congruence_type type, FroidurePinBase* S) : P(type) {
      LIBSEMIGROUPS_ASSERT(S != nullptr);
      set_nr_generators(S->nr_generators());
      set_parent(S);
    }

    TEMPLATE
    P_CLASS::P(congruence_type type, FroidurePinBase& S) : P(type, &S) {}

    TEMPLATE
    P_CLASS::~P() {
      delete_tmp_storage();
      this->internal_free(_tmp1);
      this->internal_free(_tmp2);
      for (auto& x : _map) {
        this->internal_free(const_cast<internal_element_type>(x.first));
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // Runner - overridden pure virtual methods - public
    ////////////////////////////////////////////////////////////////////////

    VOID P_CLASS::run() {
      if (finished() || dead()) {
        return;
      }
      Timer t;
      init();

      size_t tid = REPORTER.thread_id(std::this_thread::get_id());
      while (!_pairs_to_mult.empty() && !dead() && !timed_out()) {
        // Get the next pair
        auto& current_pair = _pairs_to_mult.front();
        _pairs_to_mult.pop();

        auto prnt = static_cast<froidure_pin_type*>(get_parent());
        // Add its left and/or right multiples
        for (size_t i = 0; i < prnt->nr_generators(); i++) {
          const_reference gen = prnt->generator(i);
          if (type() == congruence_type::LEFT
              || type() == congruence_type::TWOSIDED) {
            product()(
                _tmp1, this->to_internal_const(gen), current_pair.first, tid);
            product()(
                _tmp2, this->to_internal_const(gen), current_pair.second, tid);
            internal_add_pair(_tmp1, _tmp2);
          }
          if (type() == congruence_type::RIGHT
              || type() == congruence_type::TWOSIDED) {
            product()(
                _tmp1, current_pair.first, this->to_internal_const(gen), tid);
            product()(
                _tmp2, current_pair.second, this->to_internal_const(gen), tid);
            internal_add_pair(_tmp1, _tmp2);
          }
        }
        if (report()) {
          REPORT("found ",
                 _found_pairs.size(),
                 " pairs: ",
                 _map_next,
                 " elements in ",
                 _lookup.nr_blocks(),
                 " classes, ",
                 _pairs_to_mult.size(),
                 " pairs on the stack");
        }
      }

      if (!dead() && !timed_out()) {
        // Make a normalised class lookup (class numbers {0, .., n-1}, in
        // order)
        if (_lookup.get_size() > 0) {
          _class_lookup.reserve(_lookup.get_size());
          _next_class = 1;
          size_t max  = 0;
          LIBSEMIGROUPS_ASSERT(_lookup.find(0) == 0);
          _class_lookup.push_back(0);
          for (size_t i = 1; i < _lookup.get_size(); i++) {
            size_t nr = _lookup.find(i);
            if (nr > max) {
              _class_lookup.push_back(_next_class++);
              max = nr;
            } else {
              _class_lookup.push_back(_class_lookup[nr]);
            }
          }
        }

        // Record information about non-trivial classes
        _nr_non_trivial_classes = _next_class;
        _nr_non_trivial_elemnts = _map_next;
      }

      REPORT("stopping with ",
             _found_pairs.size(),
             " pairs: ",
             _map_next,
             " elements in ",
             _lookup.nr_blocks(),
             " classes");
      REPORT("elapsed time = ", t);
      report_why_we_stopped();
      if (!dead() && !timed_out()) {
        set_finished(true);
        delete_tmp_storage();
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // CongBase - overridden pure virtual methods - public
    ////////////////////////////////////////////////////////////////////////

    VOID P_CLASS::add_pair(word_type const& l, word_type const& r) {
      if (!has_parent()) {
        throw LIBSEMIGROUPS_EXCEPTION("cannot add generating pairs before "
                                      "the parent semigroup is defined");
      }
      auto x
          = static_cast<froidure_pin_type*>(get_parent())->word_to_element(l);
      auto y
          = static_cast<froidure_pin_type*>(get_parent())->word_to_element(r);
      internal_add_pair(this->to_internal(x), this->to_internal(y));
      this->external_free(x);
      this->external_free(y);
      set_finished(false);
    }

    WORD_TYPE P_CLASS::class_index_to_word(class_index_type) {
      // FIXME(now) actually implement this
      throw LIBSEMIGROUPS_EXCEPTION("not yet implemented");
    }

    TEMPLATE
    FroidurePinBase* P_CLASS::quotient_semigroup() {
      // FIXME(now) actually implement this
      throw LIBSEMIGROUPS_EXCEPTION("not yet implemented");
    }

    SIZE_T P_CLASS::nr_classes() {
      run();
      return get_parent()->size() - _class_lookup.size() + _next_class;
    }

    CLASS_INDEX_TYPE P_CLASS::word_to_class_index(word_type const& w) {
      run();
      LIBSEMIGROUPS_ASSERT(finished());
      return const_word_to_class_index(w);
    }

    ////////////////////////////////////////////////////////////////////////
    // CongBase - overridden non-pure virtual methods - protected
    ////////////////////////////////////////////////////////////////////////

    CLASS_INDEX_TYPE
    P_CLASS::const_word_to_class_index(word_type const& w) const {
      if (!finished()) {
        return UNDEFINED;
      }
      auto x
          = static_cast<froidure_pin_type*>(get_parent())->word_to_element(w);
      size_t ind_x = get_index(this->to_internal_const(x));
      this->external_free(x);
      LIBSEMIGROUPS_ASSERT(ind_x < _class_lookup.size());
      LIBSEMIGROUPS_ASSERT(_class_lookup.size() == _map.size());
      return _class_lookup[ind_x];
    }

    VOID P_CLASS::init_non_trivial_classes() {
      run();
      LIBSEMIGROUPS_ASSERT(_reverse_map.size() >= _nr_non_trivial_elemnts);
      LIBSEMIGROUPS_ASSERT(_class_lookup.size() >= _nr_non_trivial_elemnts);
      LIBSEMIGROUPS_ASSERT(has_parent());

      _non_trivial_classes.assign(_nr_non_trivial_classes,
                                  std::vector<word_type>());
      for (size_t ind = 0; ind < _nr_non_trivial_elemnts; ++ind) {
        word_type word
            = static_cast<froidure_pin_type*>(get_parent())
                  ->factorisation(this->to_external(_reverse_map[ind]));
        _non_trivial_classes[_class_lookup[ind]].push_back(word);
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // P - methods - protected
    ////////////////////////////////////////////////////////////////////////

    VOID P_CLASS::internal_add_pair(internal_const_element_type x,
                                    internal_const_element_type y) {
      if (!internal_equal_to()(x, y)) {
        internal_element_type xx, yy;
        bool                  xx_new = false, yy_new = false;
        size_t                i, j;

        auto it_x = _map.find(x);
        if (it_x == _map.end()) {
          xx_new = true;
          xx     = this->internal_copy(x);
          i      = add_index(xx);
        } else {
          i = it_x->second;
        }

        auto it_y = _map.find(y);
        if (it_y == _map.end()) {
          yy_new = true;
          yy     = this->internal_copy(y);
          j      = add_index(yy);
        } else {
          j = it_y->second;
        }

        LIBSEMIGROUPS_ASSERT(i != j);
        std::pair<internal_element_type, internal_element_type> pair;
        if (xx_new || yy_new) {  // it's a new pair
          xx   = internal_element_type(xx_new ? xx : it_x->first);
          yy   = internal_element_type(yy_new ? yy : it_y->first);
          pair = (i < j ? std::make_pair(xx, yy) : std::make_pair(yy, xx));
        } else {
          pair = (i < j ? std::make_pair(internal_element_type(it_x->first),
                                         internal_element_type(it_y->first))
                        : std::make_pair(internal_element_type(it_y->first),
                                         internal_element_type(it_x->first)));
          if (_found_pairs.find(pair) != _found_pairs.end()) {
            return;
          }
        }
        _found_pairs.insert(pair);
        _pairs_to_mult.push(pair);
        _lookup.unite(i, j);
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // P - methods - private
    ////////////////////////////////////////////////////////////////////////

    SIZE_T P_CLASS::add_index(internal_element_type x) const {
      LIBSEMIGROUPS_ASSERT(_reverse_map.size() == _map_next);
      LIBSEMIGROUPS_ASSERT(_map.size() == _map_next);
      _map.emplace(x, _map_next);
      _reverse_map.push_back(x);
      _lookup.add_entry();
      if (finished()) {
        _class_lookup.push_back(_next_class++);
      }
      return _map_next++;
    }

    VOID P_CLASS::delete_tmp_storage() {
      std::unordered_set<
          std::pair<internal_element_type, internal_element_type>,
          PHash,
          PEqual>()
          .swap(_found_pairs);
      std::queue<std::pair<internal_element_type, internal_element_type>>()
          .swap(_pairs_to_mult);
    }

    SIZE_T P_CLASS::get_index(internal_const_element_type x) const {
      auto it = _map.find(x);
      if (it == _map.end()) {
        return add_index(this->internal_copy(x));
      }
      return it->second;
    }

    VOID P_CLASS::init() {
      if (!_init_done) {
        LIBSEMIGROUPS_ASSERT(has_parent());
        LIBSEMIGROUPS_ASSERT(get_parent()->nr_generators() > 0);
        _tmp1      = this->internal_copy(this->to_internal_const(
            static_cast<froidure_pin_type*>(get_parent())->generator(0)));
        _tmp2      = this->internal_copy(_tmp1);
        _init_done = true;
      }
    }
  }  // namespace congruence
}  // namespace libsemigroups