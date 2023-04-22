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

#include "libsemigroups/froidure-pin-base.hpp"

#include <vector>

#include "libsemigroups/exception.hpp"
#include "libsemigroups/report.hpp"

namespace libsemigroups {
  using element_index_type = FroidurePinBase::element_index_type;

  ////////////////////////////////////////////////////////////////////////
  // FroidurePinBase - constructors and destructor - public
  ////////////////////////////////////////////////////////////////////////

  FroidurePinBase::FroidurePinBase()
      : Runner(),
        _degree(UNDEFINED),
        _duplicate_gens(),
        _enumerate_order(),
        _final(),
        _first(),
        _found_one(false),
        _idempotents_found(false),
        _is_idempotent(),
        _left(),
        _length(),
        _lenindex({0, 0}),
        _letter_to_pos(),
        _nr(0),
        _nr_rules(0),
        _pos(0),
        _pos_one(0),
        _prefix(),
        _reduced(),
        _right(),
        _suffix(),
        // (length of the current word) - 1
        _wordlen(0) {
#ifdef LIBSEMIGROUPS_VERBOSE
    _nr_products = 0;
#endif
  }

  FroidurePinBase::FroidurePinBase(FroidurePinBase const& S)
      : Runner(S),
        _degree(UNDEFINED),  // _degree must be UNDEFINED until !_gens.empty()
        _duplicate_gens(S._duplicate_gens),
        _enumerate_order(S._enumerate_order),
        _final(S._final),
        _first(S._first),
        _found_one(S._found_one),
        _idempotents_found(S._idempotents_found),
        _is_idempotent(S._is_idempotent),
        _left(S._left),
        _length(S._length),
        _lenindex(S._lenindex),
        _letter_to_pos(S._letter_to_pos),
        _nr(S._nr),
        _nr_rules(S._nr_rules),
        _pos(S._pos),
        _pos_one(S._pos_one),
        _prefix(S._prefix),
        _reduced(S._reduced),
        _right(S._right),
        _suffix(S._suffix),
        _wordlen(S._wordlen) {
#ifdef LIBSEMIGROUPS_VERBOSE
    _nr_products = 0;
#endif
  }

  FroidurePinBase::~FroidurePinBase() = default;

  ////////////////////////////////////////////////////////////////////////
  // FroidurePinBase - constructors - private
  ////////////////////////////////////////////////////////////////////////

  // Partial copy.
  // \p copy a semigroup
  // \p coll a collection of additional generators
  //
  // This is a constructor for a semigroup generated by the generators of the
  // FroidurePin copy and the (possibly) additional generators coll.
  //
  // The relevant parts of the data structure of copy are copied and
  // \c this will be corrupt unless add_generators or closure is called
  // subsequently. This is why this member function is private.
  //
  // The same effect can be obtained by copying copy using the copy
  // constructor and then calling add_generators or closure. However,
  // this constructor avoids copying those parts of the data structure of
  // copy that add_generators invalidates anyway. If copy has not been
  // enumerated at all, then these two routes for adding more generators are
  // equivalent.
  //
  // <add_generators> or <closure> should usually be called after this.
  void FroidurePinBase::partial_copy(FroidurePinBase const& S) {
    _degree         = S._degree;  // copy for comparison in add_generators
    _duplicate_gens = S._duplicate_gens;
    _found_one      = S._found_one;  // copy in case degree doesn't change in
    // add_generators
    _idempotents_found = S._idempotents_found;
    _is_idempotent     = S._is_idempotent;
    _left              = S._left;
    _lenindex          = {0, S._lenindex[1]};
    _letter_to_pos     = S._letter_to_pos;
    _nr                = S._nr;
    _nr_rules          = 0;
    _pos               = S._pos;
    _pos_one           = S._pos_one;  // copy in case degree doesn't change in
    // add_generators
    _reduced = S._reduced;
    _right   = S._right;
    _wordlen = 0;

    LIBSEMIGROUPS_ASSERT(S._lenindex.size() > 1);

#ifdef LIBSEMIGROUPS_VERBOSE
    _nr_products = 0;
#endif

    // the following are required for assignment to specific positions in
    // add_generators
    _final.resize(S._nr, 0);
    _first.resize(S._nr, 0);
    _length.resize(S._nr, 0);
    _prefix.resize(S._nr, 0);
    _suffix.resize(S._nr, 0);

    _enumerate_order.reserve(S._nr);

    // add the distinct old generators to new _enumerate_order
    LIBSEMIGROUPS_ASSERT(S._lenindex.size() > 1);
    for (enumerate_index_type i = 0; i < S._lenindex[1]; i++) {
      _enumerate_order.push_back(S._enumerate_order[i]);
      _final[_enumerate_order[i]]  = S._final[S._enumerate_order[i]];
      _first[_enumerate_order[i]]  = S._first[S._enumerate_order[i]];
      _prefix[_enumerate_order[i]] = UNDEFINED;
      _suffix[_enumerate_order[i]] = UNDEFINED;
      _length[_enumerate_order[i]] = 1;
    }
  }

  ////////////////////////////////////////////////////////////////////////
  // FroidurePinBase - member functions - public
  ////////////////////////////////////////////////////////////////////////

  element_index_type
  FroidurePinBase::current_position(word_type const& w) const {
    // w is a word in the generators (i.e. a vector of letter_type's)
    if (w.size() == 0) {
      LIBSEMIGROUPS_EXCEPTION("the given word has length 0");
    }
    for (auto x : w) {
      validate_letter_index(x);
    }
    element_index_type out = _letter_to_pos[w[0]];
    size_t const       n   = _right.number_of_nodes();
    auto               it  = w.cbegin() + 1;
    while (it < w.cend() && out < n) {
      out = _right.neighbor_no_checks(out, *it++);
    }
    if (out < n) {
      return out;
    }
    return UNDEFINED;
  }

  element_index_type
  FroidurePinBase::product_by_reduction(element_index_type i,
                                        element_index_type j) const {
    validate_element_index(i);
    validate_element_index(j);

    if (current_length(i) <= current_length(j)) {
      while (i != UNDEFINED) {
        j = _left.neighbor_no_checks(j, _final[i]);
        i = _prefix[i];
      }
      return j;
    } else {
      while (j != UNDEFINED) {
        i = _right.neighbor_no_checks(i, _first[j]);
        j = _suffix[j];
      }
      return i;
    }
  }

  void FroidurePinBase::enumerate(size_t limit) {
    if (finished() || limit <= current_size()) {
      return;
    } else if (LIMIT_MAX - batch_size() > current_size()) {
      limit = std::max(limit, current_size() + batch_size());
    } else {  // batch_size() is very big for some reason
      limit = batch_size();
    }
    REPORT_DEFAULT(
        "limit = %llu (%s)\n", static_cast<uint64_t>(limit), __func__);
    run_until([this, &limit]() -> bool { return current_size() >= limit; });
  }

  size_t FroidurePinBase::number_of_elements_of_length(size_t i) const {
    // _lenindex[i - 1] is the element_index_type where words of length i begin
    // so _lenindex[i] - _lenindex[i - 1]) is the number of words of length
    // i.
    if (i == 0 || i > _lenindex.size()) {
      return 0;
    } else if (i == _lenindex.size()) {
      return current_size() - _lenindex[i - 1];
    }
    return _lenindex[i] - _lenindex[i - 1];
  }

  size_t FroidurePinBase::number_of_elements_of_length(size_t min,
                                                       size_t max) const {
    size_t result = 0;
    for (size_t i = min; i < max; ++i) {
      size_t next = number_of_elements_of_length(i);
      result += next;
      if (i != 0 && next == 0) {
        break;
      }
    }
    return result;
  }

  ////////////////////////////////////////////////////////////////////////
  // FroidurePinBase - settings - public
  ////////////////////////////////////////////////////////////////////////

  FroidurePinBase& FroidurePinBase::batch_size(size_t batch_size) noexcept {
    _settings._batch_size = batch_size;
    return *this;
  }

  size_t FroidurePinBase::batch_size() const noexcept {
    return _settings._batch_size;
  }

  FroidurePinBase&
  FroidurePinBase::max_threads(size_t number_of_threads) noexcept {
    unsigned int n = static_cast<unsigned int>(
        number_of_threads == 0 ? 1 : number_of_threads);
    _settings._max_threads = std::min(n, std::thread::hardware_concurrency());
    return *this;
  }

  size_t FroidurePinBase::max_threads() const noexcept {
    return _settings._max_threads;
  }

  FroidurePinBase&
  FroidurePinBase::concurrency_threshold(size_t thrshld) noexcept {
    _settings._concurrency_threshold = thrshld;
    return *this;
  }

  size_t FroidurePinBase::concurrency_threshold() const noexcept {
    return _settings._concurrency_threshold;
  }

  FroidurePinBase& FroidurePinBase::immutable(bool val) noexcept {
    _settings._immutable = val;
    return *this;
  }

  bool FroidurePinBase::immutable() const noexcept {
    return _settings._immutable;
  }
}  // namespace libsemigroups
