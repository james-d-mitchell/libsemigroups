//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2022 James D. Mitchell
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

// TODO
// * write file description
// * only allow alphabets consisting of initial segments of the naturals, or
// handle non-consecutive values better internally (or maybe just enforce this
// where needed elsewhere).
// * identity_check, inverse_check

#ifndef LIBSEMIGROUPS_PRESENT_HPP_
#define LIBSEMIGROUPS_PRESENT_HPP_

#include <cstddef>
#include <string>
#include <unordered_set>

#include "exception.hpp"
#include "types.hpp"

namespace libsemigroups {
  struct PresentationPolymorphicBase {
    enum class empty_word { yes, no };
  };

  template <typename WordType>
  class Presentation : public PresentationPolymorphicBase {
   public:
    using word_type      = WordType;
    using letter_type    = typename word_type::value_type;
    using const_iterator = typename std::vector<word_type>::const_iterator;
    using const_alphabet_iterator = typename word_type::const_iterator;
    using size_type               = size_t;

   private:
    word_type                                  _alphabet;
    std::unordered_map<letter_type, size_type> _alphabet_map;
    empty_word                                 _empty_word;
    std::vector<word_type>                     _relations;

   public:
    explicit Presentation(empty_word ew)
        : _alphabet(), _alphabet_map(), _empty_word(ew), _relations() {}

    Presentation() : Presentation(empty_word::no) {}

    Presentation(Presentation const&) = default;
    Presentation(Presentation&&)      = default;
    Presentation& operator=(Presentation const&) = default;
    Presentation& operator=(Presentation&&) = default;

    Presentation& alphabet(size_t n) {
      word_type lphbt(n, 0);
      std::iota(lphbt.begin(), lphbt.end(), 0);
      alphabet(lphbt);
      return *this;
    }

    Presentation& alphabet(word_type const& alphabet) {
      if (alphabet.empty()) {
        LIBSEMIGROUPS_EXCEPTION("the alphabet must be non-empty");
      } else if (!_alphabet_map.empty()) {
        LIBSEMIGROUPS_EXCEPTION("the alphabet has already been set");
      }

      // We copy the _alphabet_map for exception safety
      auto      alphabet_map = _alphabet_map;
      size_type index        = 0;
      for (auto const& letter : alphabet) {
        auto it = alphabet_map.emplace(letter, index++);
        if (!it.second) {
          LIBSEMIGROUPS_EXCEPTION("invalid alphabet, duplicate letter %s!",
                                  detail::to_string(letter).c_str());
        }
      }
      _alphabet_map = std::move(alphabet_map);
      _alphabet     = alphabet;
      return *this;
    }

    word_type const& alphabet() const noexcept {
      return _alphabet;
    }

    size_type letter_index(size_type val) const {
      return _alphabet_map.find(val)->second;
    }

    const_alphabet_iterator cbegin_alphabet() const noexcept {
      return _alphabet.cbegin();
    }

    const_alphabet_iterator cend_alphabet() const noexcept {
      return _alphabet.cend();
    }

    template <typename T>
    Presentation& add_rule(T lhs_begin, T lhs_end, T rhs_begin, T rhs_end) {
      _relations.emplace_back(lhs_begin, lhs_end);
      _relations.emplace_back(rhs_begin, rhs_end);
      return *this;
    }

    template <typename T>
    Presentation&
    add_rule_and_check(T lhs_begin, T lhs_end, T rhs_begin, T rhs_end) {
      validate_word(lhs_begin, lhs_end);
      validate_word(rhs_begin, rhs_end);
      return add_rule(lhs_begin, lhs_end, rhs_begin, rhs_end);
    }

    const_iterator cbegin() const noexcept {
      return _relations.cbegin();
    }

    const_iterator cend() const noexcept {
      return _relations.cend();
    }

    bool contains_empty_word() const noexcept {
      return _empty_word == empty_word::yes;
    }

    Presentation& contains_empty_word(empty_word val) {
      _empty_word = val;
      return *this;
    }

   private:
    void validate_letter(letter_type c) const {
      if (_alphabet.empty()) {
        LIBSEMIGROUPS_EXCEPTION("no alphabet has been defined");
      } else if (_alphabet_map.find(c) == _alphabet_map.cend()) {
        LIBSEMIGROUPS_EXCEPTION("invalid letter %llu, valid letter are %s",
                                uint64_t(c),
                                detail::to_string(_alphabet).c_str());
      }
    }

    template <typename T>
    void validate_word(T first, T last) const {
      if (_empty_word == empty_word::no && std::distance(first, last) == 0) {
        LIBSEMIGROUPS_EXCEPTION("words in relations cannot be empty");
      }
      for (auto it = first; it != last; ++it) {
        validate_letter(*it);
      }
    }
  };

  namespace presentation {
    // TODO emplace_rule, emplace_rule_and_check

    template <typename WordType, typename TContainer>
    void add_rule(Presentation<WordType>& p,
                  TContainer const&       lhop,
                  TContainer const&       rhop) {
      p.add_rule(lhop.begin(), lhop.end(), rhop.begin(), rhop.end());
    }

    template <typename WordType>
    void add_rule(Presentation<WordType>& p,
                  char const*             lhop,
                  char const*             rhop) {
      add_rule(p, std::string(lhop), std::string(rhop));
    }

    template <typename WordType, typename T>
    void add_rule(Presentation<WordType>&  p,
                  std::initializer_list<T> lhop,
                  std::initializer_list<T> rhop) {
      p.add_rule(lhop.begin(), lhop.end(), rhop.begin(), rhop.end());
    }

    template <typename WordType, typename TContainer>
    void add_rule_and_check(Presentation<WordType>& p,
                            TContainer const&       lhop,
                            TContainer const&       rhop) {
      p.add_rule_and_check(lhop.begin(), lhop.end(), rhop.begin(), rhop.end());
    }

    template <typename WordType>
    void add_rule_and_check(Presentation<WordType>& p,
                            char const*             lhop,
                            char const*             rhop) {
      add_rule_and_check(p, std::string(lhop), std::string(rhop));
    }

    template <typename WordType, typename T>
    void add_rule_and_check(Presentation<WordType>&  p,
                            std::initializer_list<T> lhop,
                            std::initializer_list<T> rhop) {
      p.add_rule_and_check(lhop.begin(), lhop.end(), rhop.begin(), rhop.end());
    }

    template <typename WordType>
    typename Presentation<WordType>::letter_type
    alphabet(Presentation<WordType> const& p, size_t i) {
      return *(p.cbegin_alphabet() + i);
    }

    template <typename WordType>
    void identity(Presentation<WordType>&                      p,
                  typename Presentation<WordType>::letter_type id) {
      for (auto it = p.cbegin_alphabet(); it != p.cend_alphabet(); ++it) {
        WordType       lhs = {*it, id};
        WordType const rhs = {*it};
        add_rule(p, lhs, rhs);
        if (*it != id) {
          lhs = {id, *it};
          add_rule(p, lhs, rhs);
        }
      }
    }

    // TODO(now) this adds too many pairs
    template <typename WordType>
    void inverses(Presentation<WordType>&                      p,
                  WordType const&                              vals,
                  typename Presentation<WordType>::letter_type id) {
      WordType const rhs = {id};
      for (size_t i = 0; i < p.alphabet().size(); ++i) {
        WordType lhs = {alphabet(p, i), vals[i]};
        add_rule(p, lhs, rhs);
        if (alphabet(p, i) != id) {
          std::swap(lhs[0], lhs[1]);
          add_rule(p, lhs, rhs);
        }
      }
    }

    void inverses(Presentation<std::string>& p, char const* vals, char id) {
      inverses(p, std::string(vals), id);
    }
  }  // namespace presentation
}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_PRESENT_HPP_
