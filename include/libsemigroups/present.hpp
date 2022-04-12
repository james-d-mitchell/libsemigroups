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

#ifndef LIBSEMIGROUPS_PRESENT_HPP_
#define LIBSEMIGROUPS_PRESENT_HPP_

#include <cstddef>
#include <string>
#include <unordered_set>

#include "exception.hpp"
#include "types.hpp"

namespace libsemigroups {

  template <typename WordType>
  class Presentation {
   public:
    using word_type      = WordType;
    using letter_type    = typename WordType::value_type;
    using const_iterator = typename std::vector<word_type>::const_iterator;

    enum class empty_word { yes, no };

   private:
    word_type                       _alphabet;
    std::unordered_set<letter_type> _alphabet_set;
    empty_word                      _empty_word;
    std::vector<word_type>          _relations;

   public:
    explicit Presentation(empty_word ew)
        : _alphabet(), _alphabet_set(), _empty_word(ew), _relations() {}

    Presentation() : Presentation(empty_word::no) {}

    Presentation(Presentation const&) = default;
    Presentation(Presentation&&)      = default;
    Presentation& operator=(Presentation const&) = default;
    Presentation& operator=(Presentation&&) = default;

    Presentation& alphabet(word_type const& alphabet) {
      if (alphabet.empty()) {
        LIBSEMIGROUPS_EXCEPTION("the alphabet must be non-empty");
      }
      auto alphabet_set = _alphabet_set;
      for (auto const& letter : alphabet) {
        auto it = alphabet_set.emplace(letter);
        if (!it.second) {
          LIBSEMIGROUPS_EXCEPTION("invalid alphabet, duplicate letter %s!",
                                  detail::to_string(letter).c_str());
        }
      }
      _alphabet_set = std::move(alphabet_set);
      _alphabet     = alphabet;
      return *this;
    }

    word_type const& alphabet() const noexcept {
      return _alphabet;
    }

    template <typename T>
    Presentation& add_pair(T lhs_begin, T lhs_end, T rhs_begin, T rhs_end) {
      _relations.emplace_back(lhs_begin, lhs_end);
      _relations.emplace_back(rhs_begin, rhs_end);
      return *this;
    }

    template <typename T>
    Presentation&
    add_pair_and_check(T lhs_begin, T lhs_end, T rhs_begin, T rhs_end) {
      validate_word(lhs_begin, lhs_end);
      validate_word(rhs_begin, rhs_end);
      return add_pair(lhs_begin, lhs_end, rhs_begin, rhs_end);
    }

    const_iterator cbegin() const noexcept {
      return _relations.cbegin();
    }

    const_iterator cend() const noexcept {
      return _relations.cend();
    }

   private:
    void validate_letter(letter_type c) const {
      if (_alphabet.empty()) {
        LIBSEMIGROUPS_EXCEPTION("no alphabet has been defined");
      } else if (_alphabet_set.find(c) == _alphabet_set.cend()) {
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

    template <typename WordType, typename TContainer>
    void add_pair(Presentation<WordType>& p,
                  TContainer const&       lhop,
                  TContainer const&       rhop) {
      p.add_pair(lhop.begin(), lhop.end(), rhop.begin(), rhop.end());
    }

    template <typename WordType>
    void add_pair(Presentation<WordType>& p,
                  char const*             lhop,
                  char const*             rhop) {
      add_pair(p, std::string(lhop), std::string(rhop));
    }

    template <typename WordType, typename T>
    void add_pair(Presentation<WordType>&  p,
                  std::initializer_list<T> lhop,
                  std::initializer_list<T> rhop) {
      p.add_pair(lhop.begin(), lhop.end(), rhop.begin(), rhop.end());
    }

    template <typename WordType, typename TContainer>
    void add_pair_and_check(Presentation<WordType>& p,
                            TContainer const&       lhop,
                            TContainer const&       rhop) {
      p.add_pair_and_check(lhop.begin(), lhop.end(), rhop.begin(), rhop.end());
    }

    template <typename WordType>
    void add_pair_and_check(Presentation<WordType>& p,
                            char const*             lhop,
                            char const*             rhop) {
      add_pair_and_check(p, std::string(lhop), std::string(rhop));
    }

    template <typename WordType, typename T>
    void add_pair_and_check(Presentation<WordType>&  p,
                            std::initializer_list<T> lhop,
                            std::initializer_list<T> rhop) {
      p.add_pair_and_check(lhop.begin(), lhop.end(), rhop.begin(), rhop.end());
    }
  }  // namespace presentation
}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_PRESENT_HPP_
