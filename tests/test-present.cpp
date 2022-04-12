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

#define CATCH_CONFIG_ENABLE_PAIR_STRINGMAKER

#include <cstddef>        // for size_t
#include <stdexcept>      // for runtime_error
#include <unordered_set>  // for unordered_set
#include <vector>         // for vector

#include "catch.hpp"  // for REQUIRE, REQUIRE_THROWS_AS, REQUI...
#include "libsemigroups/present.hpp"  // for Presentation
#include "libsemigroups/types.hpp"    // for word_type
#include "test-main.hpp"              // for LIBSEMIGROUPS_TEST_CASE

namespace libsemigroups {

  struct LibsemigroupsException;  // forward decl
  LIBSEMIGROUPS_TEST_CASE("Presentation",
                          "000",
                          "vectors of ints",
                          "[quick][presentation]") {
    Presentation<word_type> p;
    p.alphabet({0, 1, 2});
    REQUIRE(p.alphabet() == word_type({0, 1, 2}));
    REQUIRE_THROWS_AS(p.alphabet({}), LibsemigroupsException);
    REQUIRE(p.alphabet() == word_type({0, 1, 2}));
    REQUIRE_THROWS_AS(p.alphabet({0, 0}), LibsemigroupsException);
    REQUIRE(p.alphabet() == word_type({0, 1, 2}));
    presentation::add_pair(p, {0, 0, 0}, {0});
    REQUIRE(std::distance(p.cbegin(), p.cend()) == 2);
    REQUIRE(std::vector<word_type>(p.cbegin(), p.cend())
            == std::vector<word_type>({{0, 0, 0}, {0}}));
    presentation::add_pair_and_check(p, {0, 0, 0}, {0});
    REQUIRE_THROWS_AS(presentation::add_pair_and_check(p, {0, 5, 0}, {0}),
                      LibsemigroupsException);
    REQUIRE_THROWS_AS(presentation::add_pair_and_check(p, {}, {0}),
                      LibsemigroupsException);
  }

  LIBSEMIGROUPS_TEST_CASE("Presentation",
                          "001",
                          "strings",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("abc");
    REQUIRE(p.alphabet() == "abc");
    REQUIRE_THROWS_AS(p.alphabet(""), LibsemigroupsException);
    REQUIRE(p.alphabet() == "abc");
    REQUIRE_THROWS_AS(p.alphabet("aa"), LibsemigroupsException);
    REQUIRE(p.alphabet() == "abc");
    presentation::add_pair(p, "aaa", "a");
    REQUIRE(std::distance(p.cbegin(), p.cend()) == 2);
    REQUIRE(std::vector<std::string>(p.cbegin(), p.cend())
            == std::vector<std::string>({"aaa", "a"}));
    REQUIRE_THROWS_AS(presentation::add_pair_and_check(p, "abz", "a"),
                      LibsemigroupsException);
    REQUIRE_THROWS_AS(presentation::add_pair_and_check(p, "", "a"),
                      LibsemigroupsException);
  }

}  // namespace libsemigroups
