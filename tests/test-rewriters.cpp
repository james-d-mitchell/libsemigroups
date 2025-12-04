// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019-2025 Joseph Edwards
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

#include "Catch2-3.8.0/catch_amalgamated.hpp"  // for AssertionHandler, ope...
#include "test-main.hpp"                       // for LIBSEMIGROUPS_TEST_CASE

#include "libsemigroups/aho-corasick.hpp"  // for dot
#include "libsemigroups/word-range.hpp"    // for operator""_w

#include "libsemigroups/detail/report.hpp"     // for ReportGuard
#include "libsemigroups/detail/rewriters.hpp"  // for RewritingSystemTrie

namespace libsemigroups {
  using literals::operator""_w;

  namespace detail {
    using string_type = RewritingSystemTrie::native_word_type;
    using namespace std::literals;

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "000",
                            "initial test",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;
      REQUIRE(rt.number_of_active_rules() == 0);
      rt.increase_alphabet_size_by(2);
      rewriting_system::add_rule(rt, "ba"_w, "a"_w);
      REQUIRE(rt.number_of_pending_rules() == 1);
      REQUIRE(rt.number_of_active_rules() == 0);
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "001",
                            "simple test",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;

      rt.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rt, "ac"_w, "ca"_w);
      rewriting_system::add_rule(rt, "aa"_w, "a"_w);
      rewriting_system::add_rule(rt, "ac"_w, "a"_w);
      rewriting_system::add_rule(rt, "ca"_w, "a"_w);
      rewriting_system::add_rule(rt, "bb"_w, "bb"_w);
      rewriting_system::add_rule(rt, "bc"_w, "cb"_w);
      rewriting_system::add_rule(rt, "bbb"_w, "b"_w);
      rewriting_system::add_rule(rt, "bc"_w, "b"_w);
      rewriting_system::add_rule(rt, "cb"_w, "b"_w);
      rewriting_system::add_rule(rt, "a"_w, "b"_w);

      REQUIRE(rt.confluent());

      string_type w1 = {0, 0};
      rt.rewrite(w1);
      REQUIRE(w1 == string_type({0}));

      string_type w2 = {0, 1};
      rt.rewrite(w2);
      REQUIRE(w2 == string_type({0}));

      string_type w3 = {0, 1, 2};
      rt.rewrite(w3);
      REQUIRE(w3 == string_type({0}));

      string_type w4 = {0, 1, 2, 0};
      rt.rewrite(w4);
      REQUIRE(w4 == string_type({0}));

      string_type w5 = {2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0, 2, 1, 0, 2, 1,
                        0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1,
                        1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0};
      rt.rewrite(w5);
      REQUIRE(w5 == string_type({0}));
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemSet",
                            "010",
                            "simple test",
                            "[quick]") {
      auto               rg = ReportGuard(false);
      RewritingSystemSet rfl;

      rfl.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rfl, "ac"_w, "ca"_w);
      rewriting_system::add_rule(rfl, "aa"_w, "a"_w);
      rewriting_system::add_rule(rfl, "ac"_w, "a"_w);
      rewriting_system::add_rule(rfl, "ca"_w, "a"_w);
      rewriting_system::add_rule(rfl, "bb"_w, "bb"_w);
      rewriting_system::add_rule(rfl, "bc"_w, "cb"_w);
      rewriting_system::add_rule(rfl, "bbb"_w, "b"_w);
      rewriting_system::add_rule(rfl, "bc"_w, "b"_w);
      rewriting_system::add_rule(rfl, "cb"_w, "b"_w);
      rewriting_system::add_rule(rfl, "a"_w, "b"_w);

      REQUIRE(rfl.confluent());

      string_type w1 = {0, 0};
      rfl.rewrite(w1);
      REQUIRE(w1 == string_type({0}));

      string_type w2 = {0, 1};
      rfl.rewrite(w2);
      REQUIRE(w2 == string_type({0}));

      string_type w3 = {0, 1, 2};
      rfl.rewrite(w3);
      REQUIRE(w3 == string_type({0}));

      string_type w4 = {0, 1, 2, 0};
      rfl.rewrite(w4);
      REQUIRE(w4 == string_type({0}));

      string_type w5 = {2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0, 2, 1, 0, 2, 1,
                        0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1,
                        1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0};
      rfl.rewrite(w5);
      REQUIRE(w5 == string_type({0}));
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "002",
                            "confluent",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;
      rt.increase_alphabet_size_by(3);

      rewriting_system::add_rule(rt, "ab"_w, "ba"_w);
      rewriting_system::add_rule(rt, "ac"_w, "ca"_w);
      rewriting_system::add_rule(rt, "aa"_w, "a"_w);
      rewriting_system::add_rule(rt, "ac"_w, "a"_w);
      rewriting_system::add_rule(rt, "ca"_w, "a"_w);
      rewriting_system::add_rule(rt, "bb"_w, "bb"_w);
      rewriting_system::add_rule(rt, "bc"_w, "cb"_w);
      rewriting_system::add_rule(rt, "bbb"_w, "b"_w);
      rewriting_system::add_rule(rt, "bc"_w, "b"_w);
      rewriting_system::add_rule(rt, "cb"_w, "b"_w);
      rewriting_system::add_rule(rt, "a"_w, "b"_w);

      REQUIRE(rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "003",
                            "non-confluent",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;
      rt.increase_alphabet_size_by(2);
      rewriting_system::add_rule(rt, "aaa"_w, ""_w);
      rewriting_system::add_rule(rt, "bbb"_w, ""_w);
      rewriting_system::add_rule(rt, "ababab"_w, ""_w);
      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "004",
                            "Example 5.1 in Sims (infinite)",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;
      rt.increase_alphabet_size_by(4);
      rewriting_system::add_rule(rt, "ab"_w, ""_w);
      rewriting_system::add_rule(rt, "ba"_w, ""_w);
      rewriting_system::add_rule(rt, "cd"_w, ""_w);
      rewriting_system::add_rule(rt, "dc"_w, ""_w);
      rewriting_system::add_rule(rt, "ca"_w, "ac"_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "005",
                            "non-confluent",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;

      rt.increase_alphabet_size_by(4);
      rewriting_system::add_rule(rt, "ca"_w, ""_w);
      rewriting_system::add_rule(rt, "ac"_w, ""_w);
      rewriting_system::add_rule(rt, "db"_w, ""_w);
      rewriting_system::add_rule(rt, "bd"_w, ""_w);
      rewriting_system::add_rule(rt, "ba"_w, "ab"_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "006",
                            "Example 5.3 in Sims",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;
      rt.increase_alphabet_size_by(2);
      rewriting_system::add_rule(rt, "aa"_w, ""_w);
      rewriting_system::add_rule(rt, "bbb"_w, ""_w);
      rewriting_system::add_rule(rt, "ababab"_w, ""_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "007",
                            "Example 5.4 in Sims",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;
      rt.increase_alphabet_size_by(3);

      rewriting_system::add_rule(rt, "aa"_w, ""_w);
      rewriting_system::add_rule(rt, "bc"_w, ""_w);
      rewriting_system::add_rule(rt, "bbb"_w, ""_w);
      rewriting_system::add_rule(rt, "ababab"_w, ""_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "008",
                            "Example 6.4 in Sims (size 168)",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;
      rt.increase_alphabet_size_by(3);

      rewriting_system::add_rule(rt, "aa"_w, ""_w);
      rewriting_system::add_rule(rt, "bc"_w, ""_w);
      rewriting_system::add_rule(rt, "bbb"_w, ""_w);
      rewriting_system::add_rule(rt, "ababababababab"_w, ""_w);
      rewriting_system::add_rule(rt, "abacabacabacabac"_w, ""_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "009",
                            "random example",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;

      rt.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rt, "aaa"_w, "c"_w);
      rewriting_system::add_rule(rt, "bbb"_w, "c"_w);
      rewriting_system::add_rule(rt, "ababab"_w, "c"_w);
      rewriting_system::add_rule(rt, "ac"_w, "a"_w);
      rewriting_system::add_rule(rt, "bc"_w, "b"_w);
      rewriting_system::add_rule(rt, "bc"_w, "c"_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie",
                            "010",
                            "large example",
                            "[quick]") {
      auto                rg = ReportGuard(false);
      RewritingSystemTrie rt;

      rt.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rt, "aaa"_w, "c"_w);
      rewriting_system::add_rule(rt, "bbb"_w, "c"_w);
      rewriting_system::add_rule(rt, "ababab"_w, "c"_w);
      rewriting_system::add_rule(rt, "ac"_w, "a"_w);
      rewriting_system::add_rule(rt, "bc"_w, "b"_w);
      rewriting_system::add_rule(rt, "bc"_w, "c"_w);

      REQUIRE(!rt.confluent());
    }
  }  // namespace detail
}  // namespace libsemigroups
