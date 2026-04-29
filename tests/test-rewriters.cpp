// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019-2026 Joseph Edwards
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

#include "Catch2-3.14.0/catch_amalgamated.hpp"  // for AssertionHandler, ope...
#include "test-main.hpp"                        // for LIBSEMIGROUPS_TEST_CASE

#include "libsemigroups/adapters.hpp"      // for ReturnFalse
#include "libsemigroups/aho-corasick.hpp"  // for dot
#include "libsemigroups/word-range.hpp"    // for operator""_w

#include "libsemigroups/detail/overlap-iterators.hpp"  // for OverlapIteratorTrie
#include "libsemigroups/detail/report.hpp"             // for ReportGuard
#include "libsemigroups/detail/rewriters.hpp"  // for RewritingSystemTrie<ShortLexCompare>

namespace std {
  std::ostream& operator<<(std::ostream& os, std::string const& value) {
    for (auto c : value) {
      if (c < 10) {
        os << int(c);
      } else {
        os << c;
      }
    }
    return os;
  }
}  // namespace std

namespace libsemigroups {
  using literals::operator""_w;

  namespace detail {

    using string_type = RewritingSystemTrie<ShortLexCompare>::native_word_type;

    using namespace std::literals;

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ShortLexCompare>",
                            "000",
                            "initial test",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;
      REQUIRE(rt.number_of_rules() == 0);
      rt.increase_alphabet_size_by(2);
      rewriting_system::add_rule(rt, "ba"_w, "a"_w);
      REQUIRE(rt.number_of_rules() == 1);
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ShortLexCompare>",
                            "001",
                            "simple test",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;

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

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemSet<ShortLexCompare>",
                            "002",
                            "simple test",
                            "[quick]") {
      using rule_type = std::pair<std::string, std::string>;

      auto rg = ReportGuard(false);

      RewritingSystemSet<ShortLexCompare> rws;

      rws.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rws, "ac"_w, "ca"_w);
      rewriting_system::add_rule(rws, "aa"_w, "a"_w);
      rewriting_system::add_rule(rws, "ac"_w, "a"_w);
      rewriting_system::add_rule(rws, "ca"_w, "a"_w);
      rewriting_system::add_rule(rws, "bb"_w, "bb"_w);
      rewriting_system::add_rule(rws, "bc"_w, "cb"_w);
      rewriting_system::add_rule(rws, "bbb"_w, "b"_w);
      rewriting_system::add_rule(rws, "bc"_w, "b"_w);
      rewriting_system::add_rule(rws, "cb"_w, "b"_w);
      rewriting_system::add_rule(rws, "a"_w, "b"_w);

      REQUIRE(rws.confluent());
      REQUIRE(rws.number_of_rules() == 4);
      REQUIRE((rws.rules()
               | rx::transform([](auto const& pair) { return rule_type(pair); })
               | rx::to_vector())
              == std::vector<std::pair<std::string, std::string>>(
                  {{{0, 0}, {0}}, {{0, 2}, {0}}, {{1}, {0}}, {{2, 0}, {0}}}));

      string_type w1 = {0, 0};
      rws.rewrite(w1);
      REQUIRE(w1 == string_type({0}));

      string_type w2 = {0, 1};
      rws.rewrite(w2);
      REQUIRE(w2 == string_type({0}));

      string_type w3 = {0, 1, 2};
      rws.rewrite(w3);
      REQUIRE(w3 == string_type({0}));

      string_type w4 = {0, 1, 2, 0};
      rws.rewrite(w4);
      REQUIRE(w4 == string_type({0}));

      string_type w5 = {2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0, 2, 1, 0, 2, 1,
                        0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1,
                        1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0};
      rws.rewrite(w5);
      REQUIRE(w5 == string_type({0}));
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ShortLexCompare>",
                            "003",
                            "confluent",
                            "[quick]") {
      using rule_type = std::pair<std::string, std::string>;
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rws;
      rws.increase_alphabet_size_by(3);

      rewriting_system::add_rule(rws, "ab"_w, "ba"_w);
      rewriting_system::add_rule(rws, "ac"_w, "ca"_w);
      rewriting_system::add_rule(rws, "aa"_w, "a"_w);
      rewriting_system::add_rule(rws, "ac"_w, "a"_w);
      rewriting_system::add_rule(rws, "ca"_w, "a"_w);
      rewriting_system::add_rule(rws, "bb"_w, "bb"_w);
      rewriting_system::add_rule(rws, "bc"_w, "cb"_w);
      rewriting_system::add_rule(rws, "bbb"_w, "b"_w);
      rewriting_system::add_rule(rws, "bc"_w, "b"_w);
      rewriting_system::add_rule(rws, "cb"_w, "b"_w);
      rewriting_system::add_rule(rws, "a"_w, "b"_w);

      REQUIRE(rws.number_of_rules() == 10);
      rewriting_system::add_rule(rws, "a"_w, "a"_w);
      REQUIRE(rws.number_of_rules() == 10);

      REQUIRE(rws.confluent());
      REQUIRE((rws.rules()
               | rx::transform([](auto const& pair) { return rule_type(pair); })
               | rx::to_vector())
              == std::vector<std::pair<std::string, std::string>>(
                  {{{0, 0}, {0}}, {{0, 2}, {0}}, {{1}, {0}}, {{2, 0}, {0}}}));
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ShortLexCompare>",
                            "004",
                            "non-confluent",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;
      rt.increase_alphabet_size_by(2);
      rewriting_system::add_rule(rt, "aaa"_w, ""_w);
      rewriting_system::add_rule(rt, "bbb"_w, ""_w);
      rewriting_system::add_rule(rt, "ababab"_w, ""_w);
      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ShortLexCompare>",
                            "005",
                            "Example 5.1 in Sims (infinite)",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;
      rt.increase_alphabet_size_by(4);
      rewriting_system::add_rule(rt, "ab"_w, ""_w);
      rewriting_system::add_rule(rt, "ba"_w, ""_w);
      rewriting_system::add_rule(rt, "cd"_w, ""_w);
      rewriting_system::add_rule(rt, "dc"_w, ""_w);
      rewriting_system::add_rule(rt, "ca"_w, "ac"_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ShortLexCompare>",
                            "006",
                            "non-confluent",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;

      rt.increase_alphabet_size_by(4);
      rewriting_system::add_rule(rt, "ca"_w, ""_w);
      rewriting_system::add_rule(rt, "ac"_w, ""_w);
      rewriting_system::add_rule(rt, "db"_w, ""_w);
      rewriting_system::add_rule(rt, "bd"_w, ""_w);
      rewriting_system::add_rule(rt, "ba"_w, "ab"_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ShortLexCompare>",
                            "007",
                            "Example 5.3 in Sims",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;
      rt.increase_alphabet_size_by(2);
      rewriting_system::add_rule(rt, "aa"_w, ""_w);
      rewriting_system::add_rule(rt, "bbb"_w, ""_w);
      rewriting_system::add_rule(rt, "ababab"_w, ""_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ShortLexCompare>",
                            "008",
                            "Example 5.4 in Sims",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;
      rt.increase_alphabet_size_by(3);

      rewriting_system::add_rule(rt, "aa"_w, ""_w);
      rewriting_system::add_rule(rt, "bc"_w, ""_w);
      rewriting_system::add_rule(rt, "bbb"_w, ""_w);
      rewriting_system::add_rule(rt, "ababab"_w, ""_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ShortLexCompare>",
                            "009",
                            "Example 6.4 in Sims (size 168)",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;
      rt.increase_alphabet_size_by(3);

      rewriting_system::add_rule(rt, "aa"_w, ""_w);
      rewriting_system::add_rule(rt, "bc"_w, ""_w);
      rewriting_system::add_rule(rt, "bbb"_w, ""_w);
      rewriting_system::add_rule(rt, "ababababababab"_w, ""_w);
      rewriting_system::add_rule(rt, "abacabacabacabac"_w, ""_w);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ShortLexCompare>",
                            "010",
                            "random example",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;

      rt.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rt, "aaa"_w, "c"_w);
      rewriting_system::add_rule(rt, "bbb"_w, "c"_w);
      rewriting_system::add_rule(rt, "ababab"_w, "c"_w);
      rewriting_system::add_rule(rt, "ac"_w, "a"_w);
      rewriting_system::add_rule(rt, "bc"_w, "b"_w);
      rewriting_system::add_rule(rt, "bc"_w, "c"_w);

      REQUIRE(rt.number_of_rules() == 6);

      REQUIRE(!rt.confluent());
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ReturnFalse>",
                            "011",
                            "not obviously terminating example",
                            "[quick]") {
      using rule_type                     = std::pair<std::string, std::string>;
      auto                             rg = ReportGuard(false);
      RewritingSystemTrie<ReturnFalse> rws;

      rws.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rws, "aaa"_w, "c"_w);
      rewriting_system::add_rule(rws, "c"_w, "bbb"_w);
      rewriting_system::add_rule(rws, "ababab"_w, "c"_w);
      rewriting_system::add_rule(rws, "a"_w, "ac"_w);
      rewriting_system::add_rule(rws, "bc"_w, "b"_w);
      rewriting_system::add_rule(rws, "bc"_w, "c"_w);

      REQUIRE((rws.rules()
               | rx::transform([](auto const& pair) { return rule_type(pair); })
               | rx::to_vector())
              == std::vector<rule_type>({{{0, 0, 0}, {2}},
                                         {{2}, {1, 1, 1}},
                                         {{0, 1, 0, 1, 0, 1}, {2}},
                                         {{0}, {0, 2}},
                                         {{1, 2}, {1}},
                                         {{1, 2}, {2}}}));
      REQUIRE(rewriting_system::is_length_decreasing_no_reduce(rws)
              == tril::unknown);
      REQUIRE(rewriting_system::is_terminating_no_reduce(rws) == tril::unknown);
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystemTrie<ReturnFalse>",
                            "012",
                            "not obviously terminating example",
                            "[quick]") {
      using rule_type                     = std::pair<std::string, std::string>;
      auto                             rg = ReportGuard(false);
      RewritingSystemTrie<ReturnFalse> rws;

      rws.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rws, "aa"_w, "bbb"_w);
      rewriting_system::add_rule(rws, "bbb"_w, "ccc"_w);

      REQUIRE((rws.rules()
               | rx::transform([](auto const& pair) { return rule_type(pair); })
               | rx::sort() | rx::to_vector())
              == std::vector<rule_type>(
                  {{{0, 0}, {1, 1, 1}}, {{1, 1, 1}, {2, 2, 2}}}));
      rws.reduce();
      REQUIRE((rws.rules()
               | rx::transform([](auto const& pair) { return rule_type(pair); })
               | rx::sort() | rx::to_vector())
              == std::vector<rule_type>(
                  {{{0, 0}, {2, 2, 2}}, {{1, 1, 1}, {2, 2, 2}}}));
      REQUIRE(!rws.confluent());

      REQUIRE(!rewriting_system::is_length_decreasing(rws));
      REQUIRE(rewriting_system::is_terminating(rws) == tril::unknown);

      std::string w({0, 0});
      rws.rewrite(w);
      REQUIRE(w == std::string({2, 2, 2}));
      REQUIRE(rewriting_system::is_terminating(rws) == tril::unknown);
    }

    LIBSEMIGROUPS_TEST_CASE("Rules", "013", "constructors/init", "[quick]") {
      Rules rules1;

      Rules rules2(rules1);
      Rules rules3(std::move(rules1));
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystem",
                            "014",
                            "constructors/init",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rws;

      rws.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rws, "aaa"_w, "c"_w);
      rewriting_system::add_rule(rws, "c"_w, "bbb"_w);
      rewriting_system::add_rule(rws, "ababab"_w, "c"_w);
      rewriting_system::add_rule(rws, "a"_w, "ac"_w);
      rewriting_system::add_rule(rws, "bc"_w, "b"_w);
      rewriting_system::add_rule(rws, "bc"_w, "c"_w);
      REQUIRE(rws.number_of_rules() == 6);

      rws.init();
      REQUIRE(rws.number_of_rules() == 0);
      REQUIRE(rws.trie().number_of_nodes() == 1);
      REQUIRE(rewriting_system::is_length_decreasing(rws));
      REQUIRE(rewriting_system::is_terminating(rws) == tril::TRUE);

      rws.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rws, "aaa"_w, "c"_w);
      rewriting_system::add_rule(rws, "bbb"_w, "c"_w);
      rewriting_system::add_rule(rws, "ababab"_w, "c"_w);
      rewriting_system::add_rule(rws, "ac"_w, "a"_w);
      rewriting_system::add_rule(rws, "bc"_w, "b"_w);
      rewriting_system::add_rule(rws, "bc"_w, "c"_w);

      auto copy = rws;
      REQUIRE(rws.number_of_rules() == 6);
      REQUIRE(!rws.confluent());
      REQUIRE(copy.number_of_rules() == 6);
      REQUIRE(!copy.confluent());

      copy = rws;
      REQUIRE(rws.number_of_rules() == 4);
      REQUIRE(!rws.confluent());
      REQUIRE(copy.number_of_rules() == 4);
      REQUIRE(!copy.confluent());

      rws.init();
      copy = std::move(rws);
      REQUIRE(copy.number_of_rules() == 0);
      REQUIRE(copy.trie().number_of_nodes() == 1);

      copy.increase_alphabet_size_by(3);
      rewriting_system::add_rule(copy, "aaa"_w, "c"_w);
      rewriting_system::add_rule(copy, "bbb"_w, "c"_w);
      rewriting_system::add_rule(copy, "ababab"_w, "c"_w);
      rewriting_system::add_rule(copy, "ac"_w, "a"_w);
      rewriting_system::add_rule(copy, "bc"_w, "b"_w);
      rewriting_system::add_rule(copy, "bc"_w, "c"_w);

      auto other_copy(copy);
      REQUIRE(copy.number_of_rules() == 6);
      REQUIRE(copy.trie().number_of_nodes() == 1);
      REQUIRE(other_copy.number_of_rules() == 6);
      REQUIRE(other_copy.trie().number_of_nodes() == 1);

      auto other_other_copy(std::move(copy));
      REQUIRE(other_other_copy.number_of_rules() == 6);
      REQUIRE(other_other_copy.trie().number_of_nodes() == 1);
    }

    LIBSEMIGROUPS_TEST_CASE("RewritingSystem",
                            "015",
                            "is_terminating",
                            "[quick]") {
      RewritingSystemTrie<ReturnFalse> rws;
      rws.increase_alphabet_size_by(3);
      rewriting_system::add_rule(rws, "bbb"_w, "aa"_w);
      rewriting_system::add_rule(rws, "bbb"_w, "ccc"_w);
      REQUIRE(rewriting_system::is_terminating_no_reduce(rws) == tril::unknown);
      REQUIRE(rws.is_reduced() == tril::unknown);
      REQUIRE(rewriting_system::is_terminating(rws) == tril::TRUE);
      REQUIRE(rws.is_reduced() == tril::TRUE);
    }

    LIBSEMIGROUPS_TEST_CASE("OverlapIteratorTrie",
                            "016",
                            "basic overlaps",
                            "[quick]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;
      rt.increase_alphabet_size_by(2);
      rewriting_system::add_rule(rt, "abba"_w, "aaa"_w);
      rewriting_system::add_rule(rt, "abab"_w, "bbb"_w);
      rt.reduce();

      auto const& trie = rt.trie();

      auto start = OverlapIteratorTrie(trie);
      auto end   = OverlapIteratorTrie();

      REQUIRE(start->lhs->lhs() == std::string({0, 1, 1, 0}));
      REQUIRE(start->lhs->rhs() == std::string({0, 0, 0}));
      REQUIRE(start->rhs->lhs() == std::string({0, 1, 1, 0}));
      REQUIRE(start->rhs->rhs() == std::string({0, 0, 0}));
      REQUIRE(start->length == 1);

      ++start;
      REQUIRE(start->lhs->lhs() == std::string({0, 1, 1, 0}));
      REQUIRE(start->lhs->rhs() == std::string({0, 0, 0}));
      REQUIRE(start->rhs->lhs() == std::string({0, 1, 0, 1}));
      REQUIRE(start->rhs->rhs() == std::string({1, 1, 1}));
      REQUIRE(start->length == 1);

      ++start;
      REQUIRE(start->lhs->lhs() == std::string({0, 1, 0, 1}));
      REQUIRE(start->lhs->rhs() == std::string({1, 1, 1}));
      REQUIRE(start->rhs->lhs() == std::string({0, 1, 1, 0}));
      REQUIRE(start->rhs->rhs() == std::string({0, 0, 0}));
      REQUIRE(start->length == 2);

      ++start;
      REQUIRE(start->lhs->lhs() == std::string({0, 1, 0, 1}));
      REQUIRE(start->lhs->rhs() == std::string({1, 1, 1}));
      REQUIRE(start->rhs->lhs() == std::string({0, 1, 0, 1}));
      REQUIRE(start->rhs->rhs() == std::string({1, 1, 1}));
      REQUIRE(start->length == 2);

      ++start;
      REQUIRE(start == end);
    }

    // TODO after JDM merged JE's PR this test did not pass
    LIBSEMIGROUPS_TEST_CASE("OverlapIteratorTrie",
                            "017",
                            "different generations",
                            "[fail]") {
      auto                                 rg = ReportGuard(false);
      RewritingSystemTrie<ShortLexCompare> rt;
      rt.increase_alphabet_size_by(2);

      // Words added in generation 0
      rewriting_system::add_rule(rt, "abba"_w, "aaa"_w);
      rewriting_system::add_rule(rt, "abab"_w, "bbb"_w);
      rt.reduce();

      // Word added in generation 1
      rt.trie().increment_generation();
      rewriting_system::add_rule(rt, "baa"_w, "a"_w);
      rt.reduce();

      {
        auto const& trie = rt.trie();

        // Should only find the overlaps between
        auto start = OverlapIteratorTrie(trie);
        auto end   = OverlapIteratorTrie();

        v4::ToWord toword(std::string({0, 1}));

        REQUIRE(toword(start->lhs->lhs()) == "baa"_w);
        REQUIRE(toword(start->lhs->rhs()) == "a"_w);
        REQUIRE(toword(start->rhs->lhs()) == "abba"_w);
        REQUIRE(toword(start->rhs->rhs()) == "aaa"_w);
        REQUIRE(start->length == 1);

        ++start;
        REQUIRE(toword(start->lhs->lhs()) == "baa"_w);
        REQUIRE(toword(start->lhs->rhs()) == "a"_w);
        REQUIRE(toword(start->rhs->lhs()) == "abab"_w);
        REQUIRE(toword(start->rhs->rhs()) == "bbb"_w);
        REQUIRE(start->length == 1);

        ++start;
        REQUIRE(toword(start->lhs->lhs()) == "abba"_w);
        REQUIRE(toword(start->lhs->rhs()) == "aaa"_w);
        REQUIRE(toword(start->rhs->lhs()) == "baa"_w);
        REQUIRE(toword(start->rhs->rhs()) == "a"_w);
        REQUIRE(start->length == 2);

        ++start;
        REQUIRE(toword(start->lhs->lhs()) == "abab"_w);
        REQUIRE(toword(start->lhs->rhs()) == "bbb"_w);
        REQUIRE(toword(start->rhs->lhs()) == "baa"_w);
        REQUIRE(toword(start->rhs->rhs()) == "a"_w);
        REQUIRE(start->length == 1);

        ++start;
        REQUIRE(start == end);
      }

      rt.increase_alphabet_size_by(1);

      // Word added in generation 2
      rt.trie().increment_generation();
      rewriting_system::add_rule(rt, "c"_w, "b"_w);
      rt.reduce();

      // No overlaps where at least one word is in generation 2
      REQUIRE(OverlapIteratorTrie(rt.trie()) == OverlapIteratorTrie());
    }

    LIBSEMIGROUPS_TEST_CASE("Rules::Overlaps",
                            "019",
                            "basic functionality tests x1",
                            "[quick]") {
      auto                                rg = ReportGuard(false);
      RewritingSystemSet<ShortLexCompare> rws;
      rws.increase_alphabet_size_by(2);
      rewriting_system::add_rule(rws, "abba"_w, "aaa"_w);
      rewriting_system::add_rule(rws, "abab"_w, "bbb"_w);
      rws.reduce();

      REQUIRE((rws.rules() | rx::to_vector())
              == std::vector<std::pair<std::string const&, std::string const&>>(
                  {{{0, 1, 0, 1}, {1, 1, 1}}, {{0, 1, 1, 0}, {0, 0, 0}}}));

      AB_BC measure;

      auto& overlaps = rws.overlaps();

      // REQUIRE(std::distance(start, end) == 4);
      // REQUIRE(start == end);

      REQUIRE(!overlaps.at_end());

      REQUIRE(to_printable(overlaps.get().lhs->lhs())
              == to_printable(std::string({0, 1, 0, 1})));
      REQUIRE(overlaps.get().rhs->lhs() == std::string({0, 1, 0, 1}));
      REQUIRE(overlaps.get().length == 2);

      overlaps.next();
      REQUIRE(to_printable(overlaps.get().lhs->lhs())
              == to_printable(std::string({0, 1, 1, 0})));
      REQUIRE(to_printable(overlaps.get().rhs->lhs())
              == to_printable(std::string({0, 1, 1, 0})));
      REQUIRE(overlaps.get().length == 1);

      overlaps.next();
      REQUIRE(to_printable(overlaps.get().lhs->lhs())
              == to_printable(std::string({0, 1, 1, 0})));
      REQUIRE(to_printable(overlaps.get().rhs->lhs())
              == to_printable(std::string({0, 1, 0, 1})));
      REQUIRE(overlaps.get().length == 1);

      overlaps.next();
      REQUIRE(to_printable(overlaps.get().lhs->lhs())
              == to_printable(std::string({0, 1, 0, 1})));
      REQUIRE(to_printable(overlaps.get().rhs->lhs())
              == to_printable(std::string({0, 1, 1, 0})));
      REQUIRE(overlaps.get().length == 2);

      overlaps.next();
      REQUIRE(overlaps.at_end());
    }

    LIBSEMIGROUPS_TEST_CASE("Rules::Overlaps",
                            "020",
                            "basic functionality tests x2",
                            "[quick]") {
      auto                                rg = ReportGuard(false);
      RewritingSystemSet<ShortLexCompare> rws;
      rws.increase_alphabet_size_by(2);
      rewriting_system::add_rule(rws, "aaaaaaaaaa"_w, "aaa"_w);
      rewriting_system::add_rule(rws, "aaabaaa"_w, "bbb"_w);
      rws.reduce();
      // The iterator only works if the system is reduced (o/w the
      // rules are just pending)

      AB_BC measure;

      auto& overlaps = rws.overlaps();

      std::vector<std::string> found;
      while (!overlaps.at_end()) {
        found.push_back(to_printable(overlaps.get().lhs->lhs()));
        found.push_back(to_printable(overlaps.get().rhs->lhs()));
        found.push_back(fmt::format("{}", overlaps.get().length));
        overlaps.next();
      }
      REQUIRE(overlaps.at_end());

      REQUIRE(found
              == std::vector<std::string>(
                  {"(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "1",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "2",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "3",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "4",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "5",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "6",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "7",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "8",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "9",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "1",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "2",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "3",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "1",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "2",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "3",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "1",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "2",
                   "(char values) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]",
                   "(char values) [0, 0, 0, 1, 0, 0, 0]",
                   "3"}));
    }

  }  // namespace detail
}  // namespace libsemigroups
