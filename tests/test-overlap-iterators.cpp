// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2026 James Mitchell
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

namespace libsemigroups::detail {
  using literals::operator""_w;

  LIBSEMIGROUPS_TEST_CASE("OverlapIteratorTrie",
                          "000",
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

  LIBSEMIGROUPS_TEST_CASE("OverlapIteratorTrie",
                          "001",
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

  LIBSEMIGROUPS_TEST_CASE("OverlapIteratorRules",
                          "002",
                          "basic functionality tests x1",
                          "[quick]") {
    auto                                rg = ReportGuard(false);
    RewritingSystemSet<ShortLexCompare> rws;
    rws.increase_alphabet_size_by(2);
    rewriting_system::add_rule(rws, "abba"_w, "aaa"_w);
    rewriting_system::add_rule(rws, "abab"_w, "bbb"_w);
    rws.reduce();  // Oddity #2

    REQUIRE((rws.rules() | rx::to_vector())
            == std::vector<std::pair<std::string const&, std::string const&>>(
                {{{0, 1, 0, 1}, {1, 1, 1}}, {{0, 1, 1, 0}, {0, 0, 0}}}));

    AB_BC measure;
    // TODO put this into RewritingSystemBase::next_overlap
    // and RewritingSystemBase::reset_next_overlap
    auto start = OverlapIteratorRules(rws, measure);
    auto end   = OverlapIteratorRules();
    // FIXME the following line causes the tests below to fail which shouldn't
    // be possible
    REQUIRE(std::distance(start, end) == 4);
    REQUIRE(start == end);

    REQUIRE(to_printable(start->lhs->lhs())
            == to_printable(std::string({0, 1, 0, 1})));
    REQUIRE(start->rhs->lhs() == std::string({0, 1, 0, 1}));
    REQUIRE(start->length == 2);

    ++start;
    REQUIRE(to_printable(start->lhs->lhs())
            == to_printable(std::string({0, 1, 1, 0})));
    REQUIRE(to_printable(start->rhs->lhs())
            == to_printable(std::string({0, 1, 1, 0})));
    REQUIRE(start->length == 1);

    ++start;
    REQUIRE(to_printable(start->lhs->lhs())
            == to_printable(std::string({0, 1, 1, 0})));
    REQUIRE(to_printable(start->rhs->lhs())
            == to_printable(std::string({0, 1, 0, 1})));
    REQUIRE(start->length == 1);

    ++start;
    REQUIRE(to_printable(start->lhs->lhs())
            == to_printable(std::string({0, 1, 0, 1})));
    REQUIRE(to_printable(start->rhs->lhs())
            == to_printable(std::string({0, 1, 1, 0})));
    REQUIRE(start->length == 2);

    ++start;
    REQUIRE(start == end);
  }

  LIBSEMIGROUPS_TEST_CASE("OverlapIteratorRules",
                          "003",
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

    auto                     start = OverlapIteratorRules(rws, measure);
    auto                     end   = OverlapIteratorRules();
    std::vector<std::string> found;
    for (auto it = start; it != end; ++it) {
      found.push_back(to_printable(it->lhs->lhs()));
      found.push_back(to_printable(it->rhs->lhs()));
      found.push_back(fmt::format("{}", it->length));
    }

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
    REQUIRE(start == end);
  }
}  // namespace libsemigroups::detail
