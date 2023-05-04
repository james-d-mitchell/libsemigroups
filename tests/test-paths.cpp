//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2023 J. D. Mitchell
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
//

#include <algorithm>      // for all_of
#include <cmath>          // for pow
#include <cstddef>        // for size_t
#include <cstdint>        // for uint64_t
#include <iterator>       // for begin, end
#include <memory>         // for shared_ptr
#include <random>         // for mt19937
#include <stdexcept>      // for runtime_error
#include <type_traits>    // for remove_extent_t
#include <unordered_set>  // for unordered_set
#include <utility>        // for swap
#include <vector>         // for vector, operator==

#include "catch.hpp"                   // for operator""_catch_sr
#include "test-main.hpp"               // for LIBSEMIGROUPS_TEST_CASE
#include "word-graph-test-common.hpp"  // for binary_tree

#include "libsemigroups/config.hpp"             // for LIBSEMIGROUPS_EIGEN_E...
#include "libsemigroups/constants.hpp"          // for operator!=, operator==
#include "libsemigroups/exception.hpp"          // for LibsemigroupsException
#include "libsemigroups/froidure-pin-base.hpp"  // for FroidurePinBase
#include "libsemigroups/knuth-bendix.hpp"       // for KnuthBendix
#include "libsemigroups/order.hpp"              // for LexicographicalCompare
#include "libsemigroups/paths.hpp"              // for Paths, const_pstilo_i...
#include "libsemigroups/ranges.hpp"             // for equal, is_sorted
#include "libsemigroups/detail/report.hpp"             // for ReportGuard
#include "libsemigroups/detail/stl.hpp"                // for hash
#include "libsemigroups/to-froidure-pin.hpp"
#include "libsemigroups/types.hpp"       // for word_type, relation_type
#include "libsemigroups/word-graph.hpp"  // for WordGraph, make, pow
#include "libsemigroups/words.hpp"       // for operator""_w, Words

#include "rx/ranges.hpp"  // for operator|, begin, end

namespace libsemigroups {

  using namespace literals;
  using namespace rx;

  struct LibsemigroupsException;  // forward decl

  namespace {
    void add_chain(WordGraph<size_t>& digraph, size_t n) {
      size_t old_nodes = digraph.number_of_nodes();
      digraph.add_nodes(n);
      for (size_t i = old_nodes; i < digraph.number_of_nodes() - 1; ++i) {
        digraph.set_target(i, 0, i + 1);
      }
    }

    WordGraph<size_t> chain(size_t n) {
      WordGraph<size_t> g(0, 1);
      add_chain(g, n);
      return g;
    }
  }  // namespace

  LIBSEMIGROUPS_TEST_CASE("Paths", "000", "100 node path", "[quick]") {
    WordGraph<size_t> ad;
    size_t const      n = 100;
    ad.add_nodes(n);
    ad.add_to_out_degree(2);
    for (size_t i = 0; i < n - 1; ++i) {
      ad.set_target(i, i % 2, i + 1);
    }

    Paths p(ad);
    p.order(Order::lex).from(0);

    REQUIRE((p | count()) == 100);

    p.from(50);
    REQUIRE((p | count()) == 50);

    p.from(0);
    REQUIRE(begin(p) != end(p));

    p.order(Order::shortlex);
    REQUIRE((p | count()) == 100);
    REQUIRE((p | skip_n(3)).get() == 010_w);

    p.from(50);
    REQUIRE((p | count()) == 50);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths", "001", "#1", "[quick]") {
    using namespace rx;

    auto ad = to_word_graph<size_t>(9,
                                    {{1, 2, UNDEFINED},
                                     {},
                                     {3, 4, 6},
                                     {},
                                     {UNDEFINED, 5},
                                     {},
                                     {UNDEFINED, 7},
                                     {8},
                                     {}});

    Paths p(ad);
    p.order(Order::shortlex).from(2).min(3).max(4);

    std::vector<word_type> expected = {{2, 1, 0}};
    REQUIRE((p | count()) == 1);
    REQUIRE(p.get() == expected[0]);

    p.from(0).min(0).max(0);
    REQUIRE(p.from() == 0);
    REQUIRE(p.to() == UNDEFINED);

    REQUIRE(p.min() == 0);
    REQUIRE(p.max() == 0);
    REQUIRE(p.order() == Order::shortlex);
    REQUIRE(p.at_end());
    REQUIRE(p.size_hint() == 0);
    REQUIRE((p | count()) == 0);

    p.min(0).max(1);
    expected = {""_w};
    REQUIRE((p | count()) == 1);
    REQUIRE((p | to_vector()) == expected);

    p.min(0).max(2);
    expected = {""_w, 0_w, 1_w};
    REQUIRE((p | to_vector()) == expected);

    expected = {""_w, 0_w, 1_w, 10_w, 11_w, 12_w};
    p.min(0).max(3);
    REQUIRE((p | to_vector()) == expected);

    expected = {""_w, 0_w, 1_w, 10_w, 11_w, 12_w, 111_w, 121_w};
    p.min(0).max(4);
    REQUIRE((p | to_vector()) == expected);

    expected = {""_w, 0_w, 1_w, 10_w, 11_w, 12_w, 111_w, 121_w, 1210_w};
    p.min(0).max(10);
    REQUIRE((p | to_vector()) == expected);

    expected = {10_w, 11_w, 12_w};
    p.min(2).max(3);
    REQUIRE((p | to_vector()) == expected);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths", "002", "100 node cycle", "[quick]") {
    WordGraph<size_t> ad;
    ad.add_to_out_degree(1);
    word_graph::add_cycle(ad, 100);

    Paths p(ad);

    p.order(Order::lex).from(0).max(200);
    REQUIRE((p | count()) == 200);

    p.order(Order::shortlex);
    REQUIRE((p | count()) == 200);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths", "003", "#2", "[quick]") {
    using namespace rx;

    WordGraph<size_t> ad = to_word_graph<size_t>(
        15, {{1, 2}, {3, 4}, {5, 6}, {7, 8}, {9, 10}, {11, 12}, {13, 14}});

    Paths p(ad);

    p.order(Order::lex).from(0).min(0).max(3);
    REQUIRE((p | count()) == 7);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({{}, 0_w, 00_w, 01_w, 1_w, 10_w, 11_w}));
    REQUIRE((p | count()) == 7);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({{}, 0_w, 00_w, 01_w, 1_w, 10_w, 11_w}));

    p.order(Order::shortlex).from(0).min(0).max(3);
    REQUIRE((p | count()) == 7);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({{}, 0_w, 1_w, 00_w, 01_w, 10_w, 11_w}));
    REQUIRE((p | count()) == 7);

    p.order(Order::shortlex);
    REQUIRE((p | count()) == 7);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({{}, 0_w, 1_w, 00_w, 01_w, 10_w, 11_w}));

    p.init(ad).order(Order::lex).from(0);
    REQUIRE((p | count()) == 15);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({{},
                                       0_w,
                                       00_w,
                                       000_w,
                                       001_w,
                                       01_w,
                                       010_w,
                                       011_w,
                                       1_w,
                                       10_w,
                                       100_w,
                                       101_w,
                                       11_w,
                                       110_w,
                                       111_w}));

    p.order(Order::shortlex);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({{},
                                       0_w,
                                       1_w,
                                       00_w,
                                       01_w,
                                       10_w,
                                       11_w,
                                       000_w,
                                       001_w,
                                       010_w,
                                       011_w,
                                       100_w,
                                       101_w,
                                       110_w,
                                       111_w}));

    p.order(Order::lex).min(1);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({0_w,
                                       00_w,
                                       000_w,
                                       001_w,
                                       01_w,
                                       010_w,
                                       011_w,
                                       1_w,
                                       10_w,
                                       100_w,
                                       101_w,
                                       11_w,
                                       110_w,
                                       111_w}));

    p.order(Order::shortlex);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({0_w,
                                       1_w,
                                       00_w,
                                       01_w,
                                       10_w,
                                       11_w,
                                       000_w,
                                       001_w,
                                       010_w,
                                       011_w,
                                       100_w,
                                       101_w,
                                       110_w,
                                       111_w}));
    p.order(Order::lex).from(2).min(1);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({0_w, 00_w, 01_w, 1_w, 10_w, 11_w}));

    p.order(Order::shortlex);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({0_w, 1_w, 00_w, 01_w, 10_w, 11_w}));

    p.order(Order::lex).from(2).min(2).max(3);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({00_w, 01_w, 10_w, 11_w}));

    p.order(Order::shortlex);
    REQUIRE((p | to_vector())
            == std::vector<word_type>({00_w, 01_w, 10_w, 11_w}));
  }

  LIBSEMIGROUPS_TEST_CASE("Paths", "004", "#3", "[quick]") {
    using namespace rx;
    auto ad = to_word_graph<size_t>(
        6, {{1, 2}, {3, 4}, {4, 2}, {1, 5}, {5, 4}, {4, 5}});

    std::vector<word_type> expected = {01_w,
                                       10_w,
                                       011_w,
                                       110_w,
                                       101_w,
                                       1101_w,
                                       1011_w,
                                       1110_w,
                                       0111_w,
                                       1000_w,
                                       0001_w,
                                       0010_w,
                                       0100_w};

    std::sort(expected.begin(), expected.end(), ShortLexCompare());

    Paths p(ad);
    p.order(Order::shortlex).from(0).to(4).min(0).max(5);

    REQUIRE((p | count()) == 13);
    REQUIRE((p | count()) == 13);
    REQUIRE((p | to_vector()) == expected);
    REQUIRE((p | take(1)).get() == 01_w);

    std::sort(expected.begin(), expected.end(), LexicographicalCompare());
    p.order(Order::lex);

    REQUIRE((p | to_vector()) == expected);
    REQUIRE((p | take(1)).get() == 0001_w);

    size_t const N = 18;

    Words w;

    auto expected2 = (w.letters(2).min(0).max(N) | filter([&ad](auto const& w) {
                        return word_graph::follow_path(ad, 0, w) == 4;
                      }));
    REQUIRE((expected2 | count()) == 131'062);

    p.order(Order::shortlex).max(N);
    REQUIRE((p | count()) == 131'062);
    REQUIRE(equal(p, expected2));
    p.to(UNDEFINED);
    REQUIRE((p | count()) == 262'143);

    REQUIRE(number_of_paths(ad, 0, 4, 0, N) == 131'062);
    REQUIRE(number_of_paths(ad, 0, 4, 10, N) == 130'556);
    REQUIRE(number_of_paths(ad, 4, 1, 0, N) == 0);
    REQUIRE(number_of_paths(ad, 0, 0, POSITIVE_INFINITY) == POSITIVE_INFINITY);
    REQUIRE(number_of_paths(ad, 0, 0, 10) == 1'023);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths", "005", "#4", "[quick]") {
    using word_graph::follow_path;
    using namespace rx;

    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule(p, "aaaaa", "aa");
    presentation::add_rule(p, "bb", "b");
    presentation::add_rule(p, "ab", "b");

    KnuthBendix kb(congruence_kind::twosided, p);
    REQUIRE(kb.number_of_classes() == 9);
    auto S = to_froidure_pin(kb);

    WordGraph<size_t> ad(S.right_cayley_graph());
    ad.add_nodes(1);

    REQUIRE(ad.number_of_nodes() == 10);
    REQUIRE(ad.number_of_edges() == 18);
    // FIXME Probably an uint32_t(UNDEFINED) versus size_t(UNDEFINED) issue
    ad.set_target(S.size(), 0, 0);
    ad.set_target(S.size(), 1, 1);

    REQUIRE(ad.number_of_edges() == 20);
    REQUIRE(word_graph::number_of_nodes_reachable_from(ad, S.size()) == 10);

    Paths paths(ad);
    paths.order(Order::lex).from(S.size()).min(0).max(9);
    REQUIRE(paths.to(0).get() == 0_w);

    auto tprime = (seq() | first_n(S.size())
                   | transform([&paths](auto i) { return paths.to(i).get(); })
                   | to_vector());

    REQUIRE(tprime.size() == 9);
    REQUIRE(tprime
            == std::vector<word_type>({0_w,
                                       00000001_w,
                                       00_w,
                                       00000010_w,
                                       000_w,
                                       00000100_w,
                                       0000_w,
                                       00001000_w,
                                       00010000_w}));

    std::vector<word_type> lprime = {00000_w,
                                     000000010_w,
                                     000000011_w,
                                     000000100_w,
                                     000000101_w,
                                     000001000_w,
                                     000001001_w,
                                     00001_w,
                                     000010000_w,
                                     000010001_w,
                                     0001_w,
                                     000100000_w,
                                     000100001_w,
                                     001_w,
                                     01_w};

    REQUIRE(lprime.size() == 15);
    REQUIRE(std::is_sorted(
        lprime.cbegin(), lprime.cend(), LexicographicalCompare()));

    auto rhs = (seq() | first_n(lprime.size()) | transform([&](auto i) {
                  return tprime[follow_path(ad, S.size(), lprime[i])];
                })
                | to_vector());

    REQUIRE(rhs
            == std::vector<word_type>({00_w,
                                       00000010_w,
                                       00000001_w,
                                       00000100_w,
                                       00000001_w,
                                       00001000_w,
                                       00000001_w,
                                       00000001_w,
                                       00010000_w,
                                       00000001_w,
                                       00000001_w,
                                       00000100_w,
                                       00000001_w,
                                       00000001_w,
                                       00000001_w}));
    for (size_t i = 0; i < lprime.size(); ++i) {
      REQUIRE(kb.contains(lprime[i], rhs[i]));
    }

    KnuthBendix kb2(congruence_kind::twosided, p);
    for (size_t i = 0; i < lprime.size(); ++i) {
      kb2.add_pair(lprime[i], rhs[i]);
    }
    kb2.add_pair(1_w, 00000001_w);
    REQUIRE(kb2.number_of_classes() == 9);
    auto T = to_froidure_pin(kb2);
    T.run();
    REQUIRE(std::vector<relation_type>(T.cbegin_rules(), T.cend_rules())
            == std::vector<relation_type>(
                {{01_w, 1_w}, {11_w, 1_w}, {00000_w, 00_w}}));
  }

  LIBSEMIGROUPS_TEST_CASE("Paths", "006", "#5", "[quick]") {
    using namespace rx;
    auto ad = to_word_graph<size_t>(
        6, {{1, 2}, {3, 4}, {4, 2}, {1, 5}, {5, 4}, {4, 5}});

    std::vector<word_type> expected = {01_w,
                                       10_w,
                                       011_w,
                                       110_w,
                                       101_w,
                                       1101_w,
                                       1011_w,
                                       1110_w,
                                       0111_w,
                                       1000_w,
                                       0001_w,
                                       0010_w,
                                       0100_w};

    std::sort(expected.begin(), expected.end(), ShortLexCompare());

    Paths p(ad);
    p.order(Order::shortlex).from(0).to(4).min(0).max(5);
    REQUIRE((p | to_vector()) == expected);

    size_t const N = 18;

    Words w;
    expected = (w.letters(2).min(0).max(N) | filter([&ad](auto const& w) {
                  return word_graph::follow_path(ad, 0, w) == 4;
                })
                | to_vector());
    REQUIRE(expected.size() == 131'062);

    p.order(Order::shortlex).from(0).to(4).min(0).max(N);
    REQUIRE((p | count()) == 131'062);
    REQUIRE((p | to_vector()) == expected);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths", "007", "#6", "[quick]") {
    using namespace rx;
    auto ad = to_word_graph<size_t>(6,
                                    {{1, 2, UNDEFINED},
                                     {2, 0, 3},
                                     {UNDEFINED, UNDEFINED, 3},
                                     {4},
                                     {UNDEFINED, 5},
                                     {3}});

    Paths p(ad);
    p.order(Order::shortlex).from(0).min(0).max(10);

    REQUIRE(is_sorted(p, ShortLexCompare()));
    REQUIRE((p | count()) == 75);
    REQUIRE(p.count() == 75);
    p.max(POSITIVE_INFINITY);
    REQUIRE(p.count() == POSITIVE_INFINITY);

    p.max(10);
    REQUIRE(
        (p | to_vector())
        == std::vector<word_type>(
            {{},          0_w,         1_w,         00_w,        01_w,
             02_w,        12_w,        002_w,       010_w,       011_w,
             020_w,       120_w,       0020_w,      0100_w,      0101_w,
             0102_w,      0112_w,      0201_w,      1201_w,      00201_w,
             01002_w,     01010_w,     01011_w,     01020_w,     01120_w,
             02010_w,     12010_w,     002010_w,    010020_w,    010100_w,
             010101_w,    010102_w,    010112_w,    010201_w,    011201_w,
             020100_w,    120100_w,    0020100_w,   0100201_w,   0101002_w,
             0101010_w,   0101011_w,   0101020_w,   0101120_w,   0102010_w,
             0112010_w,   0201001_w,   1201001_w,   00201001_w,  01002010_w,
             01010020_w,  01010100_w,  01010101_w,  01010102_w,  01010112_w,
             01010201_w,  01011201_w,  01020100_w,  01120100_w,  02010010_w,
             12010010_w,  002010010_w, 010020100_w, 010100201_w, 010101002_w,
             010101010_w, 010101011_w, 010101020_w, 010101120_w, 010102010_w,
             010112010_w, 010201001_w, 011201001_w, 020100100_w, 120100100_w}));

    auto expected = p | to_vector();
    std::sort(expected.begin(), expected.end(), LexicographicalCompare());
    REQUIRE(expected == (p.order(Order::lex) | to_vector()));
  }

  LIBSEMIGROUPS_TEST_CASE("Paths",
                          "008",
                          "path iterators corner cases",
                          "[quick]") {
    auto ad = to_word_graph<size_t>(6,
                                    {{1, 2, UNDEFINED},
                                     {2, 0, 3},
                                     {UNDEFINED, UNDEFINED, 3},
                                     {4},
                                     {UNDEFINED, 5},
                                     {3}});

    REQUIRE_THROWS_AS(cbegin_pstilo(ad, 1, 6), LibsemigroupsException);
    REQUIRE_THROWS_AS(cbegin_pstilo(ad, 6, 1), LibsemigroupsException);
    REQUIRE(cbegin_pstilo(ad, 2, 1) == cend_pstilo(ad));
    REQUIRE(cbegin_pstilo(ad, 0, 3, 10, 1) == cend_pstilo(ad));

    REQUIRE_THROWS_AS(cbegin_pstislo(ad, 1, 6), LibsemigroupsException);
    REQUIRE_THROWS_AS(cbegin_pstislo(ad, 6, 1), LibsemigroupsException);
    REQUIRE(cbegin_pstislo(ad, 2, 1) == cend_pstislo(ad));
    REQUIRE(cbegin_pstislo(ad, 0, 3, 10, 1) == cend_pstislo(ad));

    REQUIRE_THROWS_AS(cbegin_pilo(ad, 6), LibsemigroupsException);
    REQUIRE(cbegin_pilo(ad, 0, 1, 1) == cend_pilo(ad));
    REQUIRE_THROWS_AS(cbegin_pislo(ad, 6), LibsemigroupsException);
    REQUIRE(cbegin_pislo(ad, 0, 1, 1) == cend_pislo(ad));

    REQUIRE_THROWS_AS(cbegin_pilo(ad, 6), LibsemigroupsException);
    REQUIRE(cbegin_pilo(ad, 0, 1, 1) == cend_pilo(ad));

    REQUIRE_THROWS_AS(cbegin_pislo(ad, 6), LibsemigroupsException);
    REQUIRE(cbegin_pislo(ad, 0, 1, 1) == cend_pislo(ad));

    verify_forward_iterator_requirements(cbegin_pilo(ad, 0));
    verify_forward_iterator_requirements(cbegin_pislo(ad, 0));
    verify_forward_iterator_requirements(cbegin_pilo(ad, 0));
    verify_forward_iterator_requirements(cbegin_pislo(ad, 0));
    verify_forward_iterator_requirements(cbegin_pstilo(ad, 0, 1));
    verify_forward_iterator_requirements(cbegin_pstislo(ad, 0, 1));
  }

  LIBSEMIGROUPS_TEST_CASE("Paths", "009", "pstilo corner case", "[quick]") {
    using namespace rx;
    auto ad = to_word_graph<size_t>(5, {{2, 1}, {}, {3}, {4}, {2}});

    // Tests the case then there is only a single path, but if we would have
    // used pilo (i.e. not use the reachability check that is in pstilo),
    // then we'd enter an infinite loop.
    Paths p(ad);
    p.order(Order::lex).from(0).to(1);

    REQUIRE(p.get() == 1_w);
    p.next();
    REQUIRE(p.at_end());

    ad = chain(5);

    p.init(ad).order(Order::lex).from(0).to(0).min(0).max(100);
    REQUIRE((p | count()) == 1);

    p.min(4);
    REQUIRE((p | count()) == 0);

    ad = WordGraph<size_t>();
    ad.add_to_out_degree(1);
    word_graph::add_cycle(ad, 5);

    p.init(ad).order(Order::lex).from(0).to(0).min(0).max(6);
    REQUIRE((p | count()) == 2);
    REQUIRE(p.count() == 2);

    p.max(100);
    REQUIRE((p | count()) == 20);

    p.min(4);
    REQUIRE((p | count()) == 19);

    // There's 1 path from 0 to 0 of length in range [0, 1), the path of length
    // 0.
    p.min(0).max(2);
    REQUIRE((p | count()) == 1);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths",
                          "010",
                          "number_of_paths corner cases",
                          "[quick]") {
    WordGraph<size_t> ad;
    REQUIRE_THROWS_AS(number_of_paths(ad, 0, 0, POSITIVE_INFINITY),
                      LibsemigroupsException);
    size_t const n = 20;
    ad.add_to_out_degree(1);
    word_graph::add_cycle(ad, n);
    REQUIRE(number_of_paths(ad, 10) == POSITIVE_INFINITY);
    REQUIRE(number_of_paths_algorithm(ad, 10, 10, 0, POSITIVE_INFINITY)
            == paths::algorithm::trivial);
    REQUIRE(number_of_paths(ad, 10, 10, 0, POSITIVE_INFINITY)
            == POSITIVE_INFINITY);
    ad = chain(n);
    REQUIRE(number_of_paths(ad, 10) == 10);
    REQUIRE(number_of_paths(ad, 19) == 1);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths",
                          "011",
                          "number_of_paths acyclic digraph",
                          "[quick]") {
    auto ad = to_word_graph<size_t>(
        8, {{3, 2, 3}, {7}, {1}, {1, 5}, {6}, {}, {3, 7}});

    REQUIRE(word_graph::is_acyclic(ad));

    size_t expected[8][8][8] = {{{0, 1, 4, 9, 12, 12, 12, 12},
                                 {0, 0, 3, 8, 11, 11, 11, 11},
                                 {0, 0, 0, 5, 8, 8, 8, 8},
                                 {0, 0, 0, 0, 3, 3, 3, 3},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0}},
                                {{0, 1, 2, 2, 2, 2, 2, 2},
                                 {0, 0, 1, 1, 1, 1, 1, 1},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0}},
                                {{0, 1, 2, 3, 3, 3, 3, 3},
                                 {0, 0, 1, 2, 2, 2, 2, 2},
                                 {0, 0, 0, 1, 1, 1, 1, 1},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0}},
                                {{0, 1, 3, 4, 4, 4, 4, 4},
                                 {0, 0, 2, 3, 3, 3, 3, 3},
                                 {0, 0, 0, 1, 1, 1, 1, 1},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0}},
                                {{0, 1, 2, 4, 6, 7, 7, 7},
                                 {0, 0, 1, 3, 5, 6, 6, 6},
                                 {0, 0, 0, 2, 4, 5, 5, 5},
                                 {0, 0, 0, 0, 2, 3, 3, 3},
                                 {0, 0, 0, 0, 0, 1, 1, 1},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0}},
                                {{0, 1, 1, 1, 1, 1, 1, 1},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0}},
                                {{0, 1, 3, 5, 6, 6, 6, 6},
                                 {0, 0, 2, 4, 5, 5, 5, 5},
                                 {0, 0, 0, 2, 3, 3, 3, 3},
                                 {0, 0, 0, 0, 1, 1, 1, 1},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0}},
                                {{0, 1, 1, 1, 1, 1, 1, 1},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0},
                                 {0, 0, 0, 0, 0, 0, 0, 0}}};

    Paths p(ad);
    p.order(Order::lex);
    for (auto s = ad.cbegin_nodes(); s != ad.cend_nodes(); ++s) {
      for (size_t min = 0; min < ad.number_of_nodes(); ++min) {
        for (size_t max = 0; max < ad.number_of_nodes(); ++max) {
          p.from(*s).min(min).max(max);
          // the next line is the same as std::distance
          REQUIRE((p | count()) == expected[*s][min][max]);
        }
      }
    }

    for (auto s = ad.cbegin_nodes(); s != ad.cend_nodes(); ++s) {
      for (size_t min = 0; min < ad.number_of_nodes(); ++min) {
        for (size_t max = 0; max < ad.number_of_nodes(); ++max) {
          REQUIRE(number_of_paths(ad, *s, min, max) == expected[*s][min][max]);
          p.from(*s).min(min).max(max);
          REQUIRE(p.count() == expected[*s][min][max]);
        }
      }
    }

    size_t const N = ad.number_of_nodes();
    p.from(0).to(3).min(0).max(2);
    REQUIRE((p | to_vector()) == std::vector<word_type>({{0}, {2}}));

    REQUIRE(number_of_paths(ad, 0, 3, 0, 2, paths::algorithm::acyclic)
            == (p | count()));

    for (auto s = ad.cbegin_nodes(); s != ad.cend_nodes(); ++s) {
      for (auto t = ad.cbegin_nodes(); t != ad.cend_nodes(); ++t) {
        for (size_t min = 0; min < N; ++min) {
          for (size_t max = min; max < N; ++max) {
            p.from(*s).to(*t).min(min).max(max);
            REQUIRE(number_of_paths(ad, *s, *t, min, max) == (p | count()));
          }
        }
      }
    }
  }

  // This test is marginally slower using Paths rather than cbegin_pstilo etc,
  // seemily because of the use of std::variant in Paths (according to
  // Instruments)
  LIBSEMIGROUPS_TEST_CASE("Paths",
                          "012",
                          "number_of_paths binary tree",
                          "[quick][no-valgrind]") {
    using node_type      = WordGraph<size_t>::node_type;
    size_t const      n  = 6;
    WordGraph<size_t> ad = binary_tree(n);
    REQUIRE(ad.number_of_nodes() == std::pow(2, n) - 1);
    REQUIRE(ad.number_of_edges() == std::pow(2, n) - 2);
    REQUIRE(word_graph::is_acyclic(ad));
    REQUIRE(number_of_paths(ad, 0) == std::pow(2, n) - 1);

    Paths p(ad);
    p.order(Order::lex);

    for (auto s = ad.cbegin_nodes(); s != ad.cend_nodes(); ++s) {
      for (node_type min = 0; min < n; ++min) {
        for (size_t max = min; max < n; ++max) {
          p.from(*s).min(min).max(max);
          REQUIRE(number_of_paths(ad, *s, min, max) == (p | count()));
        }
      }
    }
    REQUIRE(number_of_paths_algorithm(ad, 0, 1, 0, 1)
            == paths::algorithm::acyclic);

    p.from(0).to(1).min(0).max(1);
    REQUIRE(number_of_paths(ad, 0, 1, 0, 1) == (p | count()));
    REQUIRE(p.count() == (p | count()));

    for (auto s = ad.cbegin_nodes(); s != ad.cend_nodes(); ++s) {
      for (auto t = ad.cbegin_nodes(); t != ad.cend_nodes(); ++t) {
        for (node_type min = 0; min < n; ++min) {
          for (size_t max = min; max < n; ++max) {
            p.from(*s).to(*t).min(min).max(max);
            REQUIRE(number_of_paths(ad, *s, *t, min, max) == (p | count()));
          }
        }
      }
    }
  }

  LIBSEMIGROUPS_TEST_CASE("Paths",
                          "013",
                          "number_of_paths large binary tree",
                          "[quick][no-valgrind]") {
    size_t const      n  = 20;
    WordGraph<size_t> ad = binary_tree(n);
    REQUIRE(ad.number_of_nodes() == std::pow(2, n) - 1);
    REQUIRE(ad.number_of_edges() == std::pow(2, n) - 2);
    REQUIRE(word_graph::is_acyclic(ad));
    REQUIRE(number_of_paths_algorithm(ad, 0) == paths::algorithm::acyclic);
    REQUIRE(number_of_paths(ad, 0) == std::pow(2, n) - 1);

    // The following tests for code coverage
    ad.set_target(19, 0, 0);
    REQUIRE(
        number_of_paths(ad, 0, 0, 0, POSITIVE_INFINITY, paths::algorithm::dfs)
        == POSITIVE_INFINITY);
    // 0 not reachable from 10
    REQUIRE(number_of_paths(
                ad, 10, 0, 0, POSITIVE_INFINITY, paths::algorithm::matrix)
            == 0);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths",
                          "014",
                          "number_of_paths 400 node random digraph",
                          "[quick]") {
    size_t const n  = 400;
    auto         ad = WordGraph<size_t>::random(n, 20, n, std::mt19937());
    word_graph::add_cycle(ad, ad.cbegin_nodes(), ad.cend_nodes());
    REQUIRE(!word_graph::is_acyclic(ad));
    REQUIRE(!word_graph::is_complete(ad));
    REQUIRE(number_of_paths_algorithm(ad, 0, 0, 16) == paths::algorithm::dfs);
    REQUIRE(number_of_paths(ad, 0, 0, 16) != 0);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths",
                          "015",
                          "number_of_paths 10 node acyclic digraph",
                          "[quick]") {
    // size_t const n  = 10;
    // auto ad = WordGraph<size_t>::random_acyclic(n, 20, n,
    // std::mt19937()); std::cout <<
    // word_graph::detail::to_string(ad);

    WordGraph<size_t> ad;
    ad.add_nodes(10);
    ad.add_to_out_degree(20);
    ad.set_target(0, 5, 7);
    ad.set_target(0, 7, 5);
    ad.set_target(1, 14, 9);
    ad.set_target(1, 17, 5);
    ad.set_target(3, 5, 8);
    ad.set_target(5, 1, 8);
    ad.set_target(6, 14, 8);
    ad.set_target(7, 10, 8);
    ad.set_target(8, 12, 9);
    ad.set_target(8, 13, 9);

    REQUIRE(word_graph::is_acyclic(ad));
    REQUIRE(!word_graph::is_complete(ad));

    REQUIRE(number_of_paths_algorithm(ad, 0, 0, 16)
            == paths::algorithm::acyclic);
    REQUIRE(number_of_paths(ad, 0, 0, 30) == 9);
    REQUIRE(number_of_paths(ad, 1, 0, 10, paths::algorithm::acyclic) == 6);
    REQUIRE(number_of_paths(ad, 1, 0, 10, paths::algorithm::matrix) == 6);
    REQUIRE(number_of_paths(ad, 1, 9, 0, 10, paths::algorithm::matrix) == 3);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths",
                          "016",
                          "number_of_paths node digraph",
                          "[quick]") {
    size_t const n = 10;
    // auto         ad = WordGraph<size_t>::random(n, 20, 200,
    // std::mt19937());
    // std::cout << word_graph::detail::to_string(ad);
    auto ad = to_word_graph<size_t>(
        10,
        {{9, 1, 6, 3, 7, 2, 2, 8, 1, 4, 3, 1, 7, 9, 4, 7, 8, 9, 6, 9},
         {8, 2, 5, 7, 9, 0, 2, 4, 0, 3, 2, 7, 2, 7, 6, 6, 5, 4, 6, 3},
         {2, 9, 0, 6, 7, 9, 5, 4, 9, 7, 9, 9, 0, 7, 9, 6, 3, 3, 4, 1},
         {1, 9, 6, 2, 9, 8, 1, 6, 1, 0, 5, 0, 2, 7, 4, 0, 4, 8, 3, 1},
         {0, 4, 8, 5, 5, 1, 3, 8, 4, 4, 4, 7, 8, 6, 3, 7, 6, 7, 0, 2},
         {3, 0, 4, 7, 2, 5, 7, 7, 7, 7, 0, 8, 6, 8, 8, 1, 5, 5, 3, 7},
         {8, 7, 6, 5, 6, 1, 7, 2, 7, 3, 3, 8, 3, 9, 4, 1, 4, 3, 9, 8},
         {9, 4, 3, 8, 0, 5, 6, 8, 9, 1, 7, 0, 6, 2, 3, 8, 6, 3, 2, 7},
         {0, 6, 3, 5, 7, 9, 9, 8, 1, 5, 7, 9, 6, 0, 0, 3, 6, 0, 8, 9},
         {3, 7, 9, 1, 4, 9, 4, 0, 5, 8, 3, 2, 0, 2, 3, 4, 0, 5, 3, 5}});
    REQUIRE(!word_graph::is_acyclic(ad));
    REQUIRE(word_graph::is_complete(ad));

    REQUIRE(number_of_paths_algorithm(ad, 0) == paths::algorithm::acyclic);
    REQUIRE(number_of_paths(ad, 0) == POSITIVE_INFINITY);
    REQUIRE_THROWS_AS(number_of_paths(ad, 0, 0, 10, paths::algorithm::acyclic),
                      LibsemigroupsException);
    REQUIRE_THROWS_AS(
        number_of_paths(ad, 1, 9, 0, 10, paths::algorithm::acyclic),
        LibsemigroupsException);

    ad = binary_tree(n);
    REQUIRE(number_of_paths_algorithm(ad, 0) == paths::algorithm::acyclic);
    REQUIRE(number_of_paths(ad, 0) == 1023);

    word_graph::add_cycle(ad, n);
    ad.set_target(0, 0, n + 1);
    REQUIRE(!word_graph::is_acyclic(ad));
    REQUIRE(!word_graph::is_complete(ad));
    REQUIRE(number_of_paths(ad, 1) == 511);
    REQUIRE(number_of_paths_algorithm(ad, 1, 0, POSITIVE_INFINITY)
            == paths::algorithm::acyclic);
    REQUIRE(number_of_paths(ad, 1, 0, POSITIVE_INFINITY) == 511);
    REQUIRE(word_graph::topological_sort(ad).empty());
    REQUIRE(*std::find_if(ad.cbegin_nodes(), ad.cend_nodes(), [&ad](size_t m) {
      return word_graph::topological_sort(ad, m).empty();
    }) == 1023);
  }

  LIBSEMIGROUPS_TEST_CASE("Paths",
                          "017",
                          "number_of_paths (matrix)",
                          "[quick]") {
    // REQUIRE(detail::magic_number(6) * 6 == 14.634);
    // auto ad = WordGraph<size_t>::random(6, 3, 15, std::mt19937());
    // std::cout << word_graph::detail::to_string(ad);
    auto ad = to_word_graph<size_t>(6,
                                    {{0, 3, 4},
                                     {2, 1, 4},
                                     {4, 3, 4},
                                     {0, 1, UNDEFINED},
                                     {UNDEFINED, 3, 3},
                                     {4, UNDEFINED, 2}});

    REQUIRE(ad.number_of_edges() == 15);

    Paths p(ad);
    p.order(Order::lex).from(0).min(0).max(10);
    REQUIRE((p | count()) == 6'858);
    REQUIRE(number_of_paths_algorithm(ad, 0, 0, 10)
            == paths::algorithm::matrix);
    REQUIRE(number_of_paths(ad, 0, 0, 10) == 6'858);
    REQUIRE_THROWS_AS(number_of_paths(ad, 1, 0, 10, paths::algorithm::trivial),
                      LibsemigroupsException);
    REQUIRE(number_of_paths_algorithm(ad, 0, 10, 12)
            == paths::algorithm::matrix);
    REQUIRE(number_of_paths(ad, 0, 10, 12) == 35300);

    auto checker1 = [&ad](word_type const& w) {
      return 10 <= w.size() && w.size() < 12
             && word_graph::follow_path(ad, 0, w) != UNDEFINED;
    };

    p.min(10).max(12);
    REQUIRE((p | all_of(std::move(checker1))));

    std::unordered_set<word_type> distinct_words;
    for (auto it = begin(p); it != end(p); ++it) {  // FIXME the range based for
                                                    // here doesn't work
      distinct_words.insert(*it);
    }
    REQUIRE(distinct_words.size() == 35'300);
    REQUIRE((p | count()) == 35'300);

    REQUIRE(number_of_paths_algorithm(ad, 1, 5, 0, 10)
            == paths::algorithm::trivial);
    REQUIRE(number_of_paths(ad, 1, 5, 0, 10) == 0);

    p.from(1).to(5).min(0).max(10);
    REQUIRE(0 == (p | count()));
    REQUIRE(number_of_paths(ad, 1, 1, 0, 10) == 1404);
    REQUIRE_THROWS_AS(
        number_of_paths(ad, 1, 1, 0, 10, paths::algorithm::trivial),
        LibsemigroupsException);

    p.from(1).to(1).min(0).max(10);
    REQUIRE(number_of_paths(ad, 1, 1, 0, 10) == uint64_t((p | count())));

    auto checker2 = [&ad](word_type const& w) {
      return w.size() < 10 && word_graph::follow_path(ad, 1, w) == 1;
    };
    REQUIRE((p | all_of(std::move(checker2))));
  }

  LIBSEMIGROUPS_TEST_CASE("Paths",
                          "018",
                          "number_of_paths (matrix)",
                          "[quick]") {
    WordGraph<size_t> ad;
    ad.add_nodes(2);
    ad.add_to_out_degree(2);
    ad.set_target(0, 0, 1);
    ad.set_target(1, 0, 0);

    REQUIRE(number_of_paths(
                ad, 0, 1, 0, POSITIVE_INFINITY, paths::algorithm::matrix)
            == POSITIVE_INFINITY);
    REQUIRE(number_of_paths(ad, 0, 1, 0, 10, paths::algorithm::matrix) == 5);
  }
}  // namespace libsemigroups
