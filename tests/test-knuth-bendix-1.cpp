// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019-2025 James D. Mitchell
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

// This file is one of six that contains tests for the KnuthBendix classes. In
// a mostly vain attempt to speed up compilation the tests are split across 6
// files as follows:
//
// 1: contains quick tests for KnuthBendix created from rules and all commented
//    out tests.
//
// 2: contains more quick tests for KnuthBendix created from rules
//
// 3: contains yet more quick tests for KnuthBendix created from rules
//
// 4: contains standard and extreme test for KnuthBendix created from rules
//
// 5: contains tests for KnuthBendix created from FroidurePin instances
//
// 6: contains tests for KnuthBendix using word_type presentations

// TODO(later)
// * The other examples from Sims' book (Chap.s 5 and 6) which use
//   reduction orderings different from shortlex
// * Examples from MAF

#define CATCH_CONFIG_ENABLE_ALL_STRINGMAKERS

#include <algorithm>  // for fill
#include <chrono>     // for milliseconds
#include <cstddef>    // for size_t
#include <string>     // for basic_string, operator==
#include <utility>    // for move
#include <vector>     // for vector, operator==

#include "Catch2-3.8.0/catch_amalgamated.hpp"  // for AssertionHandler, ope...
#include "test-main.hpp"  // for LIBSEMIGROUPS_TEMPLATE_TEST_CASE

#include "libsemigroups/constants.hpp"           // for operator==, operator!=
#include "libsemigroups/exception.hpp"           // for LibsemigroupsException
#include "libsemigroups/knuth-bendix.hpp"        // for KnuthBendix, normal_f...
#include "libsemigroups/obvinf.hpp"              // for is_obviously_infinite
#include "libsemigroups/paths.hpp"               // for Paths
#include "libsemigroups/presentation.hpp"        // for add_rule, Presentation
#include "libsemigroups/ranges.hpp"              // for equal
#include "libsemigroups/to-froidure-pin.hpp"     // for to<FroidurePin>
#include "libsemigroups/types.hpp"               // for word_type
#include "libsemigroups/word-graph-helpers.hpp"  // for word_graph
#include "libsemigroups/word-graph.hpp"          // for WordGraph

#include "libsemigroups/detail/report.hpp"  // for ReportGuard

namespace libsemigroups {
  using namespace rx;
  using literals::operator""_w;

  congruence_kind constexpr twosided = congruence_kind::twosided;

  namespace {
    // Generate the 'normal forms' defined by an arbitrary WordGraph.
    // If `wg` corresponds to the Gilman graph of some KnuthBendix instance,
    // then the words returned are the normal forms of that KnuthBendix
    // instance. Since the node labels returned by gilman_graph() are
    // implementation dependent, the below function can be used to check that
    // `gilman_graph()` returns something that generates the correct normal
    // forms.
    template <typename RewritingSystem,
              typename ReductionOrder,
              typename WordType>
    [[nodiscard]] inline auto normal_forms_from_word_graph(
        KnuthBendix<RewritingSystem, ReductionOrder>& kb,
        WordGraph<WordType>&                          wg) {
      Paths paths(wg);
      paths.source(0);
      if (!kb.presentation().contains_empty_word()) {
        paths.next();
      }
      return paths;
    }
  }  // namespace

  using Trie = detail::RewritingSystemTrie<>;
  using Set  = detail::RewritingSystemSet<>;

  // using RewritingSystemTrieRPC     =
  // detail::RewritingSystemTrie<RecursivePathCompare>; using
  // RewritingSystemSetRPC = detail::RewritingSystemSet<RecursivePathCompare>;

#define REWRITER_TYPES Trie, Set

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "000",
                                   "confluent fp semigroup 1 (infinite)",
                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("abc");
    p.rules = {"ab", "ba", "ac", "ca",  "aa", "a",  "ac", "a",  "ca", "a", "bb",
               "bb", "bc", "cb", "bbb", "b",  "bc", "b",  "cb", "b",  "a", "b"};

    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(kb.rewriting_system().number_of_rules() == 10);
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(knuth_bendix::reduce(kb, "ca") == "a");
    REQUIRE(knuth_bendix::reduce(kb, "ac") == "a");
    REQUIRE(knuth_bendix::contains(kb, "ca", "a"));
    REQUIRE(knuth_bendix::contains(kb, "ac", "a"));
    REQUIRE(kb.number_of_classes() == POSITIVE_INFINITY);
    REQUIRE(is_obviously_infinite(kb));

    auto nf = knuth_bendix::normal_forms(kb).min(1).max(4);

    REQUIRE((nf | to_vector())
            == std::vector<std::string>({"a", "c", "cc", "ccc", "cccc"}));
    // REQUIRE(knuth_bendix::is_reduced(kb));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "001",
                                   "confluent fp semigroup 2 (infinite)",
                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.alphabet("abc");
    presentation::add_rule_no_checks(p, "ac", "ca");
    presentation::add_rule_no_checks(p, "aa", "a");
    presentation::add_rule_no_checks(p, "ac", "a");
    presentation::add_rule_no_checks(p, "ca", "a");
    presentation::add_rule_no_checks(p, "bb", "bb");
    presentation::add_rule_no_checks(p, "bc", "cb");
    presentation::add_rule_no_checks(p, "bbb", "b");
    presentation::add_rule_no_checks(p, "bc", "b");
    presentation::add_rule_no_checks(p, "cb", "b");
    presentation::add_rule_no_checks(p, "a", "b");

    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(kb.rewriting_system().number_of_rules() == 4);
    REQUIRE(is_obviously_infinite(kb));
    auto nf = knuth_bendix::normal_forms(kb).min(1).max(4);

    REQUIRE((nf | to_vector())
            == std::vector<std::string>({"a", "c", "cc", "ccc", "cccc"}));
    REQUIRE(kb.number_of_classes() == POSITIVE_INFINITY);
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "002",
                                   "confluent fp semigroup 3 (infinite)",
                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.alphabet("012");
    presentation::add_rule_no_checks(p, "01", "10");
    presentation::add_rule_no_checks(p, "02", "20");
    presentation::add_rule_no_checks(p, "00", "0");
    presentation::add_rule_no_checks(p, "02", "0");
    presentation::add_rule_no_checks(p, "20", "0");
    presentation::add_rule_no_checks(p, "11", "11");
    presentation::add_rule_no_checks(p, "12", "21");
    presentation::add_rule_no_checks(p, "111", "1");
    presentation::add_rule_no_checks(p, "12", "1");
    presentation::add_rule_no_checks(p, "21", "1");
    presentation::add_rule_no_checks(p, "0", "1");

    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(kb.rewriting_system().number_of_rules() == 10);
    //     REQUIRE(kb.number_of_pending_rules() == 10);
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(kb.rewriting_system().number_of_rules() == 4);
    REQUIRE(kb.number_of_classes() == POSITIVE_INFINITY);

    auto nf = knuth_bendix::normal_forms(kb);
    REQUIRE((nf.min(1).max(1) | to_vector())
            == std::vector<std::string>({"0", "2"}));

    REQUIRE((nf.min(1).max(11) | to_vector())
            == std::vector<std::string>({"0",
                                         "2",
                                         "22",
                                         "222",
                                         "2222",
                                         "22222",
                                         "222222",
                                         "2222222",
                                         "22222222",
                                         "222222222",
                                         "2222222222",
                                         "22222222222"}));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "003",
                                   "non-confluent example wikipedia",
                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("01");
    presentation::add_rule_no_checks(p, "000", "");
    presentation::add_rule_no_checks(p, "111", "");
    presentation::add_rule_no_checks(p, "010101", "");

    KnuthBendix<std::string, TestType> kb(twosided, p);
    REQUIRE(kb.presentation().alphabet() == "01");
    REQUIRE(!kb.rewriting_system().confluent());
    kb.run();
    // REQUIRE(kb.rewriting_system().number_of_rules() == 4);
    REQUIRE(
        (kb.active_rules() | rx::sort() | rx::to_vector())
        == std::vector<std::pair<std::string, std::string>>(
            {{"000", ""}, {"1010", "0011"}, {"1100", "0101"}, {"111", ""}}));
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(kb.number_of_classes() == POSITIVE_INFINITY);

    auto nf = knuth_bendix::normal_forms(kb);

    REQUIRE((nf.min(0).max(4) | to_vector())
            == std::vector<std::string>(
                {"",     "0",    "1",    "00",   "01",   "10",   "11",
                 "001",  "010",  "011",  "100",  "101",  "110",  "0010",
                 "0011", "0100", "0101", "0110", "1001", "1011", "1101"}));
    REQUIRE((nf.min(0).max(10) | all_of([&kb](auto const& w) {
               return knuth_bendix::reduce(kb, w) == w;
             })));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "004",
                                   "Example 5.1 in Sims (infinite)",

                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("abcd");
    presentation::add_rule_no_checks(p, "ab", "");
    presentation::add_rule_no_checks(p, "ba", "");
    presentation::add_rule_no_checks(p, "cd", "");
    presentation::add_rule_no_checks(p, "dc", "");
    presentation::add_rule_no_checks(p, "ca", "ac");

    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(!kb.rewriting_system().confluent());
    kb.run();
    REQUIRE(kb.rewriting_system().number_of_rules() == 8);
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(kb.number_of_classes() == POSITIVE_INFINITY);

    auto nf = knuth_bendix::normal_forms(kb);
    REQUIRE((nf.min(0).max(4) | to_vector())
            == std::vector<std::string>(  // codespell:end-ignore
                {"",     "a",    "b",    "c",    "d",    "aa",   "ac",
                 "ad",   "bb",   "bc",   "bd",   "cc",   "dd",   "aaa",
                 "aac",  "aad",  "acc",  "add",  "bbb",  "bbc",  "bbd",
                 "bcc",  "bdd",  "ccc",  "ddd",  "aaaa", "aaac", "aaad",
                 "aacc", "aadd", "accc", "addd", "bbbb", "bbbc", "bbbd",
                 "bbcc", "bbdd", "bccc", "bddd", "cccc", "dddd"}));
    // codespell:end-ignore
    REQUIRE((nf.min(0).max(6) | all_of([&kb](auto const& w) {
               return knuth_bendix::reduce(kb, w) == w;
             })));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "005",
                                   "Example 5.1 in Sims (infinite) x 2",
                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("aAbB");
    presentation::add_inverse_rules(p, "AaBb");
    presentation::add_rule_no_checks(p, "ba", "ab");

    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(!kb.rewriting_system().confluent());
    kb.run();
    REQUIRE(kb.rewriting_system().number_of_rules() == 8);
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(kb.number_of_classes() == POSITIVE_INFINITY);

    auto nf = knuth_bendix::normal_forms(kb);
    REQUIRE((nf.min(0).max(4) | to_vector())
            == std::vector<std::string>(
                {"",     "a",    "A",    "b",    "B",    "aa",   "ab",
                 "aB",   "AA",   "Ab",   "AB",   "bb",   "BB",   "aaa",
                 "aab",  "aaB",  "abb",  "aBB",  "AAA",  "AAb",  "AAB",
                 "Abb",  "ABB",  "bbb",  "BBB",  "aaaa", "aaab", "aaaB",
                 "aabb", "aaBB", "abbb", "aBBB", "AAAA", "AAAb", "AAAB",
                 "AAbb", "AABB", "Abbb", "ABBB", "bbbb", "BBBB"}));
    REQUIRE((nf.min(0).max(6) | all_of([&kb](auto const& w) {
               return knuth_bendix::reduce(kb, w) == w;
             })));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "006",
                                   "Example 5.3 in Sims",

                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("ab");
    presentation::add_rule_no_checks(p, "aa", "");
    presentation::add_rule_no_checks(p, "bbb", "");
    presentation::add_rule_no_checks(p, "ababab", "");

    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(!kb.rewriting_system().confluent());
    kb.run();
    REQUIRE(kb.rewriting_system().number_of_rules() == 6);
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(kb.number_of_classes() == 12);

    auto nf = knuth_bendix::normal_forms(kb);
    REQUIRE(nf.count() == 12);

    REQUIRE((nf | to_vector())
            == std::vector<std::string>({"",
                                         "a",
                                         "b",
                                         "ab",
                                         "ba",
                                         "bb",
                                         "aba",
                                         "abb",
                                         "bab",
                                         "bba",
                                         "babb",
                                         "bbab"}));
    REQUIRE((nf.min(0).max(6) | all_of([&kb](auto const& w) {
               return knuth_bendix::reduce(kb, w) == w;
             })));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "007",
                                   "Example 5.4 in Sims",

                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("Bab");
    presentation::add_rule_no_checks(p, "aa", "");
    presentation::add_rule_no_checks(p, "bB", "");
    presentation::add_rule_no_checks(p, "bbb", "");
    presentation::add_rule_no_checks(p, "ababab", "");

    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(!kb.rewriting_system().confluent());
    kb.run();
    REQUIRE(kb.rewriting_system().number_of_rules() == 11);
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(kb.number_of_classes() == 12);

    auto nf = knuth_bendix::normal_forms(kb).min(1).max(5);
    REQUIRE(nf.size_hint() == 11);
    REQUIRE((nf | to_vector())
            == std::vector<std::string>({"B",
                                         "a",
                                         "b",
                                         "Ba",
                                         "aB",
                                         "ab",
                                         "ba",
                                         "BaB",
                                         "Bab",
                                         "aBa",
                                         "baB"}));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "008",
                                   "Example 6.4 in Sims",
                                   "[quick][knuth-bendix][no-valgrind]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.alphabet("abc");
    p.contains_empty_word(true);

    presentation::add_rule_no_checks(p, "aa", "");
    presentation::add_rule_no_checks(p, "bc", "");
    presentation::add_rule_no_checks(p, "bbb", "");
    presentation::add_rule_no_checks(p, "ababababababab", "");
    presentation::add_rule_no_checks(p, "abacabacabacabac", "");

    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(!kb.rewriting_system().confluent());
    REQUIRE(!is_obviously_infinite(kb));
    // REQUIRE(!kb.is_obviously_finite());
    kb.run();
    REQUIRE(kb.rewriting_system().number_of_rules() == 40);
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(knuth_bendix::reduce(kb, "cc") == "b");
    REQUIRE(knuth_bendix::reduce(kb, "ccc") == "");
    REQUIRE(kb.number_of_classes() == 168);

    auto nf = knuth_bendix::normal_forms(kb).min(1).max(4);
    REQUIRE((nf | to_vector())
            == std::vector<std::string>(
                {"a",    "b",    "c",    "ab",   "ac",   "ba",   "ca",
                 "aba",  "aca",  "bab",  "bac",  "cab",  "cac",  "abab",
                 "abac", "acab", "acac", "baba", "baca", "caba", "caca"}));
    auto S = to<FroidurePin>(kb);
    REQUIRE(S.size() == 168);
    REQUIRE(S.generator(2).word() == "c");
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "009",
                                   "random example",
                                   "[quick][knuth-bendix][no-valgrind]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.alphabet("012");

    presentation::add_rule_no_checks(p, "000", "2");
    presentation::add_rule_no_checks(p, "111", "2");
    presentation::add_rule_no_checks(p, "010101", "2");
    presentation::add_identity_rules(p, '2');

    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(!kb.rewriting_system().confluent());
    kb.run();
    REQUIRE(kb.rewriting_system().number_of_rules() == 9);
    REQUIRE(kb.rewriting_system().confluent());

    auto& wg = kb.gilman_graph();
    REQUIRE(wg.number_of_nodes() == 9);
    REQUIRE(wg.number_of_edges() == 13);
    REQUIRE(!v4::word_graph::is_acyclic(wg));

    auto fp = to<FroidurePin>(kb);
    fp.enumerate(100);

    auto expected = froidure_pin::current_normal_forms(fp);

    Paths paths(wg);
    paths.source(0).min(1).max(fp.current_max_word_length());

    REQUIRE(equal(expected, paths));

    auto nf = knuth_bendix::normal_forms(kb).min(1).max(4);
    REQUIRE((nf | to_vector())
            == std::vector<std::string>(
                {"0",    "1",    "2",    "00",   "01",   "10",   "11",
                 "001",  "010",  "011",  "100",  "101",  "110",  "0010",
                 "0011", "0100", "0101", "0110", "1001", "1011", "1101"}));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "010",
                                   "SL(2, 7) from Chap. 3, Prop. 1.5 in NR",
                                   "[quick][knuth-bendix][no-valgrind]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.alphabet("abAB");
    p.contains_empty_word(true);

    presentation::add_rule_no_checks(p, "aaaaaaa", "");
    presentation::add_rule_no_checks(p, "bb", "ababab");
    presentation::add_rule_no_checks(p, "bb", "aaaabaaaabaaaabaaaab");
    presentation::add_rule_no_checks(p, "aA", "");
    presentation::add_rule_no_checks(p, "Aa", "");
    presentation::add_rule_no_checks(p, "bB", "");
    presentation::add_rule_no_checks(p, "Bb", "");

    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(!kb.rewriting_system().confluent());

    kb.run();
    REQUIRE(kb.rewriting_system().number_of_rules() == 152);
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(kb.number_of_classes() == 336);

    // Test copy constructor
    auto T = to<FroidurePin>(kb);
    auto S = froidure_pin::copy_closure(T, {T.generator(0)});

    REQUIRE(S.size() == 336);
    // 5 because S is generated as semigroup by 5 generators, while p is a
    // monoid presentation
    REQUIRE(S.number_of_generators() == 5);

    auto& wg = kb.gilman_graph();
    REQUIRE(wg.number_of_nodes() == 232);
    REQUIRE(wg.number_of_edges() == 265);
    REQUIRE(v4::word_graph::is_acyclic(wg));
    Paths paths(wg);
    paths.source(0).min(0).max(13);
    REQUIRE(paths.count() == 336);
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "011",
                                   "F(2, 5) - Chap. 9, Sec. 1 in NR",
                                   "[knuth-bendix][quick]",
                                   REWRITER_TYPES) {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("abcde");

    presentation::add_rule_no_checks(p, "ab", "c");
    presentation::add_rule_no_checks(p, "bc", "d");
    presentation::add_rule_no_checks(p, "cd", "e");
    presentation::add_rule_no_checks(p, "de", "a");
    presentation::add_rule_no_checks(p, "ea", "b");
    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(!kb.rewriting_system().confluent());
    kb.run();
    REQUIRE(kb.rewriting_system().number_of_rules() == 24);
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(kb.number_of_classes() == 11);

    auto& wg = kb.gilman_graph();
    REQUIRE(wg.number_of_nodes() == 8);
    REQUIRE(wg.number_of_edges() == 11);
    REQUIRE(v4::word_graph::is_acyclic(wg));
    Paths paths(wg);
    paths.source(0).min(0).max(5);
    REQUIRE(paths.count() == 12);
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "012",
                                   "Reinis example 1",
                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("abc");

    presentation::add_rule_no_checks(p, "a", "abb");
    presentation::add_rule_no_checks(p, "b", "baa");
    KnuthBendix<std::string, TestType> kb(twosided, p);

    REQUIRE(!kb.rewriting_system().confluent());
    kb.run();
    REQUIRE(kb.rewriting_system().number_of_rules() == 4);

    auto& wg = kb.gilman_graph();
    REQUIRE(wg.number_of_nodes() == 7);
    REQUIRE(wg.number_of_edges() == 17);
    REQUIRE(!v4::word_graph::is_acyclic(wg));
    Paths paths(wg);
    paths.source(0).min(0).max(9);
    REQUIRE(paths.count() == 13'044);
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "013",
                                   "redundant_rule (std::string)",
                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("abc");
    presentation::add_rule(p, "a", "abb");
    presentation::add_rule(p, "b", "baa");
    presentation::add_rule(p, "c", "abbabababaaababababab");

    auto it = knuth_bendix::redundant_rule(p, std::chrono::milliseconds(100));
    REQUIRE(it == p.rules.cend());

    presentation::add_rule(p, "b", "baa");
    it = knuth_bendix::redundant_rule(p, std::chrono::milliseconds(100));
    REQUIRE(it != p.rules.cend());
    REQUIRE(*it == "b");
    REQUIRE(*(it + 1) == "baa");
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "014",
                                   "redundant_rule (word_type)",
                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    using literals::operator""_w;

    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(3);
    presentation::add_rule(p, 0_w, 011_w);
    presentation::add_rule(p, 1_w, 100_w);
    presentation::add_rule(p, 2_w, 011010101000101010101_w);

    auto it = knuth_bendix::redundant_rule(p, std::chrono::milliseconds(10));
    REQUIRE(it == p.rules.cend());

    presentation::add_rule(p, 1_w, 100_w);
    it = knuth_bendix::redundant_rule(p, std::chrono::milliseconds(10));
    REQUIRE(it != p.rules.cend());
    REQUIRE(*it == 1_w);
    REQUIRE(*(it + 1) == 100_w);
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "015",
                                   "constructors/init for finished",
                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<std::string> p1;
    p1.contains_empty_word(true);
    p1.alphabet("abcd");
    presentation::add_rule_no_checks(p1, "ab", "");
    presentation::add_rule_no_checks(p1, "ba", "");
    presentation::add_rule_no_checks(p1, "cd", "");
    presentation::add_rule_no_checks(p1, "dc", "");
    presentation::add_rule_no_checks(p1, "ca", "ac");

    Presentation<std::string> p2;
    p2.contains_empty_word(true);
    p2.alphabet("01");
    presentation::add_rule_no_checks(p2, "000", "");
    presentation::add_rule_no_checks(p2, "111", "");
    presentation::add_rule_no_checks(p2, "010101", "");

    KnuthBendix<std::string, TestType> kb1(twosided, p1);
    REQUIRE(!kb1.rewriting_system().confluent());
    REQUIRE(!kb1.finished());
    kb1.run();
    REQUIRE(kb1.rewriting_system().confluent());
    REQUIRE(knuth_bendix::reduce(kb1, "abababbdbcbdbabdbdb") == "bbbbbbddd");

    kb1.init(twosided, p2);
    REQUIRE(!kb1.rewriting_system().confluent());
    REQUIRE(!kb1.finished());
    REQUIRE(kb1.presentation() == p2);
    kb1.run();
    REQUIRE(kb1.finished());
    REQUIRE(kb1.rewriting_system().confluent());
    REQUIRE(kb1.rewriting_system().confluent_known());

    kb1.init(twosided, p1);
    REQUIRE(!kb1.rewriting_system().confluent());
    REQUIRE(!kb1.finished());
    REQUIRE(kb1.presentation() == p1);
    kb1.run();
    REQUIRE(kb1.finished());
    REQUIRE(kb1.rewriting_system().confluent());
    REQUIRE(kb1.rewriting_system().confluent_known());
    REQUIRE(knuth_bendix::reduce(kb1, "abababbdbcbdbabdbdb") == "bbbbbbddd");

    KnuthBendix<std::string, TestType> kb2(std::move(kb1));
    REQUIRE(kb2.rewriting_system().confluent());
    REQUIRE(kb2.rewriting_system().confluent_known());
    REQUIRE(kb2.finished());
    REQUIRE(knuth_bendix::reduce(kb2, "abababbdbcbdbabdbdb") == "bbbbbbddd");

    kb1 = std::move(kb2);
    REQUIRE(kb1.rewriting_system().confluent());
    REQUIRE(kb1.rewriting_system().confluent_known());
    REQUIRE(kb1.finished());
    REQUIRE(knuth_bendix::reduce(kb1, "abababbdbcbdbabdbdb") == "bbbbbbddd");

    kb1.init(twosided, std::move(p1));
    REQUIRE(!kb1.rewriting_system().confluent());
    REQUIRE(!kb1.finished());
    kb1.run();
    REQUIRE(kb1.finished());
    REQUIRE(kb1.rewriting_system().confluent());
    REQUIRE(kb1.rewriting_system().confluent_known());
    REQUIRE(knuth_bendix::reduce(kb1, "abababbdbcbdbabdbdb") == "bbbbbbddd");
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "016",
                                   "constructors/init for partially run",
                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    using literals::operator""_w;

    auto rg = ReportGuard(false);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("abc");

    presentation::add_rule_no_checks(p, "aa", "");
    presentation::add_rule_no_checks(p, "bc", "");
    presentation::add_rule_no_checks(p, "bbb", "");
    presentation::add_rule_no_checks(p, "ababababababab", "");
    presentation::add_rule_no_checks(p, "abacabacabacabacabacabacabacabac", "");

    KnuthBendix<std::string, TestType> kb1(twosided, p);
    REQUIRE(!kb1.rewriting_system().confluent());
    REQUIRE(!kb1.finished());
    kb1.run_for(std::chrono::milliseconds(10));
    REQUIRE(!kb1.rewriting_system().confluent());
    REQUIRE(!kb1.finished());

    kb1.init(twosided, p);
    REQUIRE(!kb1.rewriting_system().confluent());
    REQUIRE(!kb1.finished());
    REQUIRE(kb1.presentation() == p);
    kb1.run_for(std::chrono::milliseconds(10));
    REQUIRE(!kb1.rewriting_system().confluent());
    REQUIRE(!kb1.finished());

    KnuthBendix<std::string, TestType> kb2(kb1);
    REQUIRE(!kb2.rewriting_system().confluent());
    REQUIRE(!kb2.finished());
    REQUIRE(kb2.presentation() == p);
    REQUIRE(kb1.rewriting_system().number_of_rules()
            == kb2.rewriting_system().number_of_rules());
    kb2.run_for(std::chrono::milliseconds(10));
    REQUIRE(!kb2.rewriting_system().confluent());
    REQUIRE(!kb2.finished());

    size_t const M = kb2.rewriting_system().number_of_rules();
    kb1            = std::move(kb2);
    REQUIRE(kb1.rewriting_system().number_of_rules() == M);
    REQUIRE(!kb1.finished());

    kb1.init(twosided, p);
    knuth_bendix::add_generating_pair(kb1, "ab", "ba");
    REQUIRE(kb1.number_of_generating_pairs() == 1);
    REQUIRE(kb1.generating_pairs() == std::vector<std::string>({"ab", "ba"}));
    REQUIRE(kb1.internal_generating_pairs().size() == 2);

    kb1.init(twosided, p);
    REQUIRE(kb1.number_of_generating_pairs() == 0);
    REQUIRE(kb1.internal_generating_pairs().size() == 0);
    REQUIRE(kb1.generating_pairs().size() == 0);

    knuth_bendix::add_generating_pair(kb1, "ab", "ba");

    REQUIRE(kb1.number_of_generating_pairs() == 1);
    REQUIRE(kb1.internal_generating_pairs().size() == 2);
    REQUIRE(kb1.generating_pairs().size() == 2);

    kb1.init();

    REQUIRE(kb1.number_of_generating_pairs() == 0);
    REQUIRE(kb1.internal_generating_pairs().size() == 0);
    REQUIRE(kb1.generating_pairs().size() == 0);
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "017",
                                   "non-trivial classes",

                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("abc");
    presentation::add_rule_no_checks(p, "ab", "ba");
    presentation::add_rule_no_checks(p, "ac", "ca");
    presentation::add_rule_no_checks(p, "aa", "a");
    presentation::add_rule_no_checks(p, "ac", "a");
    presentation::add_rule_no_checks(p, "ca", "a");
    presentation::add_rule_no_checks(p, "bc", "cb");
    presentation::add_rule_no_checks(p, "bbb", "b");
    presentation::add_rule_no_checks(p, "bc", "b");
    presentation::add_rule_no_checks(p, "cb", "b");

    KnuthBendix<std::string, TestType> kb1(twosided, p);

    presentation::add_rule_no_checks(p, "a", "b");

    KnuthBendix<std::string, TestType> kb2(twosided, p);

    REQUIRE(knuth_bendix::contains(kb2, "a", "b"));
    REQUIRE(knuth_bendix::contains(kb2, "a", "ba"));
    REQUIRE(knuth_bendix::contains(kb2, "a", "bb"));
    REQUIRE(knuth_bendix::contains(kb2, "a", "bab"));

    REQUIRE(knuth_bendix::non_trivial_classes(kb1, kb2)
            == std::vector<std::vector<std::string>>(
                {{"b", "ab", "bb", "abb", "a"}}));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "018",
                                   "non-trivial classes x 2",

                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("abc");
    presentation::add_rule_no_checks(p, "ab", "ba");
    presentation::add_rule_no_checks(p, "ac", "ca");
    presentation::add_rule_no_checks(p, "aa", "a");
    presentation::add_rule_no_checks(p, "ac", "a");
    presentation::add_rule_no_checks(p, "ca", "a");
    presentation::add_rule_no_checks(p, "bc", "cb");
    presentation::add_rule_no_checks(p, "bbb", "b");
    presentation::add_rule_no_checks(p, "bc", "b");
    presentation::add_rule_no_checks(p, "cb", "b");

    KnuthBendix<std::string, TestType> kb1(twosided, p);
    REQUIRE(kb1.number_of_classes() == POSITIVE_INFINITY);

    presentation::add_rule_no_checks(p, "b", "c");

    KnuthBendix<std::string, TestType> kb2(twosided, p);
    REQUIRE(kb2.number_of_classes() == 2);

    REQUIRE_THROWS_AS(knuth_bendix::non_trivial_classes(kb1, kb2),
                      LibsemigroupsException);
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "019",
                                   "non-trivial classes x 3",

                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("abc");
    presentation::add_rule_no_checks(p, "ab", "ba");
    presentation::add_rule_no_checks(p, "ac", "ca");
    presentation::add_rule_no_checks(p, "aa", "a");
    presentation::add_rule_no_checks(p, "ac", "a");
    presentation::add_rule_no_checks(p, "ca", "a");
    presentation::add_rule_no_checks(p, "bc", "cb");
    presentation::add_rule_no_checks(p, "bbb", "b");
    presentation::add_rule_no_checks(p, "bc", "b");
    presentation::add_rule_no_checks(p, "cb", "b");

    KnuthBendix<std::string, TestType> kb1(twosided, p);

    presentation::add_rule_no_checks(p, "bb", "a");

    KnuthBendix<std::string, TestType> kb2(twosided, p);

    REQUIRE(knuth_bendix::non_trivial_classes(kb1, kb2)
            == std::vector<std::vector<std::string>>(
                {{"ab", "b"}, {"bb", "abb", "a"}}));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "020",
                                   "non-trivial classes x 4",

                                   "[quick][knuth-bendix]",
                                   REWRITER_TYPES) {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(4);
    presentation::add_rule_no_checks(p, 01_w, 10_w);
    presentation::add_rule_no_checks(p, 02_w, 20_w);
    presentation::add_rule_no_checks(p, 00_w, 0_w);
    presentation::add_rule_no_checks(p, 02_w, 0_w);
    presentation::add_rule_no_checks(p, 20_w, 0_w);
    presentation::add_rule_no_checks(p, 12_w, 21_w);
    presentation::add_rule_no_checks(p, 111_w, 1_w);
    presentation::add_rule_no_checks(p, 12_w, 1_w);
    presentation::add_rule_no_checks(p, 21_w, 1_w);
    presentation::add_rule_no_checks(p, 03_w, 0_w);
    presentation::add_rule_no_checks(p, 30_w, 0_w);
    presentation::add_rule_no_checks(p, 13_w, 1_w);
    presentation::add_rule_no_checks(p, 31_w, 1_w);
    presentation::add_rule_no_checks(p, 23_w, 2_w);
    presentation::add_rule_no_checks(p, 32_w, 2_w);

    KnuthBendix<word_type, TestType> kb1(twosided, p);

    presentation::add_rule_no_checks(p, 0_w, 1_w);

    KnuthBendix<word_type, TestType> kb2(twosided, p);
    REQUIRE(knuth_bendix::non_trivial_classes(kb1, kb2)
            == std::vector<std::vector<word_type>>(
                {{1_w, 01_w, 11_w, 011_w, 0_w}}));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "021",
                                   "non-triv. cong. on infinite fp semigp",
                                   "[quick][knuth-bendix][no-valgrind]",
                                   REWRITER_TYPES) {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(5);
    presentation::add_rule_no_checks(p, 01_w, 0_w);
    presentation::add_rule_no_checks(p, 10_w, 0_w);
    presentation::add_rule_no_checks(p, 02_w, 0_w);
    presentation::add_rule_no_checks(p, 20_w, 0_w);
    presentation::add_rule_no_checks(p, 03_w, 0_w);
    presentation::add_rule_no_checks(p, 30_w, 0_w);
    presentation::add_rule_no_checks(p, 00_w, 0_w);
    presentation::add_rule_no_checks(p, 11_w, 0_w);
    presentation::add_rule_no_checks(p, 22_w, 0_w);
    presentation::add_rule_no_checks(p, 33_w, 0_w);
    presentation::add_rule_no_checks(p, 12_w, 0_w);
    presentation::add_rule_no_checks(p, 21_w, 0_w);
    presentation::add_rule_no_checks(p, 13_w, 0_w);
    presentation::add_rule_no_checks(p, 31_w, 0_w);
    presentation::add_rule_no_checks(p, 23_w, 0_w);
    presentation::add_rule_no_checks(p, 32_w, 0_w);
    presentation::add_rule_no_checks(p, 40_w, 0_w);
    presentation::add_rule_no_checks(p, 41_w, 1_w);
    presentation::add_rule_no_checks(p, 42_w, 2_w);
    presentation::add_rule_no_checks(p, 43_w, 3_w);
    presentation::add_rule_no_checks(p, 04_w, 0_w);
    presentation::add_rule_no_checks(p, 14_w, 1_w);
    presentation::add_rule_no_checks(p, 24_w, 2_w);
    presentation::add_rule_no_checks(p, 34_w, 3_w);

    KnuthBendix<word_type, TestType> kb1(twosided, p);

    WordGraph test_wg1 = v4::make<WordGraph<size_t>>(
        6,
        {{1, 2, 3, 4, 5},
         {},
         {},
         {},
         {},
         {UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED, 5}});
    REQUIRE(kb1.number_of_classes() == POSITIVE_INFINITY);

    REQUIRE(
        equal((knuth_bendix::normal_forms(kb1) | rx::take(1000)),
              (normal_forms_from_word_graph(kb1, test_wg1) | rx::take(1000))));

    presentation::add_rule_no_checks(p, 1_w, 2_w);
    KnuthBendix<word_type, TestType> kb2(twosided, p);

    WordGraph test_wg2 = v4::make<WordGraph<size_t>>(
        5,
        {{1, 2, UNDEFINED, 3, 4},
         {},
         {},
         {},
         {UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED, 4}});

    REQUIRE(kb1.number_of_classes() == POSITIVE_INFINITY);
    REQUIRE(
        equal((knuth_bendix::normal_forms(kb2) | rx::take(1000)),
              (normal_forms_from_word_graph(kb2, test_wg2) | rx::take(1000))));

    REQUIRE(knuth_bendix::contains(kb2, 1_w, 2_w));

    auto ntc = knuth_bendix::non_trivial_classes(kb1, kb2);
    REQUIRE(ntc.size() == 1);
    REQUIRE(ntc[0].size() == 2);
    REQUIRE(ntc == decltype(ntc)({{{2}, {1}}}));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "022",
                                   "non-triv. cong. on infinite fp semigroup",
                                   "[quick][kbp]",
                                   REWRITER_TYPES) {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(5);
    presentation::add_rule_no_checks(p, 01_w, 0_w);
    presentation::add_rule_no_checks(p, 10_w, 0_w);
    presentation::add_rule_no_checks(p, 02_w, 0_w);
    presentation::add_rule_no_checks(p, 20_w, 0_w);
    presentation::add_rule_no_checks(p, 03_w, 0_w);
    presentation::add_rule_no_checks(p, 30_w, 0_w);
    presentation::add_rule_no_checks(p, 00_w, 0_w);
    presentation::add_rule_no_checks(p, 11_w, 0_w);
    presentation::add_rule_no_checks(p, 22_w, 0_w);
    presentation::add_rule_no_checks(p, 33_w, 0_w);
    presentation::add_rule_no_checks(p, 12_w, 0_w);
    presentation::add_rule_no_checks(p, 21_w, 0_w);
    presentation::add_rule_no_checks(p, 13_w, 0_w);
    presentation::add_rule_no_checks(p, 31_w, 0_w);
    presentation::add_rule_no_checks(p, 23_w, 0_w);
    presentation::add_rule_no_checks(p, 32_w, 0_w);
    presentation::add_rule_no_checks(p, 40_w, 0_w);
    presentation::add_rule_no_checks(p, 41_w, 2_w);
    presentation::add_rule_no_checks(p, 42_w, 3_w);
    presentation::add_rule_no_checks(p, 43_w, 1_w);
    presentation::add_rule_no_checks(p, 04_w, 0_w);
    presentation::add_rule_no_checks(p, 14_w, 2_w);
    presentation::add_rule_no_checks(p, 24_w, 3_w);
    presentation::add_rule_no_checks(p, 34_w, 1_w);

    KnuthBendix<word_type, TestType> kb1(twosided, p);

    presentation::add_rule_no_checks(p, 2_w, 3_w);

    KnuthBendix<word_type, TestType> kb2(twosided, p);
    auto ntc = knuth_bendix::non_trivial_classes(kb1, kb2);
    REQUIRE(ntc.size() == 1);
    REQUIRE(ntc[0].size() == 3);
    REQUIRE(ntc == decltype(ntc)({{{2}, {3}, {1}}}));
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "023",
                                   "triv. cong. on finite fp semigp",
                                   "[quick][kbp]",
                                   REWRITER_TYPES) {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(2);
    presentation::add_rule_no_checks(p, 001_w, 00_w);
    presentation::add_rule_no_checks(p, 0000_w, 00_w);
    presentation::add_rule_no_checks(p, 0110_w, 00_w);
    presentation::add_rule_no_checks(p, 0111_w, 000_w);
    presentation::add_rule_no_checks(p, 1110_w, 110_w);
    presentation::add_rule_no_checks(p, 1111_w, 111_w);
    presentation::add_rule_no_checks(p, 01000_w, 0101_w);
    presentation::add_rule_no_checks(p, 01010_w, 0100_w);
    presentation::add_rule_no_checks(p, 01011_w, 0101_w);

    KnuthBendix<word_type, TestType> kb1(twosided, p);
    KnuthBendix<word_type, TestType> kb2(twosided, p);

    REQUIRE(!p.contains_empty_word());
    REQUIRE(kb1.number_of_classes() == 27);
    REQUIRE(kb2.number_of_classes() == 27);
    auto ntc = knuth_bendix::non_trivial_classes(kb1, kb2);
    REQUIRE(ntc.empty());
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "024",
                                   "universal cong. on finite fp semigroup",
                                   "[quick][kbp]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<word_type> p;
    p.alphabet(2);
    presentation::add_rule_no_checks(p, 001_w, 00_w);
    presentation::add_rule_no_checks(p, 0000_w, 00_w);
    presentation::add_rule_no_checks(p, 0110_w, 00_w);
    presentation::add_rule_no_checks(p, 0111_w, 000_w);
    presentation::add_rule_no_checks(p, 1110_w, 110_w);
    presentation::add_rule_no_checks(p, 1111_w, 111_w);
    presentation::add_rule_no_checks(p, 01000_w, 0101_w);
    presentation::add_rule_no_checks(p, 01010_w, 0100_w);
    presentation::add_rule_no_checks(p, 01011_w, 0101_w);

    KnuthBendix<word_type, TestType> kb1(twosided, p);

    presentation::add_rule_no_checks(p, 0_w, 1_w);
    presentation::add_rule_no_checks(p, 00_w, 0_w);

    KnuthBendix<word_type, TestType> kb2(twosided, p);

    REQUIRE(kb2.number_of_classes() == 1);

    auto ntc = knuth_bendix::non_trivial_classes(kb1, kb2);

    REQUIRE(ntc.size() == 1);
    REQUIRE(ntc[0].size() == 27);
    std::vector expected
        = {0_w,     1_w,     00_w,    01_w,    10_w,     11_w,    000_w,
           100_w,   010_w,   101_w,   011_w,   110_w,    111_w,   1000_w,
           0100_w,  1100_w,  1010_w,  0101_w,  1101_w,   1011_w,  11000_w,
           10100_w, 11010_w, 10101_w, 11011_w, 110100_w, 110101_w};
    std::sort(expected.begin(), expected.end());
    std::sort(ntc[0].begin(), ntc[0].end());
    REQUIRE(ntc[0] == expected);
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "025",
                                   "finite fp semigroup, size 16",

                                   "[quick][kbp]",
                                   REWRITER_TYPES) {
    auto rg = ReportGuard(false);

    Presentation<word_type> p;
    p.alphabet(11);
    presentation::add_rule_no_checks(p, {2}, {1});
    presentation::add_rule_no_checks(p, {4}, {3});
    presentation::add_rule_no_checks(p, {5}, {0});
    presentation::add_rule_no_checks(p, {6}, {3});
    presentation::add_rule_no_checks(p, {7}, {1});
    presentation::add_rule_no_checks(p, {8}, {3});
    presentation::add_rule_no_checks(p, {9}, {3});
    presentation::add_rule_no_checks(p, {10}, {0});
    presentation::add_rule_no_checks(p, {0, 2}, {0, 1});
    presentation::add_rule_no_checks(p, {0, 4}, {0, 3});
    presentation::add_rule_no_checks(p, {0, 5}, {0, 0});
    presentation::add_rule_no_checks(p, {0, 6}, {0, 3});
    presentation::add_rule_no_checks(p, {0, 7}, {0, 1});
    presentation::add_rule_no_checks(p, {0, 8}, {0, 3});
    presentation::add_rule_no_checks(p, {0, 9}, {0, 3});

    presentation::add_rule_no_checks(p, {0, 10}, {0, 0});
    presentation::add_rule_no_checks(p, {1, 1}, {1});
    presentation::add_rule_no_checks(p, {1, 2}, {1});
    presentation::add_rule_no_checks(p, {1, 4}, {1, 3});
    presentation::add_rule_no_checks(p, {1, 5}, {1, 0});
    presentation::add_rule_no_checks(p, {1, 6}, {1, 3});
    presentation::add_rule_no_checks(p, {1, 7}, {1});
    presentation::add_rule_no_checks(p, {1, 8}, {1, 3});
    presentation::add_rule_no_checks(p, {1, 9}, {1, 3});
    presentation::add_rule_no_checks(p, {1, 10}, {1, 0});
    presentation::add_rule_no_checks(p, {3, 1}, {3});
    presentation::add_rule_no_checks(p, {3, 2}, {3});
    presentation::add_rule_no_checks(p, {3, 3}, {3});
    presentation::add_rule_no_checks(p, {3, 4}, {3});
    presentation::add_rule_no_checks(p, {3, 5}, {3, 0});
    presentation::add_rule_no_checks(p, {3, 6}, {3});
    presentation::add_rule_no_checks(p, {3, 7}, {3});
    presentation::add_rule_no_checks(p, {3, 8}, {3});
    presentation::add_rule_no_checks(p, {3, 9}, {3});
    presentation::add_rule_no_checks(p, {3, 10}, {3, 0});
    presentation::add_rule_no_checks(p, {0, 0, 0}, {0});
    presentation::add_rule_no_checks(p, {0, 0, 1}, {1});
    presentation::add_rule_no_checks(p, {0, 0, 3}, {3});
    presentation::add_rule_no_checks(p, {0, 1, 3}, {1, 3});
    presentation::add_rule_no_checks(p, {1, 0, 0}, {1});
    presentation::add_rule_no_checks(p, {1, 0, 3}, {0, 3});
    presentation::add_rule_no_checks(p, {3, 0, 0}, {3});
    presentation::add_rule_no_checks(p, {0, 1, 0, 1}, {1, 0, 1});
    presentation::add_rule_no_checks(p, {0, 3, 0, 3}, {3, 0, 3});
    presentation::add_rule_no_checks(p, {1, 0, 1, 0}, {1, 0, 1});
    presentation::add_rule_no_checks(p, {1, 3, 0, 1}, {1, 0, 1});
    presentation::add_rule_no_checks(p, {1, 3, 0, 3}, {3, 0, 3});
    presentation::add_rule_no_checks(p, {3, 0, 1, 0}, {3, 0, 1});
    presentation::add_rule_no_checks(p, {3, 0, 3, 0}, {3, 0, 3});

    KnuthBendix<word_type, TestType> kb1(twosided, p);
    REQUIRE(kb1.gilman_graph().number_of_nodes() == 16);

    WordGraph test_wg1
        = v4::make<WordGraph<size_t>>(16,
                                      {{3,
                                        1,
                                        UNDEFINED,
                                        2,
                                        UNDEFINED,
                                        UNDEFINED,
                                        UNDEFINED,
                                        UNDEFINED,
                                        UNDEFINED,
                                        UNDEFINED,
                                        UNDEFINED},
                                       {6, UNDEFINED, UNDEFINED, 12},
                                       {7, UNDEFINED},
                                       {4, 5, UNDEFINED, 9},
                                       {},
                                       {8},
                                       {UNDEFINED, 11},
                                       {UNDEFINED, 14, UNDEFINED, 15},
                                       {},
                                       {10},
                                       {UNDEFINED, 14},
                                       {},
                                       {13},
                                       {UNDEFINED}});
    REQUIRE(equal(knuth_bendix::normal_forms(kb1),
                  normal_forms_from_word_graph(kb1, test_wg1)));

    presentation::add_rule_no_checks(p, {1}, {3});
    KnuthBendix<word_type, TestType> kb2(twosided, p);

    WordGraph test_wg2 = v4::make<WordGraph<size_t>>(4,
                                                     {{2,
                                                       1,
                                                       UNDEFINED,
                                                       UNDEFINED,
                                                       UNDEFINED,
                                                       UNDEFINED,
                                                       UNDEFINED,
                                                       UNDEFINED,
                                                       UNDEFINED,
                                                       UNDEFINED,
                                                       UNDEFINED},
                                                      {},
                                                      {3}});

    REQUIRE(equal(knuth_bendix::normal_forms(kb2),
                  normal_forms_from_word_graph(kb2, test_wg2)));

    auto ntc = knuth_bendix::non_trivial_classes(kb1, kb2);

    std::vector expected = {1_w,
                            3_w,
                            01_w,
                            03_w,
                            10_w,
                            30_w,
                            13_w,
                            010_w,
                            030_w,
                            101_w,
                            301_w,
                            303_w,
                            130_w,
                            0301_w};
    std::sort(expected.begin(), expected.end());
    std::sort(ntc[0].begin(), ntc[0].end());
    REQUIRE(ntc[0] == expected);
  }

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "026",
                                   "non_trivial_classes exceptions",
                                   "[quick][kbp]",
                                   REWRITER_TYPES) {
    Presentation<word_type> p;
    p.alphabet(1);
    KnuthBendix<word_type, TestType> kbp(twosided, p);

    {
      Presentation<word_type> q;
      q.alphabet(2);
      KnuthBendix<word_type, TestType> kbq(twosided, q);
      REQUIRE_THROWS_AS(knuth_bendix::non_trivial_classes(kbp, kbq),
                        LibsemigroupsException);
      //      REQUIRE(kbq.number_of_inactive_rules() == 0);
    }
    {
      presentation::add_rule_no_checks(p, 0000_w, 00_w);
      kbp.init(twosided, p);

      Presentation<word_type> q;
      q.alphabet(1);
      presentation::add_rule_no_checks(q, 00_w, 0_w);

      // auto kbq = knuth_bendix::make<TestType>(twosided, q);

      KnuthBendix<word_type, TestType> kbq(twosided, q);
      REQUIRE_THROWS_AS(knuth_bendix::non_trivial_classes(kbq, kbp),
                        LibsemigroupsException);
    }
  }

  ////////////////////////////////////////////////////////////////////////
  // Commented out test cases
  ////////////////////////////////////////////////////////////////////////

  // // This example verifies the nilpotence of the group using the Sims
  // // algorithm. The original presentation was <a,b| [b,a,b], [b,a,a,a,a],
  // // [b,a,a,a,b,a,a] >. (where [] mean left-normed commutators). The
  // // presentation here was derived by first applying the NQA to find the
  // // maximal nilpotent quotient, and then introducing new generators for
  // // the PCP generators. It is essential for success that reasonably low
  // // values of the maxstoredlen parameter are given.
  // LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
  //                                  "994",
  //                                  "kbmag/verifynilp",
  //                                  "[quick][knuth-bendix][kbmag][recursive]",
  //                                  RewritingSystemTrieRPC,
  //                                  RewritingSystemSetRPC) {
  //   auto rg = ReportGuard(false);

  //   Presentation<std::string> p;
  //   p.alphabet("hHgGfFyYdDcCbBaA").contains_empty_word(true);

  //   // presentation::add_inverse_rules(p, "HhGgFfYyDdCcBbAa");
  //   presentation::add_rule(p, "BAba", "c");
  //   presentation::add_rule(p, "CAca", "d");
  //   presentation::add_rule(p, "DAda", "y");
  //   presentation::add_rule(p, "YByb", "f");
  //   presentation::add_rule(p, "FAfa", "g");
  //   presentation::add_rule(p, "ga", "ag");
  //   presentation::add_rule(p, "GBgb", "h");
  //   presentation::add_rule(p, "cb", "bc");
  //   presentation::add_rule(p, "ya", "ay");

  //   KnuthBendix<std::string, TestType> kb(congruence_kind::twosided, p);

  //   kb.run();
  //   REQUIRE(kb.rewriting_system().confluent());
  //   REQUIRE(kb.rewriting_system().number_of_rules() == 9);

  //   REQUIRE(knuth_bendix::contains(kb, "BAba", "c"));
  //   REQUIRE(knuth_bendix::contains(kb, "CAca", "d"));
  //   REQUIRE(knuth_bendix::contains(kb, "DAda", "y"));
  //   REQUIRE(knuth_bendix::contains(kb, "YByb", "f"));
  //   REQUIRE(knuth_bendix::contains(kb, "FAfa", "g"));
  //   REQUIRE(knuth_bendix::contains(kb, "ga", "ag"));
  //   REQUIRE(knuth_bendix::contains(kb, "GBgb", "h"));
  //   REQUIRE(knuth_bendix::contains(kb, "cb", "bc"));
  //   REQUIRE(knuth_bendix::contains(kb, "ya", "ay"));
  //   REQUIRE(
  //       (kb.active_rules() | rx::to_vector())
  //       == std::vector<std::pair<std::string, std::string>>({{"ga", "ag"},
  //                                                            {"GBgb", "h"},
  //                                                            {"FAfa", "g"},
  //                                                            {"ya", "ay"},
  //                                                            {"YByb", "f"},
  //                                                            {"DAda", "y"},
  //                                                            {"cb", "bc"},
  //                                                            {"CAca", "d"},
  //                                                            {"BAba",
  //                                                            "c"}}));
  // }

  // //  A nonhopfian group
  // LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
  //                                  "996",
  //                                  "kbmag/nonhopf",
  //                                  "[quick][knuth-bendix][kbmag][recursive]",
  //                                  RewritingSystemTrieRPC,
  //                                  RewritingSystemSetRPC) {
  //   auto                      rg = ReportGuard(false);
  //   Presentation<std::string> p;

  //   p.contains_empty_word(true).alphabet("aAbB");
  //   presentation::add_inverse_rules(p, "AaBb");
  //   presentation::add_rule(p, "Baab", "aaa");

  //   KnuthBendix<std::string, TestType> kb(twosided, p);

  //   kb.run();
  //   REQUIRE(kb.rewriting_system().confluent());
  //   REQUIRE(kb.rewriting_system().number_of_rules() == 8);

  //   REQUIRE(knuth_bendix::contains(kb, "Baab", "aaa"));
  //   REQUIRE(
  //       (kb.active_rules() | rx::to_vector())
  //       == std::vector<std::pair<std::string, std::string>>({{"aA", ""},
  //                                                            {"Aa", ""},
  //                                                            {"bB", ""},
  //                                                            {"Bb", ""},
  //                                                            {"aaaB", "Baa"},
  //                                                            {"aab", "baaa"},
  //                                                            {"AB", "aaBAA"},
  //                                                            {"Ab",
  //                                                            "abAAA"}}));
  // }

  // LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
  //                                  "997",
  //                                  "kbmag/freenilpc3",
  //                                  "[quick][knuth-bendix][kbmag][recursive]",
  //                                  RewritingSystemTrieRPC,
  //                                  RewritingSystemSetRPC) {
  //   auto rg = ReportGuard(false);

  //   Presentation<std::string> p;
  //   p.alphabet("yYdDcCbBaA");
  //   // TODO add inverse rules
  //   presentation::add_rule(p, "BAba", "c");
  //   presentation::add_rule(p, "CAca", "d");
  //   presentation::add_rule(p, "CBcb", "y");
  //   presentation::add_rule(p, "da", "ad");
  //   presentation::add_rule(p, "ya", "ay");
  //   presentation::add_rule(p, "db", "bd");
  //   presentation::add_rule(p, "yb", "by");

  //   KnuthBendix<std::string, TestType> kb(twosided, p);

  //   REQUIRE(kb.rewriting_system().confluent());
  //   kb.run();
  //   REQUIRE(kb.rewriting_system().confluent());
  //   REQUIRE(kb.rewriting_system().number_of_rules() == 7);

  //   REQUIRE(knuth_bendix::contains(kb, "BAba", "c"));
  //   REQUIRE(knuth_bendix::contains(kb, "CAca", "d"));
  //   REQUIRE(knuth_bendix::contains(kb, "CBcb", "y"));
  //   REQUIRE(knuth_bendix::contains(kb, "da", "ad"));
  //   REQUIRE(knuth_bendix::contains(kb, "ya", "ay"));
  //   REQUIRE(knuth_bendix::contains(kb, "db", "bd"));
  //   REQUIRE(knuth_bendix::contains(kb, "yb", "by"));
  //   REQUIRE(
  //       (kb.active_rules() | rx::to_vector())
  //       == std::vector<std::pair<std::string, std::string>>({{"yb", "by"},
  //                                                            {"ya", "ay"},
  //                                                            {"db", "bd"},
  //                                                            {"da", "ad"},
  //                                                            {"CBcb", "y"},
  //                                                            {"CAca", "d"},
  //                                                            {"BAba",
  //                                                            "c"}}));
  // }

  // // Free nilpotent group of rank 2 and class 2
  // LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
  //                                  "998",
  //                                  "kbmag/nilp2",
  //                                  "[quick][knuth-bendix][kbmag][recursive]",
  //                                  RewritingSystemTrieRPC,
  //                                  RewritingSystemSetRPC) {
  //   auto                      rg = ReportGuard(false);
  //   Presentation<std::string> p;
  //   p.alphabet("cCbBaA").contains_empty_word(true);
  //   presentation::add_inverse_rules(p, "CcBbAa");
  //   presentation::add_rule_no_checks(p, "ba", "abc");
  //   presentation::add_rule_no_checks(p, "ca", "ac");
  //   presentation::add_rule_no_checks(p, "cb", "bc");

  //   KnuthBendix<std::string, TestType> kb(twosided, p);
  //   // REQUIRE(kb.rewriting_system().confluent());

  //   kb.run();
  //   REQUIRE(kb.rewriting_system().confluent());

  //   REQUIRE(kb.rewriting_system().number_of_rules() == 18);
  //   REQUIRE(kb.number_of_classes() == POSITIVE_INFINITY);
  // }

  // // monoid presentation of F(2,7) - should produce a monoid of length 30
  // // which is the same as the group, together with the empty word. This
  // // is a very difficult calculation indeed, however.
  // //
  // // KBMAG does not terminate when SHORTLEX order is used.
  // LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
  //                                  "999",
  //                                  "kbmag/f27monoid",
  //                                  "[fail][knuth-bendix][kbmag][recursive]",
  //                                  RewritingSystemTrieRPC,
  //                                  RewritingSystemSetRPC) {
  //   auto                      rg = ReportGuard(true);
  //   Presentation<std::string> p;
  //   p.alphabet("abcdefg");
  //   presentation::add_rule_no_checks(p, "ab", "c");
  //   presentation::add_rule_no_checks(p, "bc", "d");
  //   presentation::add_rule_no_checks(p, "cd", "e");
  //   presentation::add_rule_no_checks(p, "de", "f");
  //   presentation::add_rule_no_checks(p, "ef", "g");
  //   presentation::add_rule_no_checks(p, "fg", "a");
  //   presentation::add_rule_no_checks(p, "ga", "b");

  //   KnuthBendix<std::string, TestType> kb(twosided, p);
  //   REQUIRE(!kb.rewriting_system().confluent());

  //   kb.run();
  //   REQUIRE(kb.rewriting_system().confluent());
  //   REQUIRE(kb.rewriting_system().number_of_rules() == 32767);
  // }

  // // This example verifies the nilpotence of the group using the Sims
  // // algorithm. The original presentation was <a,b| [b,a,a,a],
  // // [b^-1,a,a,a], [a,b,b,b], [a^-1,b,b,b], [a,a*b,a*b,a*b],
  // // [a^-1,a*b,a*b,a*b] >. (where [] mean left-normed commutators. The
  // // presentation here was derived by first applying the NQA to find the
  // // maximal nilpotent quotient, and then introducing new generators for
  // // the PCP generators.
  // LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
  //                                  "932",
  //                                  "kbmag/heinnilp",
  //                                  "[fail][knuth-bendix][kbmag][recursive]",
  //                                  RewritingSystemTrieRPC) {
  //   auto rg = ReportGuard(true);

  //   Presentation<std::string> p;
  //   p.alphabet("fFyYdDcCbBaA");
  //   p.contains_empty_word(true);
  //   presentation::add_inverse_rules(p, "FfYyDdCcBbAa");
  //   presentation::add_rule(p, "BAba", "c");
  //   presentation::add_rule(p, "CAca", "d");
  //   presentation::add_rule(p, "CBcb", "y");
  //   presentation::add_rule(p, "DBdb", "f");
  //   presentation::add_rule(p, "cBCb", "bcBC");
  //   presentation::add_rule(p, "babABaBA", "abABaBAb");
  //   presentation::add_rule(p, "cBACab", "abcBAC");
  //   presentation::add_rule(p, "BabABBAbab", "aabABBAb");

  //   KnuthBendix<std::string, TestType, RecursivePathCompare> kb(twosided, p);
  //   REQUIRE(!kb.rewriting_system().confluent());
  //   knuth_bendix::by_overlap_length(kb);
  //   kb.run();
  //   REQUIRE(kb.rewriting_system().confluent());
  //   REQUIRE(kb.rewriting_system().number_of_rules() == 72);
  //   REQUIRE(kb.number_of_classes() == POSITIVE_INFINITY);
  //   auto rules1 = (kb.active_rules() | rx::to_vector());
  //   REQUIRE(rules1
  //           == std::vector<std::pair<std::string, std::string>>(
  //               {{"fF", ""},     {"Ff", ""},      {"yY", ""},
  //                {"Yy", ""},     {"dD", ""},      {"Dd", ""},
  //                {"cC", ""},     {"Cc", ""},      {"bB", ""},
  //                {"Bb", ""},     {"aA", ""},      {"Aa", ""},
  //                {"db", "bdf"},  {"cb", "bcy"},   {"ca", "acd"},
  //                {"ba", "abc"},  {"YB", "BY"},    {"cB", "BcY"},
  //                {"Yb", "bY"},   {"yb", "by"},    {"yB", "By"},
  //                {"yc", "cy"},   {"Yc", "cY"},    {"yC", "Cy"},
  //                {"CB", "BCy"},  {"Ba", "aBCy"},  {"Cb", "bCY"},
  //                {"YC", "CY"},   {"fy", "yf"},    {"YA", "AYf"},
  //                {"DB", "BDf"},  {"Ca", "aCD"},   {"DC", "CD"},
  //                {"fa", "af"},   {"fC", "Cf"},    {"yD", "Dy"},
  //                {"fB", "Bf"},   {"fc", "cf"},    {"fd", "df"},
  //                {"dC", "Cd"},   {"ya", "ayf"},   {"yd", "dy"},
  //                {"Dc", "cD"},   {"YD", "DY"},    {"dB", "BdF"},
  //                {"fD", "Df"},   {"fA", "Af"},    {"fb", "bf"},
  //                {"FB", "BF"},   {"CA", "ACdff"}, {"bA", "AbCdff"},
  //                {"Da", "aDff"}, {"FC", "CF"},    {"FY", "YF"},
  //                {"dA", "Adff"}, {"dc", "cd"},    {"Ya", "aYF"},
  //                {"Fc", "cF"},   {"yA", "AyF"},   {"Yd", "dY"},
  //                {"FD", "DF"},   {"cA", "AcDFF"}, {"Fa", "aF"},
  //                {"FA", "AF"},   {"Fb", "bF"},    {"BA", "ABcDYF"},
  //                {"Db", "bDF"},  {"fY", "Yf"},    {"Fy", "yF"},
  //                {"DA", "ADFF"}, {"Fd", "dF"},    {"da", "adFF"}}));

  //   // NOTE: recursive_path_compare (and all the other orders) use the
  //   numerical
  //   // value of the letters in the alphabet as the order on the alphabet, in
  //   // this example, the order on the alphabet is "fFyYdDcCbBaA" which is not
  //   // numerical order, hence the contorsions below.
  //   // TODO: make it so that we don't have the contorsions below, using the
  //   yet
  //   // to be implemented Alphabet objects

  //   v4::ToWord to_word(p.alphabet());
  //   auto       rules2
  //       = (rx::iterator_range(rules1.begin(), rules1.end())
  //          | rx::transform([&to_word](auto const& rule) {
  //              return std::pair(to_word(rule.first), to_word(rule.second));
  //            })
  //          | rx::to_vector());

  //   REQUIRE(rules2
  //           == std::vector<std::pair<word_type, word_type>>(
  //               {{{0, 1}, {}},
  //                {{1, 0}, {}},
  //                {{2, 3}, {}},
  //                {{3, 2}, {}},
  //                {{4, 5}, {}},
  //                {{5, 4}, {}},
  //                {{6, 7}, {}},
  //                {{7, 6}, {}},
  //                {{8, 9}, {}},
  //                {{9, 8}, {}},
  //                {{10, 11}, {}},
  //                {{11, 10}, {}},
  //                {{4, 8}, {8, 4, 0}},
  //                {{6, 8}, {8, 6, 2}},
  //                {{6, 10}, {10, 6, 4}},
  //                {{8, 10}, {10, 8, 6}},
  //                {{3, 9}, {9, 3}},
  //                {{6, 9}, {9, 6, 3}},
  //                {{3, 8}, {8, 3}},
  //                {{2, 8}, {8, 2}},
  //                {{2, 9}, {9, 2}},
  //                {{2, 6}, {6, 2}},
  //                {{3, 6}, {6, 3}},
  //                {{2, 7}, {7, 2}},
  //                {{7, 9}, {9, 7, 2}},
  //                {{9, 10}, {10, 9, 7, 2}},
  //                {{7, 8}, {8, 7, 3}},
  //                {{3, 7}, {7, 3}},
  //                {{0, 2}, {2, 0}},
  //                {{3, 11}, {11, 3, 0}},
  //                {{5, 9}, {9, 5, 0}},
  //                {{7, 10}, {10, 7, 5}},
  //                {{5, 7}, {7, 5}},
  //                {{0, 10}, {10, 0}},
  //                {{0, 7}, {7, 0}},
  //                {{2, 5}, {5, 2}},
  //                {{0, 9}, {9, 0}},
  //                {{0, 6}, {6, 0}},
  //                {{0, 4}, {4, 0}},
  //                {{4, 7}, {7, 4}},
  //                {{2, 10}, {10, 2, 0}},
  //                {{2, 4}, {4, 2}},
  //                {{5, 6}, {6, 5}},
  //                {{3, 5}, {5, 3}},
  //                {{4, 9}, {9, 4, 1}},
  //                {{0, 5}, {5, 0}},
  //                {{0, 11}, {11, 0}},
  //                {{0, 8}, {8, 0}},
  //                {{1, 9}, {9, 1}},
  //                {{7, 11}, {11, 7, 4, 0, 0}},
  //                {{8, 11}, {11, 8, 7, 4, 0, 0}},
  //                {{5, 10}, {10, 5, 0, 0}},
  //                {{1, 7}, {7, 1}},
  //                {{1, 3}, {3, 1}},
  //                {{4, 11}, {11, 4, 0, 0}},
  //                {{4, 6}, {6, 4}},
  //                {{3, 10}, {10, 3, 1}},
  //                {{1, 6}, {6, 1}},
  //                {{2, 11}, {11, 2, 1}},
  //                {{3, 4}, {4, 3}},
  //                {{1, 5}, {5, 1}},
  //                {{6, 11}, {11, 6, 5, 1, 1}},
  //                {{1, 10}, {10, 1}},
  //                {{1, 11}, {11, 1}},
  //                {{1, 8}, {8, 1}},
  //                {{9, 11}, {11, 9, 6, 5, 3, 1}},
  //                {{5, 8}, {8, 5, 1}},
  //                {{0, 3}, {3, 0}},
  //                {{1, 2}, {2, 1}},
  //                {{5, 11}, {11, 5, 1, 1}},
  //                {{1, 4}, {4, 1}},
  //                {{4, 10}, {10, 4, 1, 1}}}));
  //   REQUIRE(std::all_of(rules2.begin(), rules2.end(), [](auto const& rule) {
  //     return recursive_path_compare(rule.second, rule.first);
  //   }));
  // }

}  // namespace libsemigroups
