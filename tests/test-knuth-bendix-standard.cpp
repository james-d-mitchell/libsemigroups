// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2020-2026 James D. Mitchell
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

#include "libsemigroups/knuth-bendix-helpers.hpp"
#define CATCH_CONFIG_ENABLE_ALL_STRINGMAKERS

#include <algorithm>      // for next_permutation
#include <chrono>         // for milliseconds, seconds
#include <cmath>          // for pow
#include <cstddef>        // for size_t
#include <iostream>       // for string, operator<<, endl
#include <numeric>        // for iota
#include <string>         // for basic_string, char_traits
#include <unordered_set>  // for unordered_set
#include <utility>        // for move, operator==, pair
#include <vector>         // for vector, operator==

#include "Catch2-3.14.0/catch_amalgamated.hpp"  // for AssertionHandler, oper...
#include "test-main.hpp"  // for LIBSEMIGROUPS_TEMPLATE_TEST_CASE

#include "libsemigroups/constants.hpp"  // for operator==, operat...
#include "libsemigroups/detail/rules.hpp"
#include "libsemigroups/exception.hpp"              // for LibsemigroupsExcep...
#include "libsemigroups/knuth-bendix.hpp"           // for KnuthBendix, norma...
#include "libsemigroups/order.hpp"                  // for shortlex_compare
#include "libsemigroups/paths.hpp"                  // for Paths
#include "libsemigroups/presentation-examples.hpp"  // for partition_mo
#include "libsemigroups/presentation.hpp"           // for add_rule, Presenta...
#include "libsemigroups/word-graph-helpers.hpp"     // for word_graph
#include "libsemigroups/word-graph.hpp"             // for WordGraph
#include "libsemigroups/word-range.hpp"             // for Inner, StringRange...

#include "libsemigroups/detail/report.hpp"  // for ReportGuard
#include "libsemigroups/detail/stl.hpp"     // for apply_permutation
#include "libsemigroups/detail/string.hpp"  // for random_string, operator<<

namespace libsemigroups {
  using literals::operator""_w;

  congruence_kind constexpr twosided = congruence_kind::twosided;

  using namespace rx;

  using LenLexTrie = detail::RewritingSystemTrie<ShortLexCompare>;
  using LenLexSet  = detail::RewritingSystemSet<ShortLexCompare>;
  using RPOTrie    = detail::RewritingSystemTrie<RecursivePathCompare>;
  using RPOSet     = detail::RewritingSystemSet<RecursivePathCompare>;

#define REWRITING_SYSTEM_TYPES LenLexTrie, LenLexSet  // RPOTrie, RPOSet

  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "065",
                                   "sigma sylvester monoid x 2",
                                   "[knuth-bendix][standard]",
                                   REWRITING_SYSTEM_TYPES) {
    using namespace literals;
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(2);
    presentation::add_idempotent_rules_no_checks(p, 01_w);
    using words::operator+;
    WordRange words;
    words.alphabet_size(2).min(0).max(6);
    size_t n = 2;
    for (size_t a = 0; a < n - 1; ++a) {
      for (size_t b = a; b < n - 1; ++b) {
        for (size_t c = b + 1; c < n; ++c) {
          for (auto& u : words) {
            for (auto& v : words) {
              for (auto& w : words) {
                presentation::add_rule(
                    p, u + a + c + v + b + w, u + c + a + v + b + w);
              }
            }
          }
        }
      }
    }
    presentation::sort_each_rule(p);
    presentation::sort_rules(p);
    presentation::remove_trivial_rules(p);
    p.contains_empty_word(true);
    std::reverse(p.rules.begin(), p.rules.end());

    KnuthBendix<word_type, TestType> kb(twosided, p);

    auto S = to<FroidurePin>(kb);
    REQUIRE(S.contains_one());
    REQUIRE(S.size() == kb.number_of_classes());
    REQUIRE(S.number_of_idempotents() == 5);
    REQUIRE(kb.number_of_classes() == 6);
  }

  // Takes approx. 2s
  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "100",
                                   "Sims Ex. 6.6 (limited overlap lengths)",
                                   "[standard][knuth-bendix]",
                                   REWRITING_SYSTEM_TYPES) {
    using order = typename TestType::reduction_order;
    auto rg     = ReportGuard(false);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("abc");

    presentation::add_rule(p, "aa", "");
    presentation::add_rule(p, "bc", "");
    presentation::add_rule(p, "bbb", "");
    presentation::add_rule(p, "ababababababab", "");
    presentation::add_rule(p, "abacabacabacabacabacabacabacabac", "");

    KnuthBendix<std::string, TestType> kb(twosided, p);
    REQUIRE(kb.overlap_policy() == decltype(kb)::options::overlap::ABC);

    REQUIRE(!kb.rewriting_system().confluent());

    if constexpr (std::is_same_v<order, ShortLexCompare>) {
      // In Sims it says to use 44 here, but that doesn't seem to work.
      kb.max_overlap(45);
      kb.run();
      REQUIRE(kb.rewriting_system().number_of_rules() == 1'026);
      // REQUIRE(kb.rewriting_system().confluent());
      // REQUIRE(kb.number_of_classes() == 10'752);
    } else if (std::is_same_v<order, RecursivePathCompare>) {
      kb.max_overlap(55);
      kb.run();
      // FIXME something wrong here
      REQUIRE(kb.rewriting_system().number_of_rules() == 408);
    }
  }

  // Takes approx. 2s, is very slow with RPO
  LIBSEMIGROUPS_TEMPLATE_TEST_CASE("KnuthBendix",
                                   "101",
                                   "kbmag/standalone/kb_data/funny3",
                                   "[standard][knuth-bendix][kbmag][shortlex]",
                                   LenLexSet,
                                   LenLexTrie) {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("aAbBcC");

    presentation::add_inverse_rules(p, "AaBbCc");

    presentation::add_rule(p, "aaa", "");
    presentation::add_rule(p, "bbb", "");
    presentation::add_rule(p, "ccc", "");
    presentation::add_rule(p, "ABa", "BaB");
    presentation::add_rule(p, "bcB", "cBc");
    presentation::add_rule(p, "caC", "aCa");
    presentation::add_rule(p, "abcABCabcABCabcABC", "");
    presentation::add_rule(p, "BcabCABcabCABcabCA", "");
    presentation::add_rule(p, "cbACBacbACBacbACBa", "");

    KnuthBendix<std::string, TestType> kb(twosided, p);
    REQUIRE(!kb.rewriting_system().confluent());
    REQUIRE(kb.overlap_policy() == decltype(kb)::options::overlap::ABC);

    kb.rewriting_system().settings().reduction_threshold = 200;
    knuth_bendix::by_overlap_length(kb);
    // kb.run() // also works, but is slower
    REQUIRE(kb.rewriting_system().confluent());
    REQUIRE(kb.rewriting_system().number_of_rules() == 8);
    REQUIRE(kb.number_of_classes() == 3);
    auto nf = knuth_bendix::normal_forms(kb);
    REQUIRE((nf | to_vector()) == std::vector<std::string>({"", "a", "A"}));
  }

}  // namespace libsemigroups
