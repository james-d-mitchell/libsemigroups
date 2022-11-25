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

#define CATCH_CONFIG_ENABLE_PAIR_STRINGMAKER

#include <cstddef>  // for size_t

#include "catch.hpp"      // for REQUIRE, REQUIRE_THROWS_AS, REQUI...
#include "test-main.hpp"  // for LIBSEMIGROUPS_TEST_CASE

#include "libsemigroups/bipart.hpp"        // for Bipartition
#include "libsemigroups/containers.hpp"    // for StaticVector1
#include "libsemigroups/froidure-pin.hpp"  // for FroidurePin
#include "libsemigroups/kambites.hpp"      // for Kambites
#include "libsemigroups/knuth-bendix.hpp"  // for redundant_rule
#include "libsemigroups/make-present.hpp"  // for make
#include "libsemigroups/present.hpp"       // for Presentation
#include "libsemigroups/siso.hpp"          // for Sislo
#include "libsemigroups/types.hpp"         // for word_type

namespace libsemigroups {
  enum class certificate {
    special,     // one side of one word is empty
    cycle_free,  // aub = bva
    relation_words_have_equal_length,
    self_overlap_free,  // i.e. already confluent, terminating rewriting
                        // system if |u| > |v|, aka "hypersimple"
    C3,
    C4,
    free_product_monogenic_free,
    unknown
  };
}

CATCH_REGISTER_ENUM(
    libsemigroups::certificate,
    libsemigroups::certificate::special,
    libsemigroups::certificate::cycle_free,  // aub = bva
    libsemigroups::certificate::relation_words_have_equal_length,
    libsemigroups::certificate::self_overlap_free,
    libsemigroups::certificate::C3,
    libsemigroups::certificate::C4,
    libsemigroups::certificate::free_product_monogenic_free,
    libsemigroups::certificate::unknown);

namespace libsemigroups {
  namespace {
    using Kambites_ = fpsemigroup::Kambites<detail::MultiStringView>;

    template <typename T,
              typename = std::enable_if_t<std::is_same<Kambites_, T>::value>>
    T make(Presentation<std::string>& p) {
      T k;
      k.set_alphabet(p.alphabet());
      for (auto it = p.rules.cbegin(); it < p.rules.cend(); it += 2) {
        k.add_rule(*it, *(it + 1));
      }
      return k;
    }

    template <typename W>
    auto has_decidable_word_problem(Presentation<W>& p, size_t depth = 0) {
      if (p.rules.size() != 2) {
        LIBSEMIGROUPS_EXCEPTION("TODO");
      }
      auto const& u = p.rules[0];
      auto const& v = p.rules[1];

      if (u.empty() || v.empty()) {
        return std::make_pair(certificate::special, depth);
      } else if (u.size() == v.size()) {
        return std::make_pair(certificate::relation_words_have_equal_length,
                              depth);
      } else if (u.front() == v.back() && v.front() == u.back()
                 && u.front() != u.back()) {
        return std::make_pair(certificate::cycle_free, depth);
      }

      for (auto it = p.alphabet().cbegin(); it != p.alphabet().cend(); ++it) {
        if (std::search(u.cbegin(), u.cend(), it, it + 1) == u.cend()
            && std::search(v.cbegin(), v.cend(), it, it + 1) == v.cend()) {
          return std::make_pair(certificate::free_product_monogenic_free,
                                depth);
        }
      }

      if ((u.size() > v.size() && presentation::is_self_overlap_free(u))
          || (v.size() > u.size() && presentation::is_self_overlap_free(v))) {
        return std::make_pair(certificate::self_overlap_free, depth);
      }
      auto k = make<Kambites_>(p);
      if (k.small_overlap_class() == 3) {
        return std::make_pair(certificate::C3, depth);
      } else if (k.small_overlap_class() >= 4) {
        return std::make_pair(certificate::C4, depth);
      }

      // TODO(do a proper search here!)
      if (presentation::is_weakly_compressible(p)) {
        auto copy = p;
        presentation::weakly_compress(copy);
        return has_decidable_word_problem(copy, depth + 1);
      } else if (presentation::is_strongly_compressible(p)) {
        auto copy = p;
        presentation::strongly_compress(copy);
        return has_decidable_word_problem(copy, depth + 1);
      }

      return std::make_pair(certificate::unknown, depth);
    }

    template <typename Function>
    Presentation<std::string> find_example(size_t min_depth, Function&& pred) {
      Sislo s;
      s.alphabet("ab").first("a").last("aaaaaaaaaaa");
      Presentation<std::string> p;
      p.alphabet("ab");
      for (auto u = s.cbegin(); u != s.cend(); ++u) {
        for (auto v = u + 1; v != s.cend(); ++v) {
          p.rules.clear();
          presentation::add_rule(p, *u, *v);
          if (pred(p)) {
            if (has_decidable_word_problem(p).second >= min_depth) {
              return p;
            }
          }
        }
      }
      p.rules.clear();
      return p;
    }
  }  // namespace

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "000",
                          "special",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    p.contains_empty_word(true);
    presentation::add_rule_and_check(p, "abaababb", "");
    REQUIRE(has_decidable_word_problem(p).first == certificate::special);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "001",
                          "relations of equal length",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "ab", "ba");
    REQUIRE(has_decidable_word_problem(p).first
            == certificate::relation_words_have_equal_length);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "002",
                          "cycle-free",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "ab", "baa");
    REQUIRE(has_decidable_word_problem(p).first == certificate::cycle_free);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "003",
                          "self-overlap free",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "baaa", "baa");
    REQUIRE(has_decidable_word_problem(p).first
            == certificate::self_overlap_free);
    p.rules.clear();
    presentation::add_rule_and_check(p, "baa", "baaa");
    REQUIRE(has_decidable_word_problem(p).first
            == certificate::self_overlap_free);
    p.rules.clear();
    presentation::add_rule_and_check(p, "abaababb", "abbaabb");
    REQUIRE(has_decidable_word_problem(p).first
            == certificate::self_overlap_free);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "004",
                          "C(4)",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "bbbbbbaaab", "bababbbab");
    REQUIRE(has_decidable_word_problem(p).first == certificate::C4);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "005",
                          "C(3)",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "aaba", "abbab");
    REQUIRE(has_decidable_word_problem(p).first == certificate::C3);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "006",
                          "unknown",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "bababbbabba", "a");
    REQUIRE(has_decidable_word_problem(p).first == certificate::unknown);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "007",
                          "weakly compressible",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "abaabbab", "ababaab");
    REQUIRE(presentation::is_weakly_compressible(p));
    REQUIRE(has_decidable_word_problem(p)
            == std::make_pair(certificate::self_overlap_free, size_t(1)));
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "008",
                          "free product monogenic and free",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "aa", "a");
    REQUIRE(presentation::is_strongly_compressible(p));
    REQUIRE(
        has_decidable_word_problem(p)
        == std::make_pair(certificate::free_product_monogenic_free, size_t(0)));
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "009",
                          "strongly compressible",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "aba", "a");
    REQUIRE(presentation::is_strongly_compressible(p));
    REQUIRE(has_decidable_word_problem(p)
            == std::make_pair(certificate::special, size_t(1)));
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "999",
                          "strongly compressible",
                          "[quick][presentation]") {
    auto p = find_example(1, [](auto const& p) {
      return presentation::is_strongly_compressible(p);
    });
    REQUIRE(p.rules == std::vector<std::string>());
  }

}  // namespace libsemigroups
