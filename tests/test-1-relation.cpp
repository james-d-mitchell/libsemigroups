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

// TODO:
// * add a row or column for bua = a case
// * could try compressing presentations after Tietze transformations
// * Algorithm A doesn't help, it's a process for checking equality of given
// words in a 1-relation semigroup, not a means of solving the WP in general
// (i.e. it'd be necessary to run it for all pairs of words to know if the WP
// is solvable).
// * try a BFS in knuth_bendix_search

#define CATCH_CONFIG_ENABLE_PAIR_STRINGMAKER

#include <cstddef>  // for size_t
#include <fstream>  // for ofstream

#include "catch.hpp"      // for REQUIRE, REQUIRE_THROWS_AS, REQUI...
#include "test-main.hpp"  // for LIBSEMIGROUPS_TEST_CASE

#include "libsemigroups/kambites.hpp"      // for Kambites
#include "libsemigroups/knuth-bendix.hpp"  // for KnuthBendix
#include "libsemigroups/make-present.hpp"  // for make
#include "libsemigroups/present.hpp"       // for Presentation
#include "libsemigroups/siso.hpp"          // for Sislo
#include "libsemigroups/types.hpp"         // for word_type

#include "bitmap_image.hpp"

#include "fmt/color.h"
#include "fmt/printf.h"

namespace libsemigroups {

  enum class certificate : uint8_t {
    relation_words_have_equal_length = 0,
    self_overlap_free = 1,  // i.e. already confluent, terminating rewriting
                            // system if |u| > |v|, aka "hypersimple"
    C3                               = 2,
    C4                               = 3,
    knuth_bendix_terminates          = 4,
    equal_number_of_occurrences_of_a = 5,  // Theorem 4.9
    equal_number_of_occurrences_of_b = 6,  // Theorem 4.9
    watier1                          = 7,  // Theorem 4.10
    watier2                          = 8,  // Theorem 4.11
    unknown                          = 9,
  };

  auto const& certificate_map() {
    static const std::unordered_map<certificate, std::string> map
        = {{certificate::relation_words_have_equal_length,
            "relation words have equal length"},
           {certificate::self_overlap_free, "self overlap free"},
           {certificate::C3, "C(3) monoid"},
           {certificate::C4, "C(4) monoid"},
           {certificate::knuth_bendix_terminates, "Knuth-Bendix terminates"},
           {certificate::equal_number_of_occurrences_of_a,
            "equal number of occurrences of letter a"},
           {certificate::equal_number_of_occurrences_of_b,
            "equal number of occurrences of letter b"},
           {certificate::watier1, "watier1"},
           {certificate::watier2, "watier2"},
           {certificate::unknown, "unknown"}};
    return map;
  }
}  // namespace libsemigroups

CATCH_REGISTER_ENUM(
    libsemigroups::certificate,
    libsemigroups::certificate::relation_words_have_equal_length,
    libsemigroups::certificate::self_overlap_free,
    libsemigroups::certificate::C3,
    libsemigroups::certificate::C4,
    libsemigroups::certificate::knuth_bendix_terminates,
    libsemigroups::certificate::equal_number_of_occurrences_of_a,
    libsemigroups::certificate::equal_number_of_occurrences_of_b,
    libsemigroups::certificate::watier1,
    libsemigroups::certificate::watier2,
    libsemigroups::certificate::unknown);

namespace libsemigroups {
  namespace {
    using Kambites_    = fpsemigroup::Kambites<detail::MultiStringView>;
    using KnuthBendix_ = fpsemigroup::KnuthBendix;

    // TODO const& ??
    template <typename T, typename SFINAE = T>
    auto make(Presentation<std::string>& p)
        -> std::enable_if_t<std::is_same<Kambites_, T>::value, SFINAE> {
      T k;
      k.set_alphabet(p.alphabet());
      for (auto it = p.rules.cbegin(); it < p.rules.cend(); it += 2) {
        k.add_rule(*it, *(it + 1));
      }
      return k;
    }

    // TODO const& ??
    template <typename T, typename SFINAE = T>
    auto make(Presentation<std::string>& p)
        -> std::enable_if_t<std::is_same<KnuthBendix_, T>::value, SFINAE> {
      T k;
      k.set_alphabet(p.alphabet());
      for (auto it = p.rules.cbegin(); it < p.rules.cend(); it += 2) {
        k.add_rule(*it, *(it + 1));
      }
      return k;
    }

    template <typename T, typename SFINAE = T>
    auto make(KnuthBendix_ const& k)
        -> std::enable_if_t<std::is_same<Presentation<std::string>, T>::value,
                            SFINAE> {
      T p;
      p.alphabet(k.alphabet());
      for (auto const& rule : k.active_rules()) {
        p.rules.push_back(rule.first);
        p.rules.push_back(rule.second);
      }
      return p;
    }

    std::ostream& operator<<(std::ostream& file, Presentation<std::string> p) {
      file << "<";
      std::string sep = "";
      for (auto const& x : p.alphabet()) {
        file << sep << x;
        sep = ", ";
      }
      file << " | ";
      sep             = "";
      auto empty_word = u8"\u03B5";
      for (auto it = p.rules.cbegin(); it < p.rules.cend(); ++it) {
        file << sep << (it->empty() ? empty_word : *it) << " = ";
        ++it;
        file << (it->empty() ? empty_word : *it);
        sep = ", ";
      }
      file << ">";
      return file;
    }

    // is x a subword of y
    bool is_subword(std::string const& x, std::string const& y) {
      return y.find(x) != std::string::npos;
    }

    template <typename T>
    auto subwords(T first, T last) {
      std::unordered_set<std::string> mp;

      for (auto it = first; it < last; ++it) {
        auto const& w = *it;
        for (auto suffix = w.cbegin(); suffix < w.cend(); ++suffix) {
          for (auto prefix = suffix + 2; prefix < w.cend(); ++prefix) {
            mp.emplace(suffix, prefix);
          }
        }
      }
      std::vector<std::string> words(mp.cbegin(), mp.cend());
      std::sort(words.begin(), words.end(), [](auto const& u, auto const& v) {
        return shortlex_compare(v, u);
      });
      return words;
    }

    auto knuth_bendix_search(std::ofstream&             log_file,
                             Presentation<std::string>& p,
                             size_t                     max_depth,
                             std::chrono::milliseconds  run_for,
                             size_t                     depth = 0) {
      if (depth > max_depth) {
        return std::make_pair(false, depth);
      }
      auto                lphbt = p.alphabet();
      std::vector<size_t> perm(lphbt.size(), 0);
      std::iota(perm.begin(), perm.end(), 0);
      do {
        detail::apply_permutation(lphbt, perm);
        p.alphabet(lphbt);
        auto k = make<KnuthBendix_>(p);

        k.run_for(run_for);
        if (k.confluent()) {
          log_file << "[knuth-bendix] " << make<Presentation<std::string>>(k)
                   << std::endl;
          return std::make_pair(true, depth);
        }
      } while (std::next_permutation(perm.begin(), perm.end()));

      auto sbwrds = subwords(p.rules.cbegin(), p.rules.cend());

      for (auto const& w : sbwrds) {
        if (w.size() > 1) {
          auto q = Presentation<std::string>(p);
          presentation::replace_subword(q, w.cbegin(), w.cend());
          auto kb
              = knuth_bendix_search(log_file, q, max_depth, run_for, depth + 1);
          if (kb.first) {
            size_t const n = q.rules.size();
            log_file << "[generator " << q.rules[n - 2] << " = "
                     << q.rules[n - 1] << " added] " << q << std::endl;
            return std::make_pair(true, kb.second);
          }
        }
      }
      return std::make_pair(false, depth);
    }

    auto bitmap_init_XXX(size_t N) {
      bitmap_image bmp(N, N);
      bmp.clear();
      bmp.set_all_channels(255, 255, 255);
      return bmp;
    }

    const rgb_t colors[10]
        = {{64, 64, 64},   // relation_words_have_equal_length
           {204, 160, 0},  // self_overlap_free
           {255, 0, 255},  // C3
           {76, 0, 92},    // C4
           {0, 0, 0},      // NOT USED
           {0, 92, 49},    // equal_number_of_occurrences_of_a
           {43, 206, 72},  // equal_number_of_occurrences_of_b
           {0, 80, 157},   // watier1
           {0, 41, 107},   // watier2
           {0, 0, 0}};

    const std::array<rgb_t, 6> knuth_bendix_colors = {rgb_t({232, 93, 4}),
                                                      rgb_t({220, 47, 2}),
                                                      rgb_t({208, 0, 0}),
                                                      rgb_t({157, 2, 8}),
                                                      rgb_t({106, 4, 15}),
                                                      rgb_t({55, 6, 23})};

    fmt::rgb to_fmt_color(rgb_t const& x) {
      return fmt::rgb(x.red, x.green, x.blue);
    }

    rgb_t to_color(certificate c, size_t depth) {
      if (c != certificate::knuth_bendix_terminates) {
        return colors[static_cast<size_t>(c)];
      } else {
        return knuth_bendix_colors[depth];
      }
    }

    auto bitmap_color_XXX(bitmap_image& bmp,
                          size_t        x,
                          size_t        y,
                          certificate   c,
                          size_t        depth) {
      bmp.set_pixel(x, y, to_color(c, depth));
    }

    void print_key() {
      auto const&                                      map = certificate_map();
      size_t                                           max_text_len = 0;
      std::vector<std::pair<certificate, std::string>> vec;
      for (auto const& x : map) {
        if (x.second.size() > max_text_len) {
          max_text_len = x.second.size();
        }
        vec.push_back(x);
      }

      auto pad = [&max_text_len](std::string str) {
        return str + std::string(max_text_len - str.size(), ' ');
      };

      std::sort(vec.begin(), vec.end(), [](auto const& x, auto const& y) {
        return x.second < y.second;
      });

      for (auto const& x : vec) {
        if (x.first != certificate::knuth_bendix_terminates) {
          auto cert = static_cast<size_t>(x.first);
          auto colo = to_fmt_color(colors[cert]);
          fmt::print(fmt::emphasis::bold | fmt::bg(colo), pad(x.second));
          fmt::print(fmt::bg(fmt::color::black), "\n");
        }
      }
      for (size_t i = 0; i < knuth_bendix_colors.size(); ++i) {
        auto colo = to_fmt_color(knuth_bendix_colors[i]);
        fmt::print(
            fmt::emphasis::bold | fmt::bg(colo),
            pad("Knuth-Bendix terminates at depth " + std::to_string(i)));
        fmt::print(fmt::bg(fmt::color::black), "\n");
      }
    }

    // check if the number of consecutive b's at the start of u is longer than
    // any other sequence of consecutive b's in u
    auto watier1(std::string const& u) {
      LIBSEMIGROUPS_ASSERT(u.front() == 'b');
      auto   it0             = std::find(u.cbegin(), u.cend(), 'a');
      auto   it1             = u.cbegin();
      size_t num_leading_b_s = it0 - it1;

      while (it0 != u.cend()) {
        // Start of the next sequence of b's
        it1 = std::find(it0 + 1, u.cend(), 'b');
        if (it1 == u.cend()) {
          break;
        }
        // End of the next sequence of b's
        it0 = std::find(it1 + 1, u.cend(), 'a');
        if (static_cast<size_t>(it0 - it1) >= num_leading_b_s) {
          return false;
        }
      }
      return true;
    }

    template <typename W>
    auto has_decidable_word_problem(std::ofstream&            log_file,
                                    Presentation<W>&          p,
                                    size_t                    depth,
                                    size_t                    kb_max_depth,
                                    std::chrono::milliseconds kb_run_for) {
      LIBSEMIGROUPS_ASSERT(p.rules.size() == 2);

      auto const& u = p.rules[0];
      auto const& v = p.rules[1];

      LIBSEMIGROUPS_ASSERT(u.front() == 'b');
      LIBSEMIGROUPS_ASSERT(u.back() == 'a');
      LIBSEMIGROUPS_ASSERT(v.front() == 'a');
      LIBSEMIGROUPS_ASSERT(v.back() == 'a');

      if (u.size() == v.size()) {
        log_file << "[relation words have equal length] " << p << std::endl;
        return std::make_pair(certificate::relation_words_have_equal_length,
                              depth);
      }

      int a_count = 0;
      int b_count = 0;

      for (auto const& c : u) {
        if (c == 'a') {
          a_count++;
        } else if (c == 'b') {
          b_count++;
        }
      }

      for (auto const& c : v) {
        if (c == 'a') {
          a_count--;
        } else if (c == 'b') {
          b_count--;
        }
      }

      if (a_count == 0) {
        log_file << "[equal number of occurrences of a] " << p << std::endl;
        return std::make_pair(certificate::equal_number_of_occurrences_of_a,
                              depth);
      } else if (b_count == 0) {
        log_file << "[equal number of occurrences of b] " << p << std::endl;
        return std::make_pair(certificate::equal_number_of_occurrences_of_b,
                              depth);
      }

      if (watier1(u)) {
        // only this way around applies since u = bua and v = ava
        log_file << "[Watier 1] " << p << std::endl;
        return std::make_pair(certificate::watier1, depth);
      }

      if ((u.size() > v.size() && presentation::is_self_overlap_free(u))
          || (v.size() > u.size() && presentation::is_self_overlap_free(v))) {
        log_file << "[self-overlap free] " << p << std::endl;
        return std::make_pair(certificate::self_overlap_free, depth);
      } else if (v.size() >= u.size() * u.size()
                 && presentation::is_self_overlap_free(u)
                 && !is_subword(u, v)) {
        // only this way around applies since u = bua and v = ava
        log_file << "[Watier 2] " << p << std::endl;
        return std::make_pair(certificate::watier2, depth);
      }

      {
        auto k = make<Kambites_>(p);
        if (k.small_overlap_class() == 3) {
          log_file << "[C(3) monoid] " << p << std::endl;
          return std::make_pair(certificate::C3, depth);
        } else if (k.small_overlap_class() >= 4) {
          log_file << "[C(4) monoid] " << p << std::endl;
          return std::make_pair(certificate::C4, depth);
        }
      }

      // auto copy = p;
      // if (p.alphabet().size() > 2) {
      //   presentation::reduce_to_2_generators(copy);
      // }

      // bua = ava type presentations are never weakly compressible
      // if (presentation::is_weakly_compressible(copy)) {
      //   Presentation<std::string> precompressed(copy);
      //   presentation::weakly_compress(copy);
      //   auto c = has_decidable_word_problem(log_file, copy, depth + 1);
      //   if (c.first != certificate::unknown) {
      //     log_file << "[weakly compressed] " << precompressed
      //              << " (original) -> " << copy << " (compressed)" <<
      //              std::endl;
      //     if (p.alphabet().size() > 2) {
      //       log_file << "[reduced to 2-generators] " << p << " (original)
      //       ->
      //       "
      //                << copy << " (reduced)" << std::endl;
      //     }
      //     return c;
      //   }
      // }

      // bua = ava type presentations are never strongly compressible
      // if (presentation::is_strongly_compressible(copy)) {
      //   std::cout << "Here\n!";
      //   Presentation<std::string> precompressed(copy);
      //   presentation::strongly_compress(copy);
      //   auto c = has_decidable_word_problem(log_file, copy, depth + 1);
      //   if (c.first != certificate::unknown) {
      //     log_file << "[strongly compressed] " << precompressed
      //              << " (original) -> " << copy << " (compressed)" <<
      //              std::endl;
      //     if (p.alphabet().size() > 2) {
      //       log_file << "[reduced to 2-generators] " << p << " (original)
      //       ->
      //       "
      //                << copy << " (reduced)" << std::endl;
      //     }
      //     return c;
      //   }
      // }
      auto kb = knuth_bendix_search(log_file, p, kb_max_depth, kb_run_for);

      if (kb.first) {
        // p is 2-generated so we try that first
        // if (p.alphabet().size() > 2) {
        //   log_file << "[reduced to 2-generators] " << p << " (original) ->
        //   "
        //            << copy << " (reduced)" << std::endl;
        // }
        log_file << "[original presentation] " << p << std::endl;
        return std::make_pair(certificate::knuth_bendix_terminates,
                              depth + kb.second);
      }
      // Since we never compress, we can't have more than 2 generators
      // if (p.alphabet().size() > 2) {
      //   kb = knuth_bendix_search(log_file, p);
      //   if (kb.first) {
      //     log_file << "[reduced to 2-generators] " << p << " (original) ->
      //     "
      //              << copy << " (reduced)" << std::endl;
      //     return std::make_pair(certificate::knuth_bendix_terminates,
      //                           depth + kb.second);
      //   }
      // }

      log_file << "| FAILED |" << std::endl;
      return std::make_pair(certificate::unknown, depth);
    }

    template <typename W>
    auto has_decidable_word_problem(Presentation<W>&          p,
                                    size_t                    kb_depth = 2,
                                    std::chrono::milliseconds kb_run_for
                                    = std::chrono::milliseconds(5)) {
      std::string log_filename
          = std::string("tmp/") + p.rules[0] + "_" + p.rules[1] + ".txt";
      std::ofstream log_file(log_filename);
      auto          result
          = has_decidable_word_problem(log_file, p, 0, kb_depth, kb_run_for);
      log_file.close();
      fmt::print(fmt::emphasis::bold, "Writing {} . . .\n", log_filename);
      return result;
    }
  }  // namespace

  // LIBSEMIGROUPS_TEST_CASE("1-relation",
  //                         "000",
  //                         "special",
  //                         "[quick][presentation]") {
  //   Presentation<std::string> p;
  //   p.alphabet("ab");
  //   p.contains_empty_word(true);
  //   presentation::add_rule_and_check(p, "abaababb", "");
  //   REQUIRE(has_decidable_word_problem(p).first == certificate::special);
  // }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "001",
                          "relations of equal length",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "ba", "aa");
    REQUIRE(has_decidable_word_problem(p).first
            == certificate::relation_words_have_equal_length);
  }

  //      LIBSEMIGROUPS_TEST_CASE("1-relation",
  //                              "002",
  //                              "cycle-free",
  //                              "[quick][presentation]") {
  //        Presentation<std::string> p;
  //        p.alphabet("ab");
  //        presentation::add_rule_and_check(p, "ab", "baa");
  //        REQUIRE(has_decidable_word_problem(p).first ==
  //        certificate::cycle_free);
  //      }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "003",
                          "equal number of occurrences of b",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "baaa", "baa");
    REQUIRE(has_decidable_word_problem(p).first
            == certificate::equal_number_of_occurrences_of_b);
    p.rules.clear();
    presentation::add_rule_and_check(p, "baa", "baaa");
    REQUIRE(has_decidable_word_problem(p).first
            == certificate::equal_number_of_occurrences_of_b);
    p.rules.clear();
    presentation::add_rule_and_check(p, "abaababb", "abbaabb");
    REQUIRE(has_decidable_word_problem(p).first
            == certificate::equal_number_of_occurrences_of_b);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "004",
                          "equal_number_of_occurrences_of_a",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "bbbbbbaaab", "bababbbab");
    REQUIRE(has_decidable_word_problem(p).first
            == certificate::equal_number_of_occurrences_of_a);
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

  // Takes 0.7s with depth 1
  // TODO Check if this is still the case
  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "006",
                          "least unknown example",
                          "[extreme][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "bababbbabba", "a");
    auto c = has_decidable_word_problem(p, 2);
    REQUIRE(c.first == certificate::knuth_bendix_terminates);
    REQUIRE(c.second == 2);
  }

  // LIBSEMIGROUPS_TEST_CASE("1-relation",
  //                         "007",
  //                         "weakly compressible",
  //                         "[quick][presentation]") {
  //   Presentation<std::string> p;
  //   p.alphabet("ab");
  //   presentation::add_rule_and_check(p, "abaabbab", "ababaab");
  //   REQUIRE(presentation::is_weakly_compressible(p));  // not used
  //   REQUIRE(has_decidable_word_problem(p)
  //           ==
  //           std::make_pair(certificate::equal_number_of_occurrences_of_a,
  //                             size_t(0)));
  // }

  // LIBSEMIGROUPS_TEST_CASE("1-relation",
  //                         "008",
  //                         "free product monogenic and free",
  //                         "[quick][presentation]") {
  //   Presentation<std::string> p;
  //   p.alphabet("ab");
  //   presentation::add_rule_and_check(p, "aa", "a");
  //   REQUIRE(presentation::is_strongly_compressible(p));
  //   REQUIRE(has_decidable_word_problem(p)
  //           == std::make_pair(certificate::free_product_monogenic_free,
  //                             size_t(0)));
  // }

  // LIBSEMIGROUPS_TEST_CASE("1-relation",
  //                         "009",
  //                         "weakly compressible",
  //                         "[quick][presentation]") {
  //   Presentation<std::string> p;
  //   p.alphabet("ab");
  //   presentation::add_rule_and_check(p, "aba", "a");
  //   // This is strongly compressible but doesn't use that
  //   REQUIRE(presentation::is_strongly_compressible(p));
  //   REQUIRE(presentation::is_weakly_compressible(p));
  //   REQUIRE(
  //       has_decidable_word_problem(p)
  //       == std::make_pair(certificate::knuth_bendix_terminates,
  //       size_t(0)));
  // }

  // LIBSEMIGROUPS_TEST_CASE("1-relation",
  //                         "010",
  //                         "knuth_bendix_terminates",
  //                         "[quick][presentation]") {
  //   auto                      rg = ReportGuard(false);
  //   Presentation<std::string> p;
  //   p.alphabet("ab");
  //   presentation::add_rule_and_check(p, "bbbbb", "aaabaa");
  //   REQUIRE(
  //       has_decidable_word_problem(p)
  //       == std::make_pair(certificate::knuth_bendix_terminates,
  //       size_t(0)));
  // }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "011",
                          "knuth_bendix_terminates",
                          "[quick][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "ba", "aaa");
    REQUIRE(has_decidable_word_problem(p)
            == std::make_pair(certificate::watier1, size_t(0)));
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "012",
                          "sporadic bad 40",
                          "[quick][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "ba", "aabaaaa");
    REQUIRE(has_decidable_word_problem(p)
            == std::make_pair(certificate::equal_number_of_occurrences_of_b,
                              size_t(0)));
  }

  // 13m39s
  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "013",
                          "sporadic bad 50",
                          "[extreme][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "ba", "abaabaa");
    // REQUIRE(knuth_bendix_search(p));
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "014",
                          "sporadic bad 98",
                          "[extreme][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "ba", "abaaabaa");
    // REQUIRE(knuth_bendix_search(p));
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "015",
                          "sporadic bad 98",
                          "[extreme][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "ba", "abaaabaa");
    presentation::reverse(p);
    // REQUIRE(knuth_bendix_search(p));
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "016",
                          "weirdness",
                          "[extreme][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "baabaa", "aba");
    REQUIRE(has_decidable_word_problem(p).first == certificate::unknown);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "017",
                          "robustness",
                          "[quick][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "babaa", "abaaba");
    auto c = has_decidable_word_problem(p);
    REQUIRE(c.first == certificate::equal_number_of_occurrences_of_b);
    REQUIRE(c.second == 0);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "018",
                          "robustness",
                          "[quick][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "baaaa", "abbaba");
    auto c = has_decidable_word_problem(p);
    REQUIRE(c.first == certificate::watier1);
    REQUIRE(c.second == 0);
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "019",
                          "watier1",
                          "[quick][presentation]") {
    REQUIRE(watier1("baaaa"));
    REQUIRE(watier1("bbbabbaab"));
    REQUIRE(!watier1("bbbabbaabbbb"));
    REQUIRE(!watier1("bbbabbbabaa"));
    REQUIRE(!watier1("bbbabbababbabbb"));
    REQUIRE(watier1("bbbbbb"));
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "998",
                          "strongly compressible",
                          "[fail][presentation]") {
    // Doesn't fail just don't want to run
    print_key();
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "999",
                          "solve for bua = ava where |u|, |v| < 10",
                          "[fail][presentation]") {
    // Doesn't fail just slow
    // knuth_bendix max_depth = 2, and run KnuthBendix for 5ms
    auto  rg = ReportGuard(false);
    Sislo s;
    s.alphabet("ab").first("").last("aaaaaaaaaa");
    auto bmp = bitmap_init_XXX(std::distance(s.cbegin(), s.cend()));
    // REQUIRE(bmp.width() == 0);
    Presentation<std::string> p;
    p.alphabet("ab");
    size_t                   x           = 0;
    uint64_t                 undecidable = 0;
    std::vector<std::string> bad;
    for (auto u = s.cbegin(); u != s.cend(); ++u) {
      size_t y = 0;
      auto   U = std::string("b") + *u + "a";
      // TODO V = "a"
      for (auto v = s.cbegin(); v != s.cend(); ++v) {
        auto V = std::string("a") + *v + "a";
        p.rules.clear();
        presentation::add_rule(p, U, V);
        auto c = has_decidable_word_problem(p, 1, std::chrono::milliseconds(2));
        bitmap_color_XXX(bmp, x, y, c.first, c.second);
        std::cout << U << " = " << V << " is ";
        if (c.first == certificate::unknown) {
          ++undecidable;
          std::cout << "BAD" << std::endl;
          bad.push_back(*u);
          bad.push_back(*v);
        } else {
          std::cout << "good (depth " << c.second << ")" << std::endl;
        }
        ++y;
      }
      ++x;
    }

    size_t depth = 1;
    while (!bad.empty()) {
      std::vector<std::string> next_bad;
      std::cout << "Total " << bmp.width() * bmp.width() << " instances!"
                << std::endl;
      std::cout << "Couldn't solve " << undecidable << " instances!"
                << std::endl;
      std::cout << "Writing 2_gen_1_rel.bmp . . ." << std::endl;
      bmp.save_image("2_gen_1_rel.bmp");
      undecidable = 0;
      depth       = depth + 1;

      for (auto it = bad.cbegin(); it != bad.cend(); it += 2) {
        p.rules.clear();
        auto u = it, v = (it + 1);
        auto U = std::string("b") + *u + "a", V = std::string("a") + *v + "a";
        presentation::add_rule(p, U, V);
        auto c = has_decidable_word_problem(
            p, depth, std::chrono::milliseconds(5));
        std::cout << U << " = " << V << " is ";
        if (c.first != certificate::unknown) {
          size_t x = s.position(*u);
          size_t y = s.position(*v);
          bitmap_color_XXX(bmp, x, y, c.first, c.second);
          std::cout << "good (depth " << c.second << ")" << std::endl;
        } else {
          ++undecidable;
          next_bad.push_back(std::move(*u));
          next_bad.push_back(std::move(*v));
          std::cout << "BAD" << std::endl;
        }
      }
      std::swap(bad, next_bad);
      if (depth == 3) {
        break;
      }
    }

    std::cout << "Total " << bmp.width() * bmp.width() << " instances!"
              << std::endl;
    std::cout << "Couldn't solve " << undecidable << " instances!" << std::endl;
    std::cout << "Writing 2_gen_1_rel.bmp . . ." << std::endl;
    bmp.save_image("2_gen_1_rel.bmp");
    print_key();
    // REQUIRE(undecidable == 16);
  }

}  // namespace libsemigroups
   //  std::string const& to_string(certificate c) {
   //    return certificate_map().find(c)->second;
   //  }
   //
   //  std::ostream& operator<<(std::ostream& os, certificate const& c) {
   //    os << to_string(c);
   //    return os;
   //  }
   //  auto const& reduction_map() {
   //    static const std::unordered_map<reduction, std::string> map
   //        = {{reduction::normalize_alphabet, "alphabet normalized"},
   //           {reduction::weakly_compress, "weakly compressed"},
   //           {reduction::strongly_compress, "strongly compressed"},
   //           {reduction::tietze, "tietze"},
   //           {reduction::reduce_to_2_generators, "reduced to
   //           2-generators"}, {reduction::knuth_bendix, "Knuth-Bendix
   //           active rules"}, {reduction::none, "none"}};
   //    return map;
   //  }
   //
   //  std::string const& to_string(reduction c) {
   //    return reduction_map().find(c)->second;
   //  }
   //
   //  std::ostream& operator<<(std::ostream& os, reduction const& c) {
   //    os << to_string(c);
   //    return os;
   //  }
   // template <typename Function>
   // Presentation<std::string> find_example(size_t min_depth, Function&&
   // pred)
   // {
   //   Sislo s;
   //   s.alphabet("ab").first("a").last("aaaaaaaaaaa");
   //   Presentation<std::string> p;
   //   p.alphabet("ab");
   //   for (auto u = s.cbegin(); u != s.cend(); ++u) {
   //     for (auto v = u + 1; v != s.cend(); ++v) {
   //       p.rules.clear();
   //       presentation::add_rule(p, *u, *v);
   //       if (pred(p)) {
   //         if (has_decidable_word_problem(p).second >= min_depth) {
   //           return p;
   //         }
   //       }
   //     }
   //   }
   //   p.rules.clear();
   //   return p;
   // }
   //  enum class reduction : uint8_t {
   //    normalize_alphabet     = 0,
   //    weakly_compress        = 1,
   //    strongly_compress      = 2,
   //    tietze                 = 3,
   //    reduce_to_2_generators = 4,
   //    knuth_bendix           = 5,
   //    none                   = 255
   //  };
   // CATCH_REGISTER_ENUM(libsemigroups::reduction,
   //                    libsemigroups::reduction::normalize_alphabet,
   //                    libsemigroups::reduction::weakly_compress,
   //                    libsemigroups::reduction::strongly_compress,
   //                    libsemigroups::reduction::tietze,
   //                    libsemigroups::reduction::reduce_to_2_generators,
   //                    libsemigroups::reduction::none);
   // enum class certificate : uint8_t {
   //  special                          = 0,  // one side of one word is
   //  empty cycle_free                       = 1,  // aub = bva
   //  relation_words_have_equal_length = 2,
   //  self_overlap_free = 3,  // i.e. already confluent, terminating
   //  rewriting
   //                          // system if |u| > |v|, aka "hypersimple"
   //  C3                               = 4,
   //  C4                               = 5,
   //  free_product_monogenic_free      = 6,  // relation of form a ^ k = a
   //  knuth_bendix_terminates          = 7,
   //  monogenic                        = 8,
   //  equal_number_of_occurrences_of_a = 9,   // Theorem 4.9
   //  equal_number_of_occurrences_of_b = 10,  // Theorem 4.9
   //  watier1                          = 12,  // Theorem 4.10
   //  watier2                          = 12,  // Theorem 4.11
   //  unknown                          = 37,
   //  none                             = 255
   //};
