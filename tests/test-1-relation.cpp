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
    // NEVER for bua = ava
    special = 0,  // one side of one word is empty
    // NEVER for bua = ava
    cycle_free                       = 1,  // aub = bva
    relation_words_have_equal_length = 2,
    self_overlap_free = 3,  // i.e. already confluent, terminating rewriting
                            // system if |u| > |v|, aka "hypersimple"
    C3 = 4,
    C4 = 5,
    // NEVER for bua = ava
    free_product_monogenic_free = 6,  // relation of form a ^ k = a
    knuth_bendix_terminates     = 7,
    // NEVER for bua = ava
    monogenic                        = 8,
    equal_number_of_occurrences_of_a = 9,   // Theorem 4.9
    equal_number_of_occurrences_of_b = 10,  // Theorem 4.9
    unknown                          = 37,
    none                             = 255
  };

  auto const& certificate_map() {
    static const std::unordered_map<certificate, std::string> map
        = {{certificate::special, "special"},
           {certificate::cycle_free, "cycle-free"},
           {certificate::relation_words_have_equal_length,
            "relation words have equal length"},
           {certificate::self_overlap_free, "self overlap free"},
           {certificate::C3, "C(3) monoid"},
           {certificate::C4, "C(4) monoid"},
           {certificate::free_product_monogenic_free,
            "free product monogenic and free"},
           {certificate::knuth_bendix_terminates, "Knuth-Bendix terminates"},
           {certificate::unknown, "unknown"},
           {certificate::none, "none"}};
    return map;
  }

  enum class reduction : uint8_t {
    normalize_alphabet     = 0,
    weakly_compress        = 1,
    strongly_compress      = 2,
    tietze                 = 3,
    reduce_to_2_generators = 4,
    knuth_bendix           = 5,
    none                   = 255
  };

}  // namespace libsemigroups

CATCH_REGISTER_ENUM(
    libsemigroups::certificate,
    libsemigroups::certificate::special,
    libsemigroups::certificate::cycle_free,
    libsemigroups::certificate::relation_words_have_equal_length,
    libsemigroups::certificate::self_overlap_free,
    libsemigroups::certificate::C3,
    libsemigroups::certificate::C4,
    libsemigroups::certificate::free_product_monogenic_free,
    libsemigroups::certificate::knuth_bendix_terminates,
    libsemigroups::certificate::monogenic,
    libsemigroups::certificate::none,
    libsemigroups::certificate::unknown);

CATCH_REGISTER_ENUM(libsemigroups::reduction,
                    libsemigroups::reduction::normalize_alphabet,
                    libsemigroups::reduction::weakly_compress,
                    libsemigroups::reduction::strongly_compress,
                    libsemigroups::reduction::tietze,
                    libsemigroups::reduction::reduce_to_2_generators,
                    libsemigroups::reduction::none);

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

    //   void make_human_readable(Presentation<std::string>& p) {
    //     if (p.alphabet().size() > LETTERS.size()) {
    //       LIBSEMIGROUPS_EXCEPTION(
    //           "too many letters, expected at most %llu, found %llu",
    //           uint64_t(LETTERS.size()),
    //           uint64_t(p.alphabet().size()));
    //     }
    //     std::string new_alphabet;
    //     size_t      next = 2;
    //     for (auto const& x : p.alphabet()) {
    //       if (x == 'a' || x == 'b') {
    //         new_alphabet.push_back(x);
    //       } else {
    //         new_alphabet.push_back(LETTERS[next++]);
    //       }
    //     }
    //     presentation::change_alphabet(p, new_alphabet);
    //   }

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

    template <typename T>
    auto subwords(T first, T last) {
      std::unordered_set<std::string> mp;

      for (auto it = first; it < last; ++it) {
        auto const& w = *it;
        for (auto suffix = w.cbegin(); suffix < w.cend(); ++suffix) {
          for (auto prefix = suffix + 1; prefix < w.cend(); ++prefix) {
            mp.emplace(suffix, prefix);
          }
        }
      }
      return mp;
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
      // TODO sort sbwrds from longest to shortest
      // TODO move iterator
      // std::vector<std::string> vec_sbwrds(sbwrds.cbegin(), sbwrds.cend());

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

    template <typename W>
    auto has_decidable_word_problem(std::ofstream&            log_file,
                                    Presentation<W>&          p,
                                    size_t                    depth,
                                    size_t                    kb_max_depth,
                                    std::chrono::milliseconds kb_run_for) {
      if (p.rules.size() != 2) {
        LIBSEMIGROUPS_EXCEPTION("the presentation must have 1 relation!");
      }

      auto const& u = p.rules[0];
      auto const& v = p.rules[1];

      if (p.alphabet().size() == 1) {
        log_file << "[monogenic] " << p << std::endl;
        return std::make_pair(certificate::monogenic, depth);
      } else if (u.empty() || v.empty()) {
        log_file << "[special] " << p << std::endl;
        return std::make_pair(certificate::special, depth);
      } else if (u.size() == v.size()) {
        log_file << "[relation words have equal length] " << p << std::endl;
        return std::make_pair(certificate::relation_words_have_equal_length,
                              depth);
      } else if (u.front() == v.back() && v.front() == u.back()
                 && u.front() != u.back()) {
        log_file << "[cycle-free] " << p << std::endl;
        return std::make_pair(certificate::cycle_free, depth);
      }

      for (auto it = p.alphabet().cbegin(); it != p.alphabet().cend(); ++it) {
        if (std::search(u.cbegin(), u.cend(), it, it + 1) == u.cend()
            && std::search(v.cbegin(), v.cend(), it, it + 1) == v.cend()) {
          log_file << "[free product] " << p << std::endl;
          return std::make_pair(certificate::free_product_monogenic_free,
                                depth);
        }
      }

      if ((u.size() > v.size() && presentation::is_self_overlap_free(u))
          || (v.size() > u.size() && presentation::is_self_overlap_free(v))) {
        log_file << "[self-overlap free] " << p << std::endl;
        return std::make_pair(certificate::self_overlap_free, depth);
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
      //       log_file << "[reduced to 2-generators] " << p << " (original) ->
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
      //       log_file << "[reduced to 2-generators] " << p << " (original) ->
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
        //   log_file << "[reduced to 2-generators] " << p << " (original) -> "
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
      //     log_file << "[reduced to 2-generators] " << p << " (original) -> "
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

    auto bitmap_init_XXX(size_t N) {
      bitmap_image bmp(N, N);
      bmp.clear();
      bmp.set_all_channels(255, 255, 255);
      return bmp;
    }

    const rgb_t colors[38]
        = {{255, 0, 255},   {0, 117, 220},  {153, 63, 0},    {76, 0, 92},
           {57, 255, 20},   {0, 92, 49},    {43, 206, 72},   {128, 128, 128},
           {148, 255, 181}, {143, 124, 0},  {157, 204, 0},   {194, 0, 136},
           {0, 51, 128},    {255, 164, 5},  {255, 168, 187}, {66, 102, 0},
           {255, 0, 16},    {94, 241, 242}, {0, 153, 143},   {224, 255, 102},
           {116, 10, 255},  {153, 0, 0},    {255, 255, 128}, {255, 255, 0},
           {255, 80, 5},    {255, 000, 000}};

    fmt::rgb to_fmt_color(rgb_t const& x) {
      return fmt::rgb(x.red, x.green, x.blue);
    }

    rgb_t to_color(certificate c) {
      return colors[static_cast<size_t>(c)];
    }

    auto
    bitmap_color_XXX(bitmap_image& bmp, size_t x, size_t y, certificate c) {
      bmp.set_pixel(x, y, to_color(c));
    }

    void print_key() {
      auto const& map          = certificate_map();
      size_t      max_text_len = 0;
      for (auto const& x : map) {
        if (x.second.size() > max_text_len) {
          max_text_len = x.second.size();
        }
      }

      auto pad = [&max_text_len](std::string str) {
        return str + std::string(max_text_len - str.size(), ' ');
      };

      for (auto const& x : map) {
        auto cert = static_cast<size_t>(x.first);
        auto colo = to_fmt_color(colors[cert]);
        fmt::print(fmt::emphasis::bold | fmt::bg(colo), pad(x.second));
        fmt::print(fmt::bg(fmt::color::black), "\n");
      }
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
                          "[extreme][presentation]") {
    auto                      rg = ReportGuard(false);
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
            == std::make_pair(certificate::knuth_bendix_terminates, size_t(0)));
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
                          "weakly compressible",
                          "[quick][presentation]") {
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "aba", "a");
    // This is strongly compressible but doesn't use that
    REQUIRE(presentation::is_strongly_compressible(p));
    REQUIRE(presentation::is_weakly_compressible(p));
    REQUIRE(has_decidable_word_problem(p)
            == std::make_pair(certificate::knuth_bendix_terminates, size_t(0)));
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "010",
                          "knuth_bendix_terminates",
                          "[quick][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "bbbbb", "aaabaa");
    REQUIRE(has_decidable_word_problem(p)
            == std::make_pair(certificate::knuth_bendix_terminates, size_t(0)));
  }

  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "011",
                          "knuth_bendix_terminates",
                          "[quick][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "ba", "aaa");
    REQUIRE(has_decidable_word_problem(p)
            == std::make_pair(certificate::knuth_bendix_terminates, size_t(1)));
  }

  // Takes 1m33s
  LIBSEMIGROUPS_TEST_CASE("1-relation",
                          "012",
                          "sporadic bad 40",
                          "[extreme][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "ba", "aabaaaa");
    REQUIRE(has_decidable_word_problem(p, 3)
            == std::make_pair(certificate::knuth_bendix_terminates, size_t(3)));
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
                          "[extreme][presentation]") {
    auto                      rg = ReportGuard(false);
    Presentation<std::string> p;
    p.alphabet("ab");
    presentation::add_rule_and_check(p, "babaa", "abaaba");
    auto c = has_decidable_word_problem(p);
    REQUIRE(c.first == certificate::knuth_bendix_terminates);
    REQUIRE(c.second == 2);
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
    REQUIRE(c.first == certificate::knuth_bendix_terminates);
    REQUIRE(c.second == 1);
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
                          "solve for bua = ava where |u|, |v| < 5",
                          "[extreme][presentation]") {
    // knuth_bendix max_depth = 2, and run KnuthBendix for 5ms
    auto  rg = ReportGuard(false);
    Sislo s;
    s.alphabet("ab").first("").last("aaaaa");
    auto bmp = bitmap_init_XXX(std::distance(s.cbegin(), s.cend()));
    // REQUIRE(bmp.width() == 0);
    Presentation<std::string> p;
    p.alphabet("ab");
    size_t   x           = 0;
    uint64_t undecidable = 0;
    for (auto u = s.cbegin(); u != s.cend(); ++u) {
      size_t y = 0;
      auto   U = std::string("b") + *u + "a";
      // TODO V = "a"
      for (auto v = s.cbegin(); v != s.cend(); ++v) {
        auto V = std::string("a") + *v + "a";
        p.rules.clear();
        presentation::add_rule(p, U, V);
        auto c = has_decidable_word_problem(p);
        bitmap_color_XXX(bmp, x, y, c.first);
        std::cout << U << " = " << V << " is ";
        if (c.first == certificate::unknown) {
          ++undecidable;
          std::cout << "bad" << std::endl;
        } else {
          std::cout << "good (depth " << c.second << ")" << std::endl;
        }
        ++y;
      }
      ++x;
    }
    print_key();
    bmp.save_image("2_gen_1_rel.bmp");
    REQUIRE(undecidable == 35);
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
   //           2-generators"}, {reduction::knuth_bendix, "Knuth-Bendix active
   //           rules"}, {reduction::none, "none"}};
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
