//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2021-2022 James D. Mitchell + Maria Tsalakou
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

#define CATCH_CONFIG_ENABLE_TUPLE_STRINGMAKER

#include <cstddef>   // for size_t
#include <iostream>  // for to_string
#include <string>    // for to_string
#include <unordered_set>

#include "bench-main.hpp"  // for CATCH_CONFIG_ENABLE_BENCHMARKING
#include "catch.hpp"       // for TEST_CASE, BENCHMARK, REQUIRE

#include "libsemigroups/kambites.hpp"      // for Kambites
#include "libsemigroups/knuth-bendix.hpp"  // for KnuthBendix
#include "libsemigroups/siso.hpp"          // for cbegin_sislo

namespace libsemigroups {
  using detail::MultiStringView;
  using detail::power_string;
  using detail::random_string;
  using detail::random_strings;
  using fpsemigroup::Kambites;

  namespace {
    std::string zip(std::vector<std::string> const& x,
                    std::vector<std::string> const& y) {
      LIBSEMIGROUPS_ASSERT(x.size() == y.size());
      std::string result = "";
      for (size_t i = 0; i < x.size(); ++i) {
        result += x[i];
        result += y[i];
      }
      return result;
    }

    // Returns {u_1, u_2, ..., u_{exp}} where u_i are chosen with uniform
    // distribution in {s, t}
    std::vector<std::string> random_sequence(std::string const& s,
                                             std::string const& t,
                                             size_t             exp) {
      static std::random_device              rd;
      static std::mt19937                    generator(rd());
      static std::uniform_int_distribution<> distribution(0, 1);
      std::vector<std::string>               result;
      while (exp > 0) {
        switch (distribution(generator)) {
          case 0: {
            result.push_back(s);
            break;
          }
          case 1: {
            result.push_back(t);
            break;
          }
        }
        exp--;
      }
      return result;
    }

    template <typename S, typename T>
    void xml_tag(S name, T val) {
      std::cout << "<" << name << " value=\"" << val << "\"></" << name
                << ">\n";
    }
  }  // namespace

  ////////////////////////////////////////////////////////////////////////
  // Benchmark checking C(4) or higher - Example A.1
  ////////////////////////////////////////////////////////////////////////

  // <a, b | abab^2 ... >

  std::pair<std::string, std::string> example1(size_t N) {
    std::string lhs, rhs;
    for (size_t b = 1; b <= N; ++b) {
      lhs += "a" + std::string(b, 'b');
    }
    for (size_t b = N + 1; b <= 2 * N; ++b) {
      rhs += "a" + std::string(b, 'b');
    }
    return std::make_pair(lhs, rhs);
  }

  template <typename T, typename F>
  void c4_ex_A1(F&& foo) {
    for (size_t N = 100; N <= 1000; N += 25) {
      size_t const M = N * (2 * N + 3);
      BENCHMARK_ADVANCED(std::to_string(M))
      (Catch::Benchmark::Chronometer meter) {
        std::string lhs, rhs;
        std::tie(lhs, rhs) = example1(N);
        T k;
        k.set_alphabet("ab");
        meter.measure([&]() {
          k.add_rule(lhs, rhs);
          return foo(k);
        });
      };  // NOLINT(readability/braces)
    }
  }

  TEST_CASE("Example A.1 - C(4)-check - std::string", "[quick][000]", ) {
    xml_tag(
        "Title",
        "C(4)-check for $\\langle a, b \\mid abab^2\\cdots ab^n = ab^{n + 1} "
        "ab^{n+2} \\cdots ab^{2n}\\rangle$");
    xml_tag("XLabel", "Sums of lengths of relation words");
    xml_tag("Label", "std::string");
    c4_ex_A1<Kambites<std::string>>(
        [](auto& k) { return k.small_overlap_class(); });
  }

  TEST_CASE("Example A.1 - C(4)-check - MultiStringView", "[quick][001]", ) {
    xml_tag("Label", "libsemigroups::MultiStringView");
    c4_ex_A1<Kambites<MultiStringView>>(
        [](auto& k) { return k.small_overlap_class(); });
  }

  TEST_CASE("Example A.1 - KnuthBendix", "[quick][002]", ) {
    auto rg = ReportGuard(false);
    xml_tag("Label", "Knuth-Bendix");
    c4_ex_A1<fpsemigroup::KnuthBendix>([](auto& kb) {
      kb.run();
      return kb.confluent();
    });
  }

  ////////////////////////////////////////////////////////////////////////
  // Benchmark checking C(4) or higher - Example A.2
  ////////////////////////////////////////////////////////////////////////

  // <a, b, c | a(bc) ^ k a = a (cb) ^ l a>

  template <typename T, typename F>
  void c4_ex_A2(F&& foo) {
    for (size_t m = 5000; m < 500000; m += 20000) {
      BENCHMARK_ADVANCED(std::to_string(4 * m + 4))
      (Catch::Benchmark::Chronometer meter) {
        std::string lhs = "a" + power_string("bc", m) + "a";
        std::string rhs = "a" + power_string("cb", m) + "a";
        T           k;  // We leave the construction of k outside the metered
                        // section so that we don't measure the time taken to
                        // free the memory allocated for k.
        k.set_alphabet("abc");
        meter.measure([&]() {
          k.add_rule(lhs, rhs);
          foo(k);
        });
      };  // NOLINT(readability/braces)
    }
  }

  TEST_CASE("Example A.2 - C(4)-check - std::string", "[quick][003]", ) {
    xml_tag(
        "Title",
        "C(4)-check for $\\langle a, b, c \\mid a(bc)^ka = a (cb)^la\\rangle$");
    xml_tag("XLabel", "Sums of lengths of relation words");
    xml_tag("Label", "std::string");
    c4_ex_A2<Kambites<std::string>>(
        [](auto& k) { return k.small_overlap_class(); });
  }

  TEST_CASE("Example A.2 - C(4)-check - MultiStringView", "[quick][004]", ) {
    xml_tag("Label", "libsemigroups::MultiStringView");
    c4_ex_A2<Kambites<MultiStringView>>(
        [](auto& k) { return k.small_overlap_class(); });
  }

  ////////////////////////////////////////////////////////////////////////
  // Benchmark wp-prefix - Example A.1
  ////////////////////////////////////////////////////////////////////////

  template <typename T>
  void equal_to_ex_A1(size_t m) {
    for (size_t N = 100; N <= 400; N += 8) {
      std::string lhs, rhs;
      std::tie(lhs, rhs) = example1(m);
      Kambites<T> k;
      k.set_alphabet("ab");
      k.add_rule(lhs, rhs);
      auto random = random_strings("ab", N, 0, 4 * N + 4);
      auto u      = zip(random_sequence(lhs, rhs, N), random);
      auto v      = zip(random_sequence(lhs, rhs, N), random);
      REQUIRE(k.small_overlap_class() >= 4);
      BENCHMARK(std::to_string(u.size() + v.size())) {
        k.equal_to(u, v);
      };
    }
  }

  TEST_CASE("Example A.1 - n = 10 - equal_to - MultiStringView",
            "[A1][equal_to][n=10]") {
    size_t const n = 10;
    xml_tag("Title",
            "WpPrefix for $\\langle a, b \\mid ab^1ab^2\\cdots ab^n = "
            "ab^{n + 1} ab^{n+2} \\cdots ab^{2n}\\rangle$");
    xml_tag("XLabel", "The sum of the lengths of the 2 words compared");
    xml_tag("Label", std::string("$n = ") + std::to_string(n) + "$");
    equal_to_ex_A1<MultiStringView>(n);
  }

  namespace {
    template <typename T>
    auto count_2_gen_1_rel(size_t len) {
      Sislo lhs;
      lhs.alphabet("ab");
      lhs.first(len);
      lhs.last(len + 1);

      Sislo rhs;
      rhs.alphabet("ab");
      rhs.first(1);
      rhs.last(len);

      uint64_t total_c4     = 0;
      uint64_t total        = 0;
      uint64_t total_length = 0;

      auto last = lhs.cbegin();
      std::advance(last, std::distance(lhs.cbegin(), lhs.cend()) - 1);

      auto lhs_end = lhs.cend();
      auto rhs_end = rhs.cend();

      Kambites<T> k;
      k.set_alphabet("ab");

      for (auto l = lhs.cbegin(); l != lhs_end; ++l) {
        for (auto r = rhs.cbegin(); r != rhs_end; ++r) {
          total++;
          total_length += l->size() + r->size();
          k.clear();
          k.add_rule_nc(*l, *r);
          if (k.small_overlap_class() >= 4) {
            total_c4++;
          }
        }
        if (l != last) {
          for (auto r = l + 1; r != lhs_end; ++r) {
            total_length += l->size() + r->size();
            total++;
            k.clear();
            k.add_rule_nc(*l, *r);
            if (k.small_overlap_class() >= 4) {
              total_c4++;
            }
          }
        }
      }
      return std::make_tuple(total_c4, total, total_length);
    }
  }  // namespace

  TEST_CASE("C(4)-check for all 2-generated 1-relation monoids (max. word "
            "length = 4..12)",
            "[038]") {
    std::array<std::tuple<uint64_t, uint64_t, uint64_t>, 14> const expected
        = {std::make_tuple(0, 0, 0),
           {0, 1, 0},
           {0, 14, 0},
           {0, 76, 392},
           {0, 344, 2'400},
           {0, 1'456, 12'896},
           {0, 5'984, 64'512},
           {2, 24'256, 308'864},
           {26, 97'664, 1'436'160},
           {760, 391'936, 6'540'800},
           {17'382, 1'570'304, 29'331'456},
           {217'458, 6'286'336, 129'959'936},
           {1'994'874, 25'155'584, 570'286'080},
           {14'633'098, 100'642'816, 2'482'724'864}};

    // xml_tag("Title", "C(4)-check for all 2-generated 1-relation monoids");
    xml_tag("XLabel", "Maximum length of a relation word");
    xml_tag("YLabel", "Mean time in microseconds");
    std::vector<uint64_t> results;
    for (size_t n = 4; n < 13; ++n) {
      std::tuple<uint64_t, uint64_t, uint64_t> x;
      BENCHMARK(std::to_string(n)) {
        x = count_2_gen_1_rel<MultiStringView>(n);
      };
      results.push_back(std::get<1>(x));
      REQUIRE(x == expected[n]);
    }
    xml_tag("Data", detail::to_string(results));
  }

  namespace {
    template <typename T>
    auto count_2_gen_1_rel(std::vector<std::string> const& sample) {
      uint64_t total_c4     = 0;
      uint64_t total        = 0;
      uint64_t total_length = 0;

      Kambites<T> k;
      k.set_alphabet("ab");

      for (auto l = sample.cbegin(); l != sample.cend(); l += 2) {
        for (auto r = l + 1; r != sample.cend() - 1; r += 2) {
          total_length += l->size() + r->size();
          total++;
          k.clear();
          k.add_rule_nc(*l, *r);
          if (k.small_overlap_class() >= 4) {
            total_c4++;
          }
        }
      }
      return std::make_tuple(total_c4, total, total_length);
    }
  }  // namespace

  TEST_CASE("C(4)-check for random 2-generated 1-relation monoids "
            "(max. word length 10,12..100 )",
            "[039]") {
    xml_tag("Title", "C(4)-check for random 2-generated 1-relation monoids");
    xml_tag("XLabel", "Maximum length of a relation word");
    xml_tag("YLabel", "Mean time in nanoseconds");

    size_t const          sample_size = 1'000;
    std::vector<uint64_t> results;

    for (size_t n = 10; n < 100; n += 2) {
      std::vector<std::string> sample;
      for (size_t i = 0; i < sample_size; ++i) {
        sample.push_back(random_string("ab", n));
        sample.push_back(random_string("ab", 1, n));
      }

      std::tuple<uint64_t, uint64_t, uint64_t> x;
      BENCHMARK(std::to_string(n)) {
        x = count_2_gen_1_rel<MultiStringView>(sample);
      };
      results.push_back(std::get<1>(x));
    }
    xml_tag("Data", detail::to_string(results));
  }

  // This test case is only to compute an approx. of the ratio of C4 to total
  // 2-generator 1-relation monoids
  TEST_CASE("C(4)-check for random 2-generated 1-relation monoids"
            "(max. word length 10..50)",
            "[041]") {
    size_t const          sample_size = 1'000;
    std::vector<uint64_t> results;

    for (size_t n = 10; n < 50; n += 1) {
      std::vector<std::string> sample;
      for (size_t i = 0; i < sample_size; ++i) {
        sample.push_back(random_string("ab", n));
        sample.push_back(random_string("ab", 1, n));
      }

      std::tuple<uint64_t, uint64_t, uint64_t> x
          = count_2_gen_1_rel<MultiStringView>(sample);
      std::cout << "\n\n ratio = "
                << static_cast<long double>(std::get<0>(x)) / std::get<1>(x);
      results.push_back(std::get<1>(x));
    }
  }

  TEST_CASE("C(4)-check for random 2-generated 1-relation monoids "
            "(max. word length 1000,3000..100000)",
            "[040]") {
    xml_tag("Title", "C(4)-check for random 2-generated 1-relation monoids");
    xml_tag("XLabel", "Maximum length of a relation word");
    xml_tag("YLabel", "Mean time in nanoseconds");

    size_t const          sample_size = 100;
    std::vector<uint64_t> results;

    for (size_t n = 1000; n < 100000; n += 2000) {
      std::vector<std::string> sample;
      for (size_t i = 0; i < 2 * sample_size; ++i) {
        sample.push_back(random_string("ab", n));
      }

      std::tuple<uint64_t, uint64_t, uint64_t> x;
      BENCHMARK(std::to_string(n)) {
        x = count_2_gen_1_rel<MultiStringView>(sample);
      };
      results.push_back(std::get<1>(x));
    }
    xml_tag("Data", detail::to_string(results));
  }
}  // namespace libsemigroups
