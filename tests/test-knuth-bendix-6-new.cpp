// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2020 James D. Mitchell
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

// This file is the sixth of six that contains tests for the KnuthBendix
// classes. In a mostly vain attempt to speed up compilation the tests are
// split across 6 files as follows:
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
// 6: contains tests for KnuthBendix.

#include "catch.hpp"      // for REQUIRE, REQUIRE_NOTHROW, REQUIRE_THROWS_AS
#include "test-main.hpp"  // for LIBSEMIGROUPS_TEST_CASE

#include "libsemigroups/fpsemi-examples.hpp"   // for chinese_monoid
#include "libsemigroups/knuth-bendix-new.hpp"  // for KnuthBendix, operator<<
#include "libsemigroups/report.hpp"            // for ReportGuard
#include "libsemigroups/to-froidure-pin.hpp"
#include "libsemigroups/types.hpp"  // for word_type

namespace libsemigroups {
  using literals::operator""_w;

  struct LibsemigroupsException;

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "103",
                          "Presentation<word_type>",
                          "[quick][knuth-bendix]") {
    auto rg = ReportGuard(false);

    Presentation<word_type> p;
    p.alphabet(2);
    presentation::add_rule(p, 000_w, 0_w);
    presentation::add_rule(p, 0_w, 11_w);

    KnuthBendix kb(p);

    REQUIRE(!kb.finished());
    REQUIRE(kb.size() == 5);
    REQUIRE(kb.finished());

    REQUIRE(kb.normal_form(to_string(kb.presentation(), 001_w)) == "aab");
    REQUIRE(kb.normal_form(to_string(kb.presentation(), 00001_w)) == "aab");
    REQUIRE(kb.normal_form(to_string(kb.presentation(), 011001_w)) == "aab");
    REQUIRE(!kb.equal_to(to_string(kb.presentation(), 000_w),
                         to_string(kb.presentation(), 1_w)));
    REQUIRE(!kb.equal_to(to_string(kb.presentation(), 0000_w),
                         to_string(kb.presentation(), 000_w)));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "104",
                          "free semigroup congruence (6 classes)",
                          "[quick][knuth-bendix]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(5);
    presentation::add_rule(p, 00_w, 0_w);
    presentation::add_rule(p, 01_w, 1_w);
    presentation::add_rule(p, 10_w, 1_w);
    presentation::add_rule(p, 02_w, 2_w);
    presentation::add_rule(p, 20_w, 2_w);
    presentation::add_rule(p, 03_w, 3_w);
    presentation::add_rule(p, 30_w, 3_w);
    presentation::add_rule(p, 04_w, 4_w);
    presentation::add_rule(p, 40_w, 4_w);
    presentation::add_rule(p, 12_w, 0_w);
    presentation::add_rule(p, 21_w, 0_w);
    presentation::add_rule(p, 34_w, 0_w);
    presentation::add_rule(p, 43_w, 0_w);
    presentation::add_rule(p, 22_w, 0_w);
    presentation::add_rule(p, 14233_w, 0_w);
    presentation::add_rule(p, 444_w, 0_w);

    KnuthBendix kb(p);

    REQUIRE(kb.size() == 6);
    REQUIRE(kb.equal_to(to_string(kb.presentation(), 1_w),
                        to_string(kb.presentation(), 2_w)));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "105",
                          "free semigroup congruence (16 classes)",
                          "[quick][knuth-bendix]") {
    auto rg = ReportGuard(false);

    Presentation<word_type> p;
    p.alphabet(4);
    presentation::add_rule(p, {3}, {2});
    presentation::add_rule(p, {0, 3}, {0, 2});
    presentation::add_rule(p, {1, 1}, {1});
    presentation::add_rule(p, {1, 3}, {1, 2});
    presentation::add_rule(p, {2, 1}, {2});
    presentation::add_rule(p, {2, 2}, {2});
    presentation::add_rule(p, {2, 3}, {2});
    presentation::add_rule(p, {0, 0, 0}, {0});
    presentation::add_rule(p, {0, 0, 1}, {1});
    presentation::add_rule(p, {0, 0, 2}, {2});
    presentation::add_rule(p, {0, 1, 2}, {1, 2});
    presentation::add_rule(p, {1, 0, 0}, {1});
    presentation::add_rule(p, {1, 0, 2}, {0, 2});
    presentation::add_rule(p, {2, 0, 0}, {2});
    presentation::add_rule(p, {0, 1, 0, 1}, {1, 0, 1});
    presentation::add_rule(p, {0, 2, 0, 2}, {2, 0, 2});
    presentation::add_rule(p, {1, 0, 1, 0}, {1, 0, 1});
    presentation::add_rule(p, {1, 2, 0, 1}, {1, 0, 1});
    presentation::add_rule(p, {1, 2, 0, 2}, {2, 0, 2});
    presentation::add_rule(p, {2, 0, 1, 0}, {2, 0, 1});
    presentation::add_rule(p, {2, 0, 2, 0}, {2, 0, 2});

    KnuthBendix kb(p);
    REQUIRE(kb.size() == 16);
    REQUIRE(kb.number_of_active_rules() == 18);
    REQUIRE(kb.equal_to(to_string(kb.presentation(), 2_w),
                        to_string(kb.presentation(), 3_w)));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "106",
                          "free semigroup congruence (6 classes)",
                          "[quick][knuth-bendix]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(11);
    p.rules
        = {{2},          {1},          {4},          {3},          {5},
           {0},          {6},          {3},          {7},          {1},
           {8},          {3},          {9},          {3},          {10},
           {0},          {0, 2},       {0, 1},       {0, 4},       {0, 3},
           {0, 5},       {0, 0},       {0, 6},       {0, 3},       {0, 7},
           {0, 1},       {0, 8},       {0, 3},       {0, 9},       {0, 3},
           {0, 10},      {0, 0},       {1, 1},       {1},          {1, 2},
           {1},          {1, 4},       {1, 3},       {1, 5},       {1, 0},
           {1, 6},       {1, 3},       {1, 7},       {1},          {1, 8},
           {1, 3},       {1, 9},       {1, 3},       {1, 10},      {1, 0},
           {3, 1},       {3},          {3, 2},       {3},          {3, 3},
           {3},          {3, 4},       {3},          {3, 5},       {3, 0},
           {3, 6},       {3},          {3, 7},       {3},          {3, 8},
           {3},          {3, 9},       {3},          {3, 10},      {3, 0},
           {0, 0, 0},    {0},          {0, 0, 1},    {1},          {0, 0, 3},
           {3},          {0, 1, 3},    {1, 3},       {1, 0, 0},    {1},
           {1, 0, 3},    {0, 3},       {3, 0, 0},    {3},          {0, 1, 0, 1},
           {1, 0, 1},    {0, 3, 0, 3}, {3, 0, 3},    {1, 0, 1, 0}, {1, 0, 1},
           {1, 3, 0, 1}, {1, 0, 1},    {1, 3, 0, 3}, {3, 0, 3},    {3, 0, 1, 0},
           {3, 0, 1},    {3, 0, 3, 0}, {3, 0, 3}};

    KnuthBendix kb(p);
    REQUIRE(kb.size() == 16);
    REQUIRE(kb.equal_to(to_string(kb.presentation(), {0}),
                        to_string(kb.presentation(), {5})));
    REQUIRE(kb.equal_to(to_string(kb.presentation(), {0}),
                        to_string(kb.presentation(), {5})));
    REQUIRE(kb.equal_to(to_string(kb.presentation(), {0}),
                        to_string(kb.presentation(), {10})));
    REQUIRE(kb.equal_to(to_string(kb.presentation(), {1}),
                        to_string(kb.presentation(), {2})));
    REQUIRE(kb.equal_to(to_string(kb.presentation(), {1}),
                        to_string(kb.presentation(), {7})));
    REQUIRE(kb.equal_to(to_string(kb.presentation(), {3}),
                        to_string(kb.presentation(), {4})));
    REQUIRE(kb.equal_to(to_string(kb.presentation(), {3}),
                        to_string(kb.presentation(), {6})));
    REQUIRE(kb.equal_to(to_string(kb.presentation(), {3}),
                        to_string(kb.presentation(), {8})));
    REQUIRE(kb.equal_to(to_string(kb.presentation(), {3}),
                        to_string(kb.presentation(), {9})));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "107",
                          "free semigroup congruence (240 classes)",
                          "[no-valgrind][quick][knuth-bendix]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(2);
    presentation::add_rule(p, 000_w, 0_w);
    presentation::add_rule(p, 1111_w, 1_w);
    presentation::add_rule(p, 01110_w, 00_w);
    presentation::add_rule(p, 1001_w, 11_w);
    presentation::add_rule(p, 001010101010_w, 00_w);

    KnuthBendix kb(p);
    REQUIRE(kb.size() == 240);
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "108",
                          "free semigroup congruence (240 classes)",
                          "[no-valgrind][quick][knuth-bendix]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(2);
    presentation::add_rule(p, 000_w, 0_w);
    presentation::add_rule(p, 1111_w, 1_w);
    presentation::add_rule(p, 01110_w, 00_w);
    presentation::add_rule(p, 1001_w, 11_w);
    presentation::add_rule(p, 001010101010_w, 00_w);

    KnuthBendix kb(p);
    REQUIRE_NOTHROW(to_froidure_pin(kb));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "111",
                          "constructors",
                          "[quick][knuth-bendix][no-valgrind]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(2);
    presentation::add_rule(p, 000_w, 0_w);
    presentation::add_rule(p, 111111111_w, 1_w);
    presentation::add_rule(p, 011111011_w, 110_w);

    KnuthBendix kb(p);
    REQUIRE(kb.size() == 746);

    auto copy(kb);
    REQUIRE(copy.size() == 746);
    REQUIRE(copy.presentation().alphabet().size() == 2);
    // the copy uses the "active rules" of kb, of which there are 105 since
    // knuth-bendix has already been run.
    REQUIRE(copy.number_of_active_rules() == 105);
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "115",
                          "to_froidure_pin",
                          "[quick][knuth-bendix]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(2);
    presentation::add_rule(p, 000_w, 0_w);
    presentation::add_rule(p, 1111_w, 1_w);
    presentation::add_rule(p, 011111011_w, 110_w);

    KnuthBendix kb(p);
    REQUIRE(to_froidure_pin(kb).size() == 12);
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "117",
                          "number of classes when obv-inf",
                          "[quick][knuth-bendix]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p;
    p.alphabet(3);
    presentation::add_rule(p, 01_w, 10_w);
    presentation::add_rule(p, 02_w, 20_w);
    presentation::add_rule(p, 00_w, 0_w);
    presentation::add_rule(p, 02_w, 0_w);
    presentation::add_rule(p, 20_w, 0_w);
    presentation::add_rule(p, 11_w, 11_w);
    presentation::add_rule(p, 12_w, 21_w);
    presentation::add_rule(p, 111_w, 1_w);
    presentation::add_rule(p, 12_w, 1_w);
    presentation::add_rule(p, 21_w, 1_w);
    presentation::add_rule(p, 0_w, 1_w);

    KnuthBendix kb(p);
    REQUIRE(is_obviously_infinite(kb));
    REQUIRE(kb.size() == POSITIVE_INFINITY);
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "020",
                          "Chinese monoid",
                          "[quick][knuth-bendix]") {
    auto                    rg = ReportGuard(false);
    Presentation<word_type> p  = fpsemigroup::chinese_monoid(3);

    KnuthBendix kb(p);
    REQUIRE(is_obviously_infinite(kb));
    REQUIRE(kb.size() == POSITIVE_INFINITY);
    REQUIRE(kb.presentation().rules.size() / 2 == 8);
    auto nf = knuth_bendix::normal_forms(kb).min(1).max(10);
    REQUIRE(nf.count() == 1'175);
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "083",
                          "partial_transformation_monoid(4)",
                          "[standard][knuth-bendix]") {
    auto rg = ReportGuard(false);

    size_t n = 4;
    auto   p = partial_transformation_monoid(n, fpsemigroup::author::Sutov);

    KnuthBendix kb(p);
    REQUIRE(!is_obviously_infinite(kb));
    REQUIRE(kb.size() == 625);
  }

  // Takes about 1 minute
  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "118",
                          "partial_transformation_monoid5",
                          "[extreme][knuth-bendix]") {
    auto rg = ReportGuard(true);

    size_t n = 5;
    auto   p = partial_transformation_monoid(n, fpsemigroup::author::Sutov);

    KnuthBendix kb(p);
    REQUIRE(!is_obviously_infinite(kb));
    REQUIRE(kb.size() == 7'776);
  }

  // Takes about 5 seconds
  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "119",
                          "full_transformation_monoid Iwahori",
                          "[extreme][knuth-bendix]") {
    auto rg = ReportGuard(true);

    size_t      n = 5;
    auto        p = full_transformation_monoid(n, fpsemigroup::author::Iwahori);
    KnuthBendix kb(p);
    REQUIRE(!is_obviously_infinite(kb));
    REQUIRE(kb.size() == 3'125);
  }
}  // namespace libsemigroups