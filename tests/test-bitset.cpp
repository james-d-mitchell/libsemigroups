//
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

#include "catch.hpp"                 // for REQUIRE
#include "libsemigroups/bitset.hpp"  // for BitSet
#include "test-main.hpp"             // for LIBSEMIGROUPS_TEST_CASE

namespace libsemigroups {
  LIBSEMIGROUPS_TEST_CASE("BitSet", "000", "size", "[bitset][quick]") {
    BitSet<10> bs;
    REQUIRE(bs.size() == 10);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "001", "operator<", "[bitset][quick]") {
    BitSet<10> bs1;
    bs1.reset();
    BitSet<10> bs2;
    bs2.reset();
    bs2.set(0);

    REQUIRE(bs1 < bs2);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "002", "operator==", "[bitset][quick]") {
    BitSet<10> bs1;
    bs1.reset();
    BitSet<10> bs2;
    bs2.reset();
    bs2.set(0);

    REQUIRE(!(bs1 == bs2));
    bs1.set(0);
    REQUIRE(bs1 == bs2);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "003", "operator!=", "[bitset][quick]") {
    BitSet<10> bs1;
    bs1.reset();
    BitSet<10> bs2;
    bs2.reset();
    bs2.set(0);

    REQUIRE(bs1 != bs2);
    bs1.set(0);
    REQUIRE(bs1 == bs2);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "004", "operator&=", "[bitset][quick]") {
    BitSet<10> bs1;
    bs1.reset();
    bs1.set(0);
    bs1.set(1);
    BitSet<10> bs2;
    bs2.reset();
    bs2.set(1);
    bs1 &= bs2;
    REQUIRE(bs1 == bs2);
    REQUIRE(bs1.count() == 1);
    REQUIRE(bs2.count() == 1);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "005", "&", "[bitset][quick]") {
    BitSet<10> bs1;
    bs1.reset();
    bs1.set(0);
    bs1.set(1);
    BitSet<10> bs2;
    bs2.reset();
    bs2.set(1);
    BitSet<10> bs3 = bs1 & bs2;
    REQUIRE(bs3 == bs2);
    REQUIRE(&bs3 != &bs2);
    REQUIRE(bs1.count() == 2);
    REQUIRE(bs2.count() == 1);
    REQUIRE(bs3.count() == 1);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "006", "operator|=", "[bitset][quick]") {
    BitSet<10> bs1;
    bs1.reset();
    bs1.set(0);
    BitSet<10> bs2;
    bs2.reset();
    bs2.set(1);
    bs2 |= bs1;
    REQUIRE(bs1 != bs2);
    REQUIRE(bs2.count() == 2);
    REQUIRE(bs1.count() == 1);
    REQUIRE(bs2.test(0));
    REQUIRE(bs2.test(1));
    REQUIRE(!bs2.test(2));
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "007", "operator[]", "[bitset][quick]") {
    BitSet<10> bs;
    bs.reset();
    bs.set(0);
    bs.set(3);
    bs.set(5);
    REQUIRE(bs[0]);
    REQUIRE(!bs[1]);
    REQUIRE(!bs[2]);
    REQUIRE(bs[3]);
    REQUIRE(!bs[4]);
    REQUIRE(bs[5]);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "008", "set(none)", "[bitset][quick]") {
    BitSet<10> bs;
    bs.set();
    REQUIRE(bs[0]);
    REQUIRE(bs[1]);
    REQUIRE(bs[2]);
    REQUIRE(bs[3]);
    REQUIRE(bs[4]);
    REQUIRE(bs[5]);
    REQUIRE(bs.to_int() == 1023);
    REQUIRE(bs.count() == 10);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet",
                          "009",
                          "set(pos, value)",
                          "[bitset][quick]") {
    BitSet<10> bs;
    bs.set();
    bs.set(0, false);
    REQUIRE(!bs[0]);
    REQUIRE(bs[1]);
    REQUIRE(bs[2]);
    REQUIRE(bs[3]);
    REQUIRE(bs[4]);
    REQUIRE(bs[5]);
    REQUIRE(bs.count() == 9);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet",
                          "010",
                          "set(first, last, value)",
                          "[bitset][quick]") {
    BitSet<10> bs;
    bs.reset();
    REQUIRE(bs.count() == 0);
    bs.set(2, 6, true);
    REQUIRE(bs.count() == 4);
    REQUIRE(!bs[0]);
    REQUIRE(!bs[1]);
    REQUIRE(bs[2]);
    REQUIRE(bs[3]);
    REQUIRE(bs[4]);
    REQUIRE(bs[5]);
    REQUIRE(!bs[6]);
    REQUIRE(!bs[7]);
  }
  LIBSEMIGROUPS_TEST_CASE("BitSet",
                          "011",
                          "reset(first, last)",
                          "[bitset][quick]") {
    BitSet<10> bs;
    bs.set();
    REQUIRE(bs.count() == 10);
    bs.reset(2, 6);

    REQUIRE(bs.count() == 6);
    REQUIRE(bs[0]);
    REQUIRE(bs[1]);
    REQUIRE(!bs[2]);
    REQUIRE(!bs[3]);
    REQUIRE(!bs[4]);
    REQUIRE(bs[6]);
    REQUIRE(bs[7]);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "012", "reset(pos)", "[bitset][quick]") {
    BitSet<10> bs;
    bs.set();
    REQUIRE(bs.count() == 10);
    bs.reset(2);
    bs.reset(3);
    bs.reset(4);
    bs.reset(5);

    REQUIRE(bs.count() == 6);
    REQUIRE(bs[0]);
    REQUIRE(bs[1]);
    REQUIRE(!bs[2]);
    REQUIRE(!bs[3]);
    REQUIRE(!bs[4]);
    REQUIRE(bs[6]);
    REQUIRE(bs[7]);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet",
                          "013",
                          "apply (iterate through set bits)",
                          "[bitset][quick]") {
    BitSet<10> bs;
    bs.set();
    bs.reset(2);
    bs.reset(3);
    bs.reset(4);
    bs.reset(5);

    std::vector<size_t> expected = {0, 1, 6, 7, 8, 9};
    std::vector<size_t> result;

    // hi bits are not nec. set to false
    bs.apply([&result](size_t i) { result.push_back(i); });

    REQUIRE(bs.count() == 6);
    // hi bits are set to false
    result.clear();
    bs.apply([&result](size_t i) { result.push_back(i); });
    REQUIRE(result == expected);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "014", "std::hash", "[bitset][quick]") {
    BitSet<10> bs;
    REQUIRE(std::hash<BitSet<10>>()(bs) != 0);
  }

  LIBSEMIGROUPS_TEST_CASE("BitSet", "015", "constructors", "[bitset][quick]") {
    BitSet<10> bs;
    bs.set();
    bs.reset(2, 6);
    REQUIRE(bs.count() == 6);
    REQUIRE(bs[0]);
    REQUIRE(bs[1]);
    REQUIRE(!bs[2]);
    REQUIRE(!bs[3]);
    REQUIRE(!bs[4]);
    REQUIRE(bs[6]);
    REQUIRE(bs[7]);

    {  // Copy constructor
      auto copy(bs);
      REQUIRE(copy == bs);
      REQUIRE(&copy != &bs);
    }
    REQUIRE(bs.count() == 6);
    REQUIRE(bs[0]);
    REQUIRE(bs[1]);
    REQUIRE(!bs[2]);
    REQUIRE(!bs[3]);
    REQUIRE(!bs[4]);
    REQUIRE(bs[6]);
    REQUIRE(bs[7]);
    {  // Move constructor
      auto copy(std::move(bs));
      REQUIRE(copy.count() == 6);
      REQUIRE(copy[0]);
      REQUIRE(copy[1]);
      REQUIRE(!copy[2]);
      REQUIRE(!copy[3]);
      REQUIRE(!copy[4]);
      REQUIRE(copy[6]);
      REQUIRE(copy[7]);
    }
    bs.set();
    bs.reset(2, 6);
    {  // Copy assignment
      auto copy = bs;
      REQUIRE(copy.count() == 6);
      REQUIRE(copy[0]);
      REQUIRE(copy[1]);
      REQUIRE(!copy[2]);
      REQUIRE(!copy[3]);
      REQUIRE(!copy[4]);
      REQUIRE(copy[6]);
      REQUIRE(copy[7]);
    }
    REQUIRE(bs.count() == 6);
    REQUIRE(bs[0]);
    REQUIRE(bs[1]);
    REQUIRE(!bs[2]);
    REQUIRE(!bs[3]);
    REQUIRE(!bs[4]);
    REQUIRE(bs[6]);
    REQUIRE(bs[7]);
    {  // Move assignment
      auto copy = std::move(bs);
      REQUIRE(copy.count() == 6);
      REQUIRE(copy[0]);
      REQUIRE(copy[1]);
      REQUIRE(!copy[2]);
      REQUIRE(!copy[3]);
      REQUIRE(!copy[4]);
      REQUIRE(copy[6]);
      REQUIRE(copy[7]);
    }
  }
}  // namespace libsemigroups
