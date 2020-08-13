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

#include "bench-main.hpp"  // for LIBSEMIGROUPS_BENCHMARK
#include "catch.hpp"       // for REQUIRE, REQUIRE_NOTHROW, REQUIRE_THROWS_AS

#include "libsemigroups/element.hpp" // for BooleanMat

#include "examples/generators.hpp"

namespace libsemigroups {


  TEST_CASE("const_panilo_iterator", "[quick][000]") {
    using node_type = size_t;
    auto   ad       = test_digraph();
    size_t N        = 20;

    BENCHMARK("const_panilo_iterator") {
      std::vector<std::pair<word_type, node_type>> v(ad.cbegin_panilo(0, 0, N),
                                                     ad.cend_panilo());
      REQUIRE(v.size() == 1048575);
    };

    BENCHMARK("free function for comparison with const_panilo_iterator") {
      std::pair<std::vector<word_type>, std::vector<node_type>> v
          = paths_in_lex_order(ad, 0, 0, N);
      REQUIRE(v.first.size() == 1048575);
    };
  }

  LIBSEMIGROUPS_BENCHMARK("cbegin/end_rules",
                          "[FroidurePin][002]",
                          before_bench_rules<Transf>,
                          bench_const_rule_iterator<Transf>,
                          after_bench<Transf>,
                          {transf_examples(0x9806816B9D761476)});

  LIBSEMIGROUPS_BENCHMARK("relations",
                          "[FroidurePin][003]",
                          before_bench_rules<Transf>,
                          bench_relations<Transf>,
                          after_bench<Transf>,
                          {transf_examples(0x9806816B9D761476)});

}  // namespace libsemigroups
