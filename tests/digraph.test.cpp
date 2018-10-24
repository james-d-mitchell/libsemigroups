//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2018 Finn Smith
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

#include <stddef.h>  // for size_t
#include <vector>    // for vector

#include "catch.hpp"                // for REQUIRE, REQUIRE_THROWS_AS, REQUI...
#include "digraph.hpp"              // for ActionDigraph
#include "forest.hpp"               // for Forest
#include "libsemigroups.tests.hpp"  // for LIBSEMIGROUPS_TEST_CASE

namespace libsemigroups {

  struct LibsemigroupsException;
  ActionDigraph<size_t> cycle(size_t n) {
    ActionDigraph<size_t> g(n);
    for (size_t i = 0; i < n - 1; ++i) {
      g.add_edge(i, i + 1, 0);
    }
    g.add_edge(n - 1, 0, 0);
    return g;
  }

  void cycle(ActionDigraph<size_t>& digraph, size_t n) {
    size_t old_nodes = digraph.nr_nodes();
    digraph.add_nodes(n);
    for (size_t i = old_nodes; i < digraph.nr_nodes() - 1; ++i) {
      digraph.add_edge(i, i + 1, 0);
    }
    digraph.add_edge(digraph.nr_nodes() - 1, old_nodes, 0);
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "001",
                          "constructor with 1  default arg",
                          "[quick][digraph]") {
    ActionDigraph<size_t> g;
    REQUIRE(g.nr_nodes() == 0);
    REQUIRE(g.nr_edges() == 0);
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "002",
                          "constructor with 0 default args",
                          "[quick][digraph]") {
    for (size_t j = 0; j < 100; ++j) {
      ActionDigraph<size_t> g(j);
      REQUIRE(g.nr_nodes() == j);
      REQUIRE(g.nr_edges() == 0);
    }
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "003",
                          "add nodes",
                          "[quick][digraph]") {
    ActionDigraph<size_t> g(3);
    REQUIRE(g.nr_nodes() == 3);
    REQUIRE(g.nr_edges() == 0);

    for (size_t i = 1; i < 100; ++i) {
      g.add_nodes(i);
      REQUIRE(g.nr_nodes() == 3 + i * (i + 1) / 2);
    }
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "004",
                          "add edges",
                          "[quick][digraph]") {
    ActionDigraph<size_t> g(17);

    for (size_t i = 0; i < 17; ++i) {
      for (size_t j = 0; j < 31; ++j) {
        g.add_edge(i, (7 * i + 23 * j) % 17, j);
      }
    }

    REQUIRE(g.nr_edges() == 31 * 17);
    REQUIRE(g.nr_nodes() == 17);

    for (size_t i = 0; i < 17; ++i) {
      for (size_t j = 0; j < 31; ++j) {
        REQUIRE(g.get(i, j) == (7 * i + 23 * j) % 17);
      }
    }

    for (size_t i = 0; i < 17; ++i) {
      for (size_t j = 0; j < 10; ++j) {
        g.add_edge(i, (7 * i + 23 * j) % 17, 31 + j);
      }
    }

    REQUIRE(g.nr_edges() == 41 * 17);
    REQUIRE(g.nr_nodes() == 17);
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "005",
                          "strongly connected components - cycles",
                          "[quick][digraph]") {
    auto g = cycle(32);
    REQUIRE(g.scc_id(0) == 0);
    g = cycle(33);
    REQUIRE(std::vector<std::vector<size_t>>(g.cbegin_sccs(), g.cend_sccs())
            == std::vector<std::vector<size_t>>(
                   {{32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22,
                     21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11,
                     10, 9,  8,  7,  6,  5,  4,  3,  2,  1,  0}}));
    for (size_t i = 0; i < 33; ++i) {
      REQUIRE(g.scc_id(i) == 0);
    }
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "006",
                          "Strongly connected components - no edges",
                          "[quick][digraph]") {
    ActionDigraph<size_t> graph = ActionDigraph<size_t>(0);
    for (size_t j = 1; j < 100; ++j) {
      graph.add_nodes(j);

      for (size_t i = 0; i < j * (j + 1) / 2; ++i) {
        REQUIRE(graph.scc_id(i) == i);
      }
    }
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "007",
                          "strongly connected components - disjoint cycles",
                          "[quick][digraph]") {
    for (size_t j = 2; j < 50; ++j) {
      ActionDigraph<size_t> graph;

      for (size_t k = 0; k < 10; ++k) {
        graph.add_nodes(j);
        for (size_t i = k * j; i < (k + 1) * j - 1; ++i) {
          graph.add_edge(i, i + 1, 0);
        }
        graph.add_edge((k + 1) * j - 1, k * j, 0);
      }
      for (size_t i = 0; i < 10 * j; ++i) {
        REQUIRE(graph.scc_id(i) == i / j);
      }
    }
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "008",
                          "Strongly connected components - complete graphs",
                          "[quick][digraph]") {
    for (size_t k = 2; k < 50; ++k) {
      ActionDigraph<size_t> graph(k);

      for (size_t i = 0; i < k; ++i) {
        for (size_t j = 0; j < k; ++j) {
          // might as well leave the loops in
          graph.add_edge(i, j, j);
        }
      }
      for (size_t i = 0; i < k; ++i) {
        REQUIRE(graph.scc_id(i) == 0);
      }
    }
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "009",
                          "exceptions",
                          "[quick][digraph]") {
    ActionDigraph<size_t> graph(10);
    REQUIRE_THROWS_AS(graph.get(10, 0), LibsemigroupsException);
    REQUIRE_THROWS_AS(graph.get(0, 1), LibsemigroupsException);

    REQUIRE_THROWS_AS(graph.add_edge(0, 10, 0), LibsemigroupsException);
    REQUIRE_THROWS_AS(graph.add_edge(10, 0, 0), LibsemigroupsException);
    for (size_t i = 0; i < 5; ++i) {
      graph.add_edge(0, 1, i);
      graph.add_edge(2, 2, i);
    }
    REQUIRE_NOTHROW(graph.add_edge(0, 1, 0));
    REQUIRE_NOTHROW(graph.add_edge(2, 2, 0));

    REQUIRE_THROWS_AS(graph.scc_id(10), LibsemigroupsException);
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "010",
                          "Spanning forest - complete graphs",
                          "[quick][digraph]") {
    for (size_t k = 2; k < 50; ++k) {
      ActionDigraph<size_t> graph(k);

      for (size_t i = 0; i < k; ++i) {
        for (size_t j = 0; j < k; ++j) {
          // might as well leave the loops in
          graph.add_edge(i, j, j);
        }
      }
      REQUIRE(graph.nr_scc() == 1);

      Forest forest = graph.spanning_forest();

      REQUIRE(forest.parent(k - 1) == UNDEFINED);
    }
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "011",
                          "Spanning forest - disjoint cycles",
                          "[quick][digraph]") {
    size_t                j = 33;
    ActionDigraph<size_t> graph;

    for (size_t k = 0; k < 10; ++k) {
      graph.add_nodes(j);
      for (size_t i = k * j; i < (k + 1) * j - 1; ++i) {
        graph.add_edge(i, i + 1, 0);
      }
      graph.add_edge((k + 1) * j - 1, k * j, 0);
    }
    for (size_t i = 0; i < 10 * j; ++i) {
      REQUIRE(graph.scc_id(i) == i / j);
    }
    Forest forest = graph.spanning_forest();

    REQUIRE(
        std::vector<size_t>(forest.cbegin_parent(), forest.cend_parent())
        == std::vector<size_t>(
               {32,  0,   1,   2,   3,   4,   5,   6,   7,   8,   9,
                10,  11,  12,  13,  14,  15,  16,  17,  18,  19,  20,
                21,  22,  23,  24,  25,  26,  27,  28,  29,  30,  UNDEFINED,
                65,  33,  34,  35,  36,  37,  38,  39,  40,  41,  42,
                43,  44,  45,  46,  47,  48,  49,  50,  51,  52,  53,
                54,  55,  56,  57,  58,  59,  60,  61,  62,  63,  UNDEFINED,
                98,  66,  67,  68,  69,  70,  71,  72,  73,  74,  75,
                76,  77,  78,  79,  80,  81,  82,  83,  84,  85,  86,
                87,  88,  89,  90,  91,  92,  93,  94,  95,  96,  UNDEFINED,
                131, 99,  100, 101, 102, 103, 104, 105, 106, 107, 108,
                109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
                120, 121, 122, 123, 124, 125, 126, 127, 128, 129, UNDEFINED,
                164, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141,
                142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152,
                153, 154, 155, 156, 157, 158, 159, 160, 161, 162, UNDEFINED,
                197, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174,
                175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185,
                186, 187, 188, 189, 190, 191, 192, 193, 194, 195, UNDEFINED,
                230, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207,
                208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218,
                219, 220, 221, 222, 223, 224, 225, 226, 227, 228, UNDEFINED,
                263, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240,
                241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251,
                252, 253, 254, 255, 256, 257, 258, 259, 260, 261, UNDEFINED,
                296, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273,
                274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284,
                285, 286, 287, 288, 289, 290, 291, 292, 293, 294, UNDEFINED,
                329, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306,
                307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317,
                318, 319, 320, 321, 322, 323, 324, 325, 326, 327, UNDEFINED}));
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "012",
                          "scc root paths - complete graphs",
                          "[quick][digraph]") {
    for (size_t k = 2; k < 50; ++k) {
      ActionDigraph<size_t> graph(k);

      for (size_t i = 0; i < k; ++i) {
        for (size_t j = 0; j < k; ++j) {
          graph.add_edge(i, j, j);
        }
      }

      for (size_t i = 0; i < k; ++i) {
        size_t pos = i;
        for (auto it = graph.cbegin_path_to_root(i); it < graph.cend_path_to_root(i); ++it) {
          pos = graph.get(pos, *it);
        }
        REQUIRE(pos == graph.cbegin_sccs()[graph.scc_id(i)][0]);
      }
    }
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "013",
                          "scc root paths - disjoint cycles",
                          "[quick][digraph]") {
    for (size_t j = 2; j < 35; ++j) {
      ActionDigraph<size_t> graph;

      for (size_t k = 0; k < 6; ++k) {
        graph.add_nodes(j);
        for (size_t i = k * j; i < (k + 1) * j - 1; ++i) {
          graph.add_edge(i, i + 1, 0);
        }
        graph.add_edge((k + 1) * j - 1, k * j, 0);
      }

      for (size_t i = 0; i < graph.nr_nodes(); ++i) {
        size_t pos = i;
        for (auto it = graph.cbegin_path_to_root(i);
             it < graph.cend_path_to_root(i);
             ++it) {
          pos = graph.get(pos, *it);
        }
        REQUIRE(pos == graph.cbegin_sccs()[graph.scc_id(i)][0]);
      }
    }
  }

  LIBSEMIGROUPS_TEST_CASE("ActionDigraph",
                          "014",
                          "scc large cycle",
                          "[quick][digraph]") {
    ActionDigraph<size_t> graph = cycle(100000);
    using node_type             = decltype(graph)::node_type;

    REQUIRE(std::all_of(
        graph.cbegin(), graph.cend(), [&graph](node_type i) -> bool {
          return graph.scc_id(i) == 0;
        }));
    cycle(graph, 10101);
    REQUIRE(std::all_of(
        graph.cbegin(), graph.cend() - 10101, [&graph](node_type i) -> bool {
          return graph.scc_id(i) == 0;
        }));
    REQUIRE(std::all_of(
        graph.cbegin() + 100000, graph.cend(), [&graph](node_type i) -> bool {
          return graph.scc_id(i) == 1;
        }));
  }
}  // namespace libsemigroups
