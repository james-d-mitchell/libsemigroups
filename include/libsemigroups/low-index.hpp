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

// This file contains a declaration of a class for performing the "low-index
// congruence" algorithm for semigroups and monoid.

#ifndef LIBSEMIGROUPS_LOW_INDEX_HPP_
#define LIBSEMIGROUPS_LOW_INDEX_HPP_

namespace libsemigroups {
  // IDEA:
  // * have an object that can take a presentation (like CongruenceInterface or
  // FpSemigroupInterface);
  // * the object has cbegin(size_t n), cend(size_t n) mem fns that allow
  // iteration through the congruences with at most n classes;
  // * these will use some of the code from ToddCoxeter (mostly
  // push_definition, and process_deductions (these parts of ToddCoxeter should
  // then be refactored out into a separate base class for ToddCoxeter +
  // LowIndexCongruences);
  // * they perform a DFS trying to fill in the "graph" such that it is
  // compatible with the relations. We backtrack when two paths labelled by
  // relation words lead to different places. Dereferencing the iterator just
  // points to the reference for the "graph", and incrementing continues the
  // search for the next "graph"
  class LowIndexCongruences {};
}  // namespace libsemigroups

#endif  // LIBSEMIGROUPS_LOW_INDEX_HPP_
