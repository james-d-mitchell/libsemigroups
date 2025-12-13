//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2023-2025 Joseph Edwards + James D. Mitchell
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

// This file contains the implementation of the AhoCorasickImpl class.
#include "libsemigroups/detail/aho-corasick-impl.hpp"

#include <algorithm>    // for max, copy, reverse
#include <array>        // for array
#include <string>       // for basic_string, string, to_string
#include <string_view>  // for basic_string_view, string_view

#include "libsemigroups/constants.hpp"   // for Undefined, UNDEFINED, operator==
#include "libsemigroups/debug.hpp"       // for LIBSEMIGROUPS_ASSERT
#include "libsemigroups/detail/fmt.hpp"  // for format
#include "libsemigroups/dot.hpp"         // for Dot, Dot::Edge, Dot::Node
#include "libsemigroups/exception.hpp"   // for LIBSEMIGROUPS_EXCEPTION
#include "libsemigroups/types.hpp"       // for word_type, letter_type

// TODO rm this file
namespace libsemigroups {
  namespace detail {}  // namespace detail
}  // namespace libsemigroups
