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

// This file contains an implementation of Stephen's procedure for finitely
// presented semigroups and monoids.

#include "libsemigroups/stephen.hpp"

#include <chrono>                                  // for duration, duration...
#include <tuple>                                   // for tie, tuple
#include <utility>                                 // for move, pair
                                                   //
#include "libsemigroups/constants.hpp"             // for operator==, Undefined
#include "libsemigroups/debug.hpp"                 // for LIBSEMIGROUPS_ASSERT
#include "libsemigroups/digraph-helper.hpp"        // for last_node_on_path_nc
#include "libsemigroups/exception.hpp"             // for LibsemigroupsExcep...
#include "libsemigroups/present.hpp"               // for Presentation<>::wo...
#include "libsemigroups/report.hpp"                // for REPORT_DEFAULT_V3
#include "libsemigroups/string.hpp"                // for group_digits
#include "libsemigroups/todd-coxeter-digraph.hpp"  // for ToddCoxeterDigraph...
#include "libsemigroups/types.hpp"                 // for word_type

namespace libsemigroups {}  // namespace libsemigroups
