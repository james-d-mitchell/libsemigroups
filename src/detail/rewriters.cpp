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

#include "libsemigroups/detail/rewriters.hpp"

#include <algorithm>
#include <atomic>
#include <chrono>

#include "libsemigroups/runner.hpp"  // for Ticker

#include "libsemigroups/detail/guard.hpp"   // for Guard
#include "libsemigroups/detail/report.hpp"  // for report_default

namespace libsemigroups {
  namespace detail {}  // namespace detail
}  // namespace libsemigroups
