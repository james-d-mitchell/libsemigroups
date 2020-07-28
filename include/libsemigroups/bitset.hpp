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

// TODO(now):
// 1) tests
// 3) make this intrinsic proof
//
// TODO(later)
// 1) doc

#ifndef LIBSEMIGROUPS_BITSET_HPP_
#define LIBSEMIGROUPS_BITSET_HPP_

#include <climits>  // for CHAR_BIT
#include <cstddef>  // for size_t
#include <utility>  // for hash

#include "libsemigroups-debug.hpp"  // for LIBSEMIGROUPS_ASSERT

namespace libsemigroups {

  // T = type of integers
  template <size_t N>
  class BitSet {
    static_assert(N <= 64, "BitSet does not support more than 64 entries");

   public:
    using block_type = typename std::conditional<
        N <= 8,
        uint_fast8_t,
        typename std::conditional<
            N <= 16,
            uint_fast16_t,
            typename std::conditional<N <= 32, uint_fast32_t, uint64_t>::type>::
            type>::type;

    BitSet() noexcept              = default;
    BitSet(BitSet const&) noexcept = default;
    BitSet(BitSet&&) noexcept      = default;
    BitSet& operator=(BitSet const&) noexcept = default;
    BitSet& operator=(BitSet&&) noexcept = default;
    ~BitSet()                            = default;

    constexpr size_t size() const noexcept {
      return N;
    }

    bool operator<(BitSet const& that) const noexcept {
      clear_hi_bits();
      that.clear_hi_bits();
      return _block < that._block;
    }

    bool operator==(BitSet const& that) const noexcept {
      clear_hi_bits();
      that.clear_hi_bits();
      return _block == that._block;
    }

    bool operator!=(BitSet const& that) const noexcept {
      return !(*this == that);
    }

    void operator&=(BitSet const& that) const noexcept {
      _block &= that._block;
    }

    BitSet<N> operator&(BitSet const& that) const noexcept {
      return BitSet(_block & that._block);
    }

    void operator|=(BitSet const& that) const noexcept {
      _block |= that._block;
    }

    bool test(size_t const pos) const noexcept {
      LIBSEMIGROUPS_ASSERT(pos < N);
      return _block & mask(pos);
    }

    bool operator[](size_t const pos) const noexcept {
      return test(pos);
    }

    BitSet& set() noexcept {
      _block = ~0;
      return *this;
    }

    BitSet& set(size_t const pos, bool const value = true) noexcept {
      LIBSEMIGROUPS_ASSERT(pos < N);
      if (value) {
        _block |= mask(pos);
      } else {
        _block &= ~mask(pos);
      }
      return *this;
    }

    BitSet& set(size_t const first,
                size_t const last,
                bool const   value) noexcept {
      LIBSEMIGROUPS_ASSERT(first < N);
      LIBSEMIGROUPS_ASSERT(last <= N);
      LIBSEMIGROUPS_ASSERT(first < last);
      block_type m = ~0;
      m            = (m >> first);
      m            = (m << (first + (block_count() - last)));
      m            = (m >> (block_count() - last));
      if (value) {
        _block |= m;
      } else {
        _block &= ~m;
      }
      return *this;
    }

    BitSet& reset() noexcept {
      _block = 0;
      return *this;
    }

    BitSet& reset(size_t const pos) noexcept {
      LIBSEMIGROUPS_ASSERT(pos < N);
      _block &= ~mask(pos);
      return *this;
    }

    BitSet& reset(size_t const first, size_t const last) {
      LIBSEMIGROUPS_ASSERT(first < N);
      LIBSEMIGROUPS_ASSERT(last <= N);
      LIBSEMIGROUPS_ASSERT(first < last);
      return set(first, last, false);
    }

    size_t count() const noexcept {
      clear_hi_bits();
      return __builtin_popcountl(_block);
    }

    template <typename S>
    void apply(S&& func) const {
      block_type block = _block;
      while (block != 0) {
        block_type t = block & -block;
        size_t     i = static_cast<size_t>(__builtin_ctzll(block));
        if (i >= size()) {
          break;
        }
        func(i);
        block ^= t;
      }
    }

    block_type to_int() const noexcept {
      clear_hi_bits();
      return _block;
    }

   private:
    explicit BitSet<N>(block_type const block) : _block(block) {}

    void clear_hi_bits() const noexcept {
      size_t s = block_count() - N;
      _block   = _block << s;
      _block   = _block >> s;
    }

    constexpr size_t block_count() const noexcept {
      return sizeof(block_type) * CHAR_BIT;
    }

    constexpr block_type mask(size_t const i) const noexcept {
      // LIBSEMIGROUPS_ASSERT(i < size());
      return static_cast<block_type>(MASK[i]);
    }

    static constexpr uint64_t MASK[64] = {0x1,
                                          0x2,
                                          0x4,
                                          0x8,
                                          0x10,
                                          0x20,
                                          0x40,
                                          0x80,
                                          0x100,
                                          0x200,
                                          0x400,
                                          0x800,
                                          0x1000,
                                          0x2000,
                                          0x4000,
                                          0x8000,
                                          0x10000,
                                          0x20000,
                                          0x40000,
                                          0x80000,
                                          0x100000,
                                          0x200000,
                                          0x400000,
                                          0x800000,
                                          0x1000000,
                                          0x2000000,
                                          0x4000000,
                                          0x8000000,
                                          0x10000000,
                                          0x20000000,
                                          0x40000000,
                                          0x80000000,
                                          0x100000000,
                                          0x200000000,
                                          0x400000000,
                                          0x800000000,
                                          0x1000000000,
                                          0x2000000000,
                                          0x4000000000,
                                          0x8000000000,
                                          0x10000000000,
                                          0x20000000000,
                                          0x40000000000,
                                          0x80000000000,
                                          0x100000000000,
                                          0x200000000000,
                                          0x400000000000,
                                          0x800000000000,
                                          0x1000000000000,
                                          0x2000000000000,
                                          0x4000000000000,
                                          0x8000000000000,
                                          0x10000000000000,
                                          0x20000000000000,
                                          0x40000000000000,
                                          0x80000000000000,
                                          0x100000000000000,
                                          0x200000000000000,
                                          0x400000000000000,
                                          0x800000000000000,
                                          0x1000000000000000,
                                          0x2000000000000000,
                                          0x4000000000000000,
                                          0x8000000000000000};
    mutable block_type        _block;
  };

  template <size_t N>
  constexpr uint64_t BitSet<N>::MASK[64];

}  // namespace libsemigroups

namespace std {
  // TODO noexcept
  template <size_t N>
  struct hash<libsemigroups::BitSet<N>> {
    size_t operator()(libsemigroups::BitSet<N> const& bs) const {
      using block_type = typename libsemigroups::BitSet<N>::block_type;
      return hash<block_type>()(bs.to_int());
    }
  };
}  // namespace std
#endif  // LIBSEMIGROUPS_BITSET_HPP_
