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

// This file contains the implementation of a trie with suffix links for use by
// the Aho-Corasick dictionary search algorithm

#ifndef LIBSEMIGROUPS_DETAIL_AHO_CORASICK_IMPL_HPP_
#define LIBSEMIGROUPS_DETAIL_AHO_CORASICK_IMPL_HPP_

#include <cstddef>        // for size_t
#include <memory>         // for allocator_traits<>::value_type
#include <set>            // for set
#include <stack>          // for stack
#include <string>         // for string
#include <unordered_set>  // for unordered_set
#include <vector>         // for vector

#include "libsemigroups/aho-corasick.hpp"
#include "libsemigroups/constants.hpp"  // for Undefined, operator!=, UNDEFINED, operator==
#include "libsemigroups/debug.hpp"      // for LIBSEMIGROUPS_ASSERT
#include "libsemigroups/exception.hpp"  // for LIBSEMIGROUPS_EXCEPTION
#include "libsemigroups/ranges.hpp"     // for rx::iterator_range
#include "libsemigroups/types.hpp"      // for letter_type, word_type

#include "containers.hpp"  // DynamicArray2
#include "print.hpp"       // for to_printable

// TODO(2) is it worthwhile storing a pointer to the terminal nodes beneath
// each node? If this can be updated quickly, it would save a lot of time in
// overlap/confluence checking. One compromise is to have a pointer to the rules
// any given node is contained within. This could be updated easily when adding
// new rules, but more care would be needed when removing rules.
// TODO(2) add something that gets a ranges element to find all terminal nodes.
// TODO(2) change all_nodes[i] to node_no_checks(i);

namespace libsemigroups {
  namespace detail {

    // TODO remove once AhoCorasickImpl<Value> as a template class
    // forward decl
    class Rule;

    // An AhoCorasickImpl<Value> object represents a hash map like container
    // (implemented using a trie), where the keys in the map must be
    // words consisting of letters in the range {0, ..., n - 1} for some n.
    template <typename Value>
    class AhoCorasickImpl {
     public:
      using index_type = uint32_t;
      using terminal_node_const_iterator
          = std::unordered_set<index_type>::const_iterator;

      static constexpr const index_type root = 0;

      // This struct represents a match of the "key" [first, last) in the trie,
      // which has value "value"
      template <typename Iterator>
      class Match {
       public:
        Iterator first;
        Iterator last;

       private:
        // TODO should be std::optional<Value const&>
        std::optional<Value> const* value_ptr;

       public:
        Match(Iterator frst, Iterator lst, std::optional<Value> const& val)
            : first(frst), last(lst), value_ptr(&val) {}

        Match& operator=(Match&& that) {
          first     = std::move(that.first);
          last      = std::move(that.last);
          value_ptr = that.value_ptr;
          return *this;
        }

        // TODO to tpp
        [[nodiscard]] bool operator==(Match const& that) const {
          if (first == last) {
            // Indicates no match, and we don't care about value in that case
            // TODO What if the empty string is a match?
            return that.first == that.last;
          }
          return first == that.first && last == that.last
                 && value() == that.value();
        }

        [[nodiscard]] std::optional<Value> const& value() const noexcept {
          // LIBSEMIGROUPS_ASSERT(value_ptr->has_value());
          // TODO return Value
          return *value_ptr;
        }

        [[nodiscard]] operator bool() {
          return first != last;
        }
      };

     private:
      class Node {
        friend class AhoCorasickImpl;
        ////////////////////////////////////////////////////////////////////////
        // Private data
        ////////////////////////////////////////////////////////////////////////
       private:
        uint32_t                       _height;
        index_type                     _link;
        index_type                     _parent;
        letter_type                    _parent_letter;
        std::unordered_set<index_type> _suffix_link_sources;

        Node& init() noexcept {
          return init(UNDEFINED, UNDEFINED);
        }

        Node& init(index_type parent, letter_type a) noexcept;

       public:
        std::optional<Value> value;

        ////////////////////////////////////////////////////////////////////////
        // Constructors/initializers - public
        ////////////////////////////////////////////////////////////////////////

        Node() : Node(UNDEFINED, UNDEFINED) {}
        Node(index_type parent, letter_type a);

        Node(Node const&)            = default;
        Node& operator=(Node const&) = default;
        Node(Node&&)                 = default;
        Node& operator=(Node&&)      = default;

        ~Node() = default;

        ////////////////////////////////////////////////////////////////////////
        // Getters - public
        ////////////////////////////////////////////////////////////////////////

        [[nodiscard]] size_t height() const noexcept {
          return _height;
        }

        [[nodiscard]] index_type suffix_link() const noexcept {
          return _link;
        }

        std::unordered_set<index_type>& suffix_link_sources() noexcept {
          return _suffix_link_sources;
        }

        [[nodiscard]] bool terminal() const noexcept {
          return value.has_value();
        }

        [[nodiscard]] index_type parent() const noexcept {
          return _parent;
        }

        [[nodiscard]] letter_type parent_letter() const noexcept {
          return _parent_letter;
        }

       private:
        ////////////////////////////////////////////////////////////////////////
        // Setters - private
        ////////////////////////////////////////////////////////////////////////

        // All setters are private to avoid corrupting the objects.

        Node const& height(size_t val) noexcept {
          _height = val;
          return *this;
        }

        Node const& suffix_link(index_type val) noexcept {
          _link = val;
          return *this;
        }

      };  // class Node

      // TODO(1) if we store pointers here instead of Nodes, then inside the
      // Nodes themselves we could store pointers to the parents etc, rather
      // than indices, which would mean we could set the _link and other info in
      // the Node::init() function, also will remove the index <-> Node
      // conversions everywhere.
      std::vector<Node>                 _all_nodes;
      detail::DynamicArray2<index_type> _children;
      std::unordered_set<index_type>    _active_nodes_index;
      std::vector<index_type>           _inactive_nodes_index;
      std::vector<index_type>           _node_indices_to_update;
      std::unordered_set<index_type>    _terminal_nodes_index;

      // TODO(1): it seems likely that the positions of the active nodes in
      // _all_nodes will become scattered and disordered over time, and so it'd
      // probably be best to periodically (or maybe always?) compress, and sort
      // the nodes.

     public:
      ////////////////////////////////////////////////////////////////////////
      // Constructors + initializers
      ////////////////////////////////////////////////////////////////////////

      AhoCorasickImpl();
      AhoCorasickImpl& init();

      explicit AhoCorasickImpl(size_t num_letters);
      AhoCorasickImpl& init(size_t num_letters);

      AhoCorasickImpl(AhoCorasickImpl const&);
      AhoCorasickImpl& operator=(AhoCorasickImpl const&);
      AhoCorasickImpl(AhoCorasickImpl&&);
      AhoCorasickImpl& operator=(AhoCorasickImpl&&);

      ~AhoCorasickImpl();

      size_t alphabet_size() const noexcept {
        return _children.number_of_cols();
      }

      AhoCorasickImpl& increase_alphabet_size_by(size_t val);

      // TODO private?
      [[nodiscard]] size_t height_no_checks(index_type i) const;

      // TODO private?
      [[nodiscard]] Node const& node_no_checks(index_type i) const {
        LIBSEMIGROUPS_ASSERT(i < _all_nodes.size());
        return _all_nodes[i];
      }

      ////////////////////////////////////////////////////////////////////////
      // New API - somewhat similar mem fns to std::unordered_map
      ////////////////////////////////////////////////////////////////////////

      // TODO return type should be maybe a bool to indicate if insertion
      // actually happened, i.e. somewhat the same as std::unordered_map
      template <typename Iterator, typename... Args>
      index_type emplace_no_checks(Iterator first,
                                   Iterator last,
                                   Args&&... args);

      template <typename Word>
      index_type insert_no_checks(Word const& key, Value const& value) {
        return emplace_no_checks(key.begin(), key.end(), value);
      }

      template <typename Word>
      index_type insert_no_checks(Word const& key, Value&& value) {
        return emplace_no_checks(key.begin(), key.end(), std::move(value));
      }

      // TODO return type should be maybe a bool to indicate if insertion
      // actually happened, i.e. somewhat the same as std::unordered_map
      template <typename Iterator, typename... Args>
      index_type emplace(Iterator first, Iterator last, Args&&... args);

      template <typename Word>
      index_type insert(Word const& key, Value const& value) {
        return emplace(key.begin(), key.end(), value);
      }

      template <typename Word>
      index_type insert(Word const& key, Value&& value) {
        return emplace(key.begin(), key.end(), value);
      }

      template <typename Iterator>
      index_type erase_no_checks(Iterator first, Iterator last);

      template <typename Word>
      index_type erase_no_checks(Word const& key) {
        return erase_no_checks(key.begin(), key.end());
      }

      template <typename Iterator>
      index_type erase(Iterator first, Iterator last);

      template <typename Word>
      index_type erase(Word const& key) {
        return erase(key.begin(), key.end());
      }

      template <typename Iterator>
      [[nodiscard]] std::optional<Value> const& at(Iterator first,
                                                   Iterator last) const {
        index_type current = root;
        for (auto it = first; it != last; ++it) {
          throw_if_letter_out_of_range(*it);
          current = _children.get(current, *it);
          if (current == UNDEFINED) {
            // TODO this doesn't really make sense, should throw
            // std::out_of_range
            return node_no_checks(root).value;
          }
        }
        return node_no_checks(current).value;
      }

      template <typename Word>
      [[nodiscard]] std::optional<Value> const& at(Word const& key) const {
        return at(key.begin(), key.end());
      }

      // TODO to tpp
      template <typename Word>
      [[nodiscard]] Value const& operator[](Word const& key) const {
        index_type current = root;
        for (auto it = key.begin(); it != key.end(); ++it) {
          current = _children.get(current, *it);
        }
        return node_no_checks(current).value.value();
      }

      // TODO to tpp
      template <typename Iterator>
      [[nodiscard]] bool contains_no_checks(Iterator first,
                                            Iterator last) const {
        index_type current = root;
        for (auto it = first; it != last; ++it) {
          current = _children.get(current, *it);
          if (current == UNDEFINED) {
            return false;
          }
        }
        return node_no_checks(current).terminal();
      }

      template <typename Word>
      [[nodiscard]] bool contains_no_checks(Word const& key) const {
        return contains_no_checks(key.begin(), key.end());
      }

      template <typename Iterator>
      [[nodiscard]] bool contains(Iterator first, Iterator last) const {
        throw_if_any_letter_out_of_range(first, last);
        return contains_no_checks(first, last);
      }

      template <typename Word>
      [[nodiscard]] bool contains(Word const& key) const {
        return contains(key.begin(), key.end());
      }

      // TODO rename to begin and change return type to {key, val}, or whatever
      // std::unordered_map implements
      [[nodiscard]] terminal_node_const_iterator cbegin_terminal_nodes() const {
        return _terminal_nodes_index.cbegin();
      }

      // TODO rename to end and change return type to {key, val}, or whatever
      // std::unordered_map implements
      [[nodiscard]] terminal_node_const_iterator cend_terminal_nodes() const {
        return _terminal_nodes_index.cend();
      }

      // TODO rename to items and change return type to {key, val}, or whatever
      // std::unordered_map implements
      [[nodiscard]] auto terminal_nodes() const {
        return rx::iterator_range(cbegin_terminal_nodes(),
                                  cend_terminal_nodes());
      }

      [[nodiscard]] bool empty() const noexcept {
        return number_of_nodes() == 1;
      }

      // The following are implemented for std::unordered_map and could be
      // impled here too.
      // TODO find
      // TODO size()
      // TODO clear
      // TODO try_emplace
      // TODO std::swap fn
      // TODO  operator==
      // TODO reserve? not sure how this would work

      ////////////////////////////////////////////////////////////////////////
      // New API - trie specific
      ////////////////////////////////////////////////////////////////////////

      // Returns the longest prefix of [first, last) that belongs to *this.
      // TODO to tpp
      template <typename Iterator>
      [[nodiscard]] Match<Iterator>
      longest_prefix_no_checks(Iterator first, Iterator last) const {
        index_type current = root;
        index_type best    = root;
        auto       best_it = first;
        for (auto it = first; it != last; ++it) {
          current = _children.get(current, *it);
          if (current == UNDEFINED) {
            break;
          } else if (node_no_checks(current).terminal()) {
            best    = current;
            best_it = it + 1;
          }
        }
        return Match(first, best_it, node_no_checks(best).value);
      }

      // Returns the longest prefix of [first, last) that belongs to *this.
      // TODO should return iterator (which I need to implement)
      template <typename Word>
      [[nodiscard]] Match<typename Word::const_iterator>
      longest_prefix_no_checks(Word const& key) const {
        return longest_prefix_no_checks(key.begin(), key.end());
      }

      // TODO to tpp
      template <typename Iterator>
      [[nodiscard]]
      Match<Iterator> longest_prefix(Iterator first, Iterator last) const {
        throw_if_any_letter_out_of_range(first, last);
        return longest_prefix_no_checks(first, last);
      }

      template <typename Word>
      [[nodiscard]] Match<typename Word::const_iterator>
      longest_prefix(Word const& key) const {
        return longest_prefix(key.begin(), key.end());
      }

      // Finds any subword contained in both [first, last) and the keys of the
      // trie.
      template <typename Iterator>
      [[nodiscard]] Match<Iterator> subword_no_checks(Iterator first,
                                                      Iterator last) const {
        index_type current = root;
        for (auto it = first; it < last; ++it) {
          current = traverse_no_checks(current, *it);
          if (current == UNDEFINED) {
            // No match possible, the word goes off the trie before a match is
            // found.
            break;
          } else if (node_no_checks(current).terminal()) {
            // The match is the word labelling the path from the root to
            // current, which corresponds to the return value below
            LIBSEMIGROUPS_ASSERT(static_cast<size_t>(std::distance(first, it))
                                     + 1
                                 >= height_no_checks(current));
            return Match(it - height_no_checks(current) + 1,
                         it + 1,
                         node_no_checks(current).value);
          }
        }
        // No match, the last parameter for Match's constructor isn't then used
        // for anything, but it's required to be a reference so we use the only
        // node we know always exists the "root"
        return Match(first, first, node_no_checks(root).value);
      }

      // Returns the longest prefix of [first, last) that belongs to *this.
      // TODO should return iterator (which I need to implement)
      template <typename Word>
      [[nodiscard]] Match<typename Word::const_iterator>
      subword_no_checks(Word const& key) const {
        return subword_no_checks(key.begin(), key.end());
      }

      // TODO should return iterator (which I need to implement)
      // TODO to tpp
      template <typename Iterator>
      [[nodiscard]]
      Match<Iterator> subword(Iterator first, Iterator last) const {
        throw_if_any_letter_out_of_range(first, last);
        return subword_no_checks(first, last);
      }

      template <typename Word>
      [[nodiscard]] Match<typename Word::const_iterator>
      subword(Word const& key) const {
        return subword(key.begin(), key.end());
      }

      ////////////////////////////////////////////////////////////////////////
      // Old API
      ////////////////////////////////////////////////////////////////////////

      // TODO private
      [[nodiscard]] size_t number_of_nodes() const noexcept {
        LIBSEMIGROUPS_ASSERT(_children.number_of_rows() == _all_nodes.size());
        return _active_nodes_index.size();
      }

      // The following function is critical for KnuthBendix and so we leave it
      // here to be inlined possibly.
      // TODO private?
      [[nodiscard]] index_type traverse_no_checks(index_type  current,
                                                  letter_type a) const {
        LIBSEMIGROUPS_ASSERT(current < _all_nodes.size());
        LIBSEMIGROUPS_ASSERT(_active_nodes_index.count(current) == 1);
        index_type next = _children.get(current, a);
        if (next != UNDEFINED) {
          return next;
        } else if (current == root) {
          return root;
        }
        return traverse_no_checks(suffix_link_no_checks(current), a);
      }

      // TODO private?
      [[nodiscard]] index_type traverse(index_type  current,
                                        letter_type a) const {
        throw_if_node_index_not_active(current);
        return traverse_no_checks(current, a);
      }

      // TODO private?
      [[nodiscard]] size_t height(index_type i) const {
        throw_if_node_index_not_active(i);
        return height_no_checks(i);
      }

      // TODO private?
      [[nodiscard]] bool terminal_no_checks(index_type i) const;

      // TODO private?
      [[nodiscard]] bool terminal(index_type i) const {
        throw_if_node_index_not_active(i);
        return terminal_no_checks(i);
      }

      // TODO private?
      [[nodiscard]] index_type suffix_link_no_checks(index_type i) const {
        LIBSEMIGROUPS_ASSERT(i < _all_nodes.size());
        LIBSEMIGROUPS_ASSERT(_active_nodes_index.count(i) == 1);
        return _all_nodes[i].suffix_link();
      }

      // TODO private?
      [[nodiscard]] index_type suffix_link(index_type current) const {
        throw_if_node_index_not_active(current);
        return suffix_link_no_checks(current);
      }

      // TODO private?
      [[nodiscard]] Node const& node(index_type i) const {
        throw_if_node_index_out_of_range(i);
        return node_no_checks(i);
      }

      // TODO private?
      [[nodiscard]] index_type child_no_checks(index_type  parent,
                                               letter_type letter) const {
        LIBSEMIGROUPS_ASSERT(parent < _all_nodes.size());
        LIBSEMIGROUPS_ASSERT(_active_nodes_index.count(parent) == 1);
        return _children.get(parent, letter);
      }

      // TODO private?
      [[nodiscard]] index_type child(index_type  parent,
                                     letter_type letter) const {
        throw_if_node_index_not_active(parent);
        return child_no_checks(parent, letter);
      }

      // TODO private?
      [[nodiscard]] size_t
      number_of_children_no_checks(index_type i) const noexcept {
        return _children.number_of_cols()
               - std::count(
                   _children.cbegin_row(i), _children.cend_row(i), UNDEFINED);
      }

      // TODO private?
      [[nodiscard]] size_t number_of_children(index_type i) const noexcept {
        throw_if_node_index_not_active(i);
        return number_of_children_no_checks(i);
      }

      // TODO private?
      template <typename Iterator>
      [[nodiscard]] index_type traverse_trie_no_checks(Iterator first,
                                                       Iterator last) const;
      // TODO private?
      template <typename Iterator>
      [[nodiscard]] index_type traverse_trie(Iterator first,
                                             Iterator last) const {
        throw_if_any_letter_out_of_range(first, last);
        return traverse_trie_no_checks(first, last);
      }

      // TODO private?
      void throw_if_node_index_out_of_range(index_type i) const;
      // TODO private?
      void throw_if_node_index_not_active(index_type i) const;

     private:
      ////////////////////////////////////////////////////////////////////////
      // Exceptions
      ////////////////////////////////////////////////////////////////////////

      void throw_if_letter_out_of_range(index_type i) const;

      template <typename Iterator>
      void throw_if_any_letter_out_of_range(Iterator first,
                                            Iterator last) const {
        for (auto it = first; it != last; ++it) {
          throw_if_letter_out_of_range(*it);
        }
      }

      ////////////////////////////////////////////////////////////////////////
      // Activate or deactivate a node
      ////////////////////////////////////////////////////////////////////////

      [[nodiscard]] bool is_active_node(index_type i) {
        return _active_nodes_index.find(i) != _active_nodes_index.end();
      }

      [[nodiscard]] index_type new_active_node_no_checks(index_type  parent,
                                                         letter_type a);

      void deactivate_node_no_checks(index_type i);

      ////////////////////////////////////////////////////////////////////////
      // Update suffix link sources
      ////////////////////////////////////////////////////////////////////////

      // Add <source_index> as a suffix link source of <target_index>, i.e.
      // _all_nodes[source_index].suffix_link() == target_index
      void add_suffix_link_source(index_type source_index,
                                  index_type target_index);

      // Remove <source_index> as a suffix link source of <target_index>, i.e.
      // _all_nodes[source_index].suffix_link() == target_index
      void rm_suffix_link_source(index_type source_index,
                                 index_type target_index);

      void populate_node_indices_to_update(index_type  target_index,
                                           index_type  new_node_index,
                                           letter_type a);
    };  // class AhoCorasickImpl

    namespace aho_corasick_impl {

      // TODO rm?
      template <typename Value, typename Iterator>
      typename AhoCorasickImpl<Value>::index_type
      traverse_word_no_checks(AhoCorasickImpl<Value> const&               ac,
                              typename AhoCorasickImpl<Value>::index_type start,
                              Iterator                                    first,
                              Iterator                                    last);

      // TODO rm?
      template <typename Value, typename Iterator>
      typename AhoCorasickImpl<Value>::index_type
      traverse_word_no_checks(AhoCorasickImpl<Value> const& ac,
                              Iterator                      first,
                              Iterator                      last) {
        return traverse_word_no_checks(ac, ac.root, first, last);
      }

      // TODO rm?
      template <typename Value, typename Word>
      [[nodiscard]] typename AhoCorasickImpl<Value>::index_type
      traverse_word_no_checks(AhoCorasickImpl<Value>& ac, Word const& w) {
        return traverse_word_no_checks(ac, w.begin(), w.end());
      }

      template <typename Value, typename Iterator>
      class SearchIterator {
        using index_type = typename AhoCorasickImpl<Value>::index_type;

        Iterator                      _first;
        Iterator                      _last;
        index_type                    _prefix;
        index_type                    _suffix;
        AhoCorasickImpl<Value> const& _trie;

       public:
        using iterator_category = std::input_iterator_tag;
        using value_type        = index_type;
        using difference_type   = std::ptrdiff_t;
        using pointer           = value_type const*;
        using reference         = value_type const&;

        SearchIterator(AhoCorasickImpl<Value> const& trie,
                       Iterator                      first,
                       Iterator                      last);

        explicit SearchIterator(AhoCorasickImpl<Value> const& trie);

        reference operator*() const {
          // TODO(1) would be easy enough to return the position of the match
          // also, I think it's just height(_prefix) - height(_suffix)
          return _suffix;
        }

        // Pre-increment
        SearchIterator& operator++();

        // Post-increment
        SearchIterator operator++(int) {
          SearchIterator tmp = *this;
          ++(*this);
          return tmp;
        }

        friend bool operator==(SearchIterator const& a,
                               SearchIterator const& b) {
          // TODO(1) more?
          return a._prefix == b._prefix && a._suffix == b._suffix;
        }

        friend bool operator!=(SearchIterator const& a,
                               SearchIterator const& b) {
          return !(a == b);
        }
      };  // class SearchIterator

      // Deduction guide
      template <typename Value, typename Iterator>
      SearchIterator(AhoCorasickImpl<Value> const& ac,
                     Iterator                      first,
                     Iterator last) -> SearchIterator<Value, Iterator>;

      template <typename Value, typename Iterator>
      [[nodiscard]] auto
      begin_search_no_checks(AhoCorasickImpl<Value> const& ac,
                             Iterator                      first,
                             Iterator                      last) {
        return SearchIterator(ac, first, last);
      }

      template <typename Value, typename Iterator>
      [[nodiscard]] auto end_search_no_checks(AhoCorasickImpl<Value> const& ac,
                                              Iterator,
                                              Iterator) {
        return SearchIterator<Value, Iterator>(ac);
      }

      // TODO: ac should be a const&
      template <typename Value, typename Word>
      [[nodiscard]] auto begin_search_no_checks(AhoCorasickImpl<Value>& ac,
                                                Word const&             w) {
        return begin_search_no_checks(ac, w.begin(), w.end());
      }

      // TODO: ac should be a const&
      template <typename Value, typename Word>
      [[nodiscard]] auto end_search_no_checks(AhoCorasickImpl<Value>& ac,
                                              Word const&             w) {
        return end_search_no_checks(ac, w.begin(), w.end());
      }

    }  // namespace aho_corasick_impl
  }  // namespace detail
}  // namespace libsemigroups

#include "aho-corasick-impl.tpp"

#endif  // LIBSEMIGROUPS_DETAIL_AHO_CORASICK_IMPL_HPP_
