//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019-2025 James D. Mitchell + Joseph Edwards
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
// This file contains implementations of the member functions for the
// AhoCorasickImpl<Value> class.

#include "libsemigroups/detail/aho-corasick-impl.hpp"
#include <optional>
namespace libsemigroups {
  namespace detail {

    template <typename Value>
    template <typename Iterator, typename... Args>
    typename AhoCorasickImpl<Value>::index_type
    AhoCorasickImpl<Value>::emplace_no_checks(Iterator first,
                                              Iterator last,
                                              Args&&... args) {
      index_type current = root;
      for (auto it = first; it != last; ++it) {
        index_type next = _children.get(current, *it);
        if (next == UNDEFINED) {
          // index of next node added
          next = new_active_node_no_checks(current, *it);
        }
        current = next;
      }
      _terminal_nodes_index.emplace(current);
      _all_nodes[current].value = Value(std::forward<Args>(args)...);

      return current;
    }
    template <typename Value>
    template <typename Iterator, typename... Args>
    typename AhoCorasickImpl<Value>::index_type
    AhoCorasickImpl<Value>::emplace(Iterator first,
                                    Iterator last,
                                    Args&&... args) {
      auto last_index = traverse_trie(first, last);
      if (last_index != UNDEFINED && _all_nodes[last_index].value.has_value()) {
        std::string word;
        if constexpr (std::is_same_v<
                          std::decay_t<decltype(*std::declval<Iterator>())>,
                          char>) {
          word = to_printable(std::string(first, last));
        } else {
          word = fmt::format("[{}]", fmt::join(first, last, ", "));
        }
        LIBSEMIGROUPS_EXCEPTION(
            "the word {} given by the arguments [first, last) already belongs "
            "to the trie, and cannot be added again",
            word);
      }
      return emplace_no_checks(first, last, std::forward<Args>(args)...);
    }

    template <typename Value>
    template <typename Iterator>
    typename AhoCorasickImpl<Value>::index_type
    AhoCorasickImpl<Value>::erase_no_checks(Iterator first, Iterator last) {
      auto last_index = traverse_trie_no_checks(first, last);
      auto rule_index = last_index;
      if (number_of_children_no_checks(last_index) != 0) {
        LIBSEMIGROUPS_ASSERT(_all_nodes[last_index].terminal());
        _terminal_nodes_index.erase(last_index);
        _all_nodes[last_index].value = std::nullopt;
        return rule_index;
      }

      _node_indices_to_update.clear();

      auto parent_index  = _all_nodes[last_index].parent();
      auto parent_letter = *(last - 1);
      deactivate_node_no_checks(last_index);
      while (number_of_children_no_checks(parent_index) == 1
             && !_all_nodes[parent_index].terminal() && parent_index != root) {
        last_index    = parent_index;
        parent_index  = _all_nodes[last_index].parent();
        parent_letter = _all_nodes[last_index].parent_letter();
        deactivate_node_no_checks(last_index);
      }
      _children.set(parent_index, parent_letter, UNDEFINED);

      return rule_index;
    }

    template <typename Value>
    template <typename Iterator>
    typename AhoCorasickImpl<Value>::index_type
    AhoCorasickImpl<Value>::erase(Iterator first, Iterator last) {
      auto last_index = traverse_trie(first, last);
      if (last_index == UNDEFINED) {
        LIBSEMIGROUPS_EXCEPTION("cannot remove the word {} given by the "
                                "arguments [first, last), as it does not "
                                "correspond to a node in the trie",
                                word_type(first, last));
      }
      if (!_all_nodes[last_index].terminal()) {
        LIBSEMIGROUPS_EXCEPTION("cannot remove the word {} given by the "
                                "arguments [first, last), as it does not "
                                "correspond to a terminal node in the trie",
                                word_type(first, last));
      }
      return erase_no_checks(first, last);
    }

    template <typename Value>
    template <typename Iterator>
    typename AhoCorasickImpl<Value>::index_type
    AhoCorasickImpl<Value>::traverse_trie_no_checks(Iterator first,
                                                    Iterator last) const {
      index_type current = root;
      for (auto it = first; it != last; ++it) {
        current = _children.get(current, *it);
        if (current == UNDEFINED) {
          return current;
        }
      }
      return current;
    }

    ////////////////////////////////////////////////////////////////////////
    // Node nested class
    ////////////////////////////////////////////////////////////////////////

    template <typename Value>
    AhoCorasickImpl<Value>::Node::Node(index_type parent, letter_type a)
        : _height(), _link(), _parent(), _parent_letter(), value(std::nullopt) {
      init(parent, a);
    }

    template <typename Value>
    typename AhoCorasickImpl<Value>::Node&
    AhoCorasickImpl<Value>::Node::init(index_type i, letter_type a) noexcept {
      _height = i == UNDEFINED ? 0 : UNDEFINED;
      if (_parent == root || _parent == UNDEFINED) {
        _link = root;
      } else {
        _link = UNDEFINED;
      }
      _parent        = i;
      _parent_letter = a;
      _suffix_link_sources.clear();

      value = std::nullopt;

      // Cannot set _link or _height here because we don't have access to the
      // relevant info here.
      return *this;
    }

    ////////////////////////////////////////////////////////////////////////
    // AhoCorasickImpl<Value> class
    ////////////////////////////////////////////////////////////////////////

    template <typename Value>
    AhoCorasickImpl<Value>::AhoCorasickImpl()
        : _all_nodes({Node()}),
          _children(0, 1, UNDEFINED),
          _active_nodes_index({root}),
          _inactive_nodes_index(),
          _node_indices_to_update(),
          _terminal_nodes_index() {}

    template <typename Value>
    AhoCorasickImpl<Value>& AhoCorasickImpl<Value>::init() {
      init(0);
      return *this;
    }

    template <typename Value>
    AhoCorasickImpl<Value>::AhoCorasickImpl(AhoCorasickImpl<Value> const&)
        = default;
    template <typename Value>
    AhoCorasickImpl<Value>::AhoCorasickImpl(AhoCorasickImpl<Value>&&) = default;

    template <typename Value>
    AhoCorasickImpl<Value>&
    AhoCorasickImpl<Value>::operator=(AhoCorasickImpl<Value> const&)
        = default;
    template <typename Value>
    AhoCorasickImpl<Value>&
    AhoCorasickImpl<Value>::operator=(AhoCorasickImpl<Value>&&)
        = default;

    template <typename Value>
    AhoCorasickImpl<Value>::AhoCorasickImpl(size_t num_letters)
        : _all_nodes({Node()}),
          _children(num_letters, 1, UNDEFINED),
          _active_nodes_index({root}),
          _inactive_nodes_index(),
          _node_indices_to_update(),
          _terminal_nodes_index() {}

    template <typename Value>
    AhoCorasickImpl<Value>& AhoCorasickImpl<Value>::init(size_t num_letters) {
      LIBSEMIGROUPS_ASSERT(!_all_nodes.empty());
      LIBSEMIGROUPS_ASSERT(!_active_nodes_index.empty());

      _children.init(num_letters, _all_nodes.size(), UNDEFINED);
      size_t const old_num_inactive_nodes = _inactive_nodes_index.size();
      _inactive_nodes_index.resize(old_num_inactive_nodes
                                   + _active_nodes_index.size() - 1);
      std::copy_if(_active_nodes_index.begin(),
                   _active_nodes_index.end(),
                   _inactive_nodes_index.begin() + old_num_inactive_nodes,
                   [](auto val) { return val != root; });
      std::sort(_inactive_nodes_index.begin(),
                _inactive_nodes_index.end(),
                std::greater{});
      _active_nodes_index.clear();
      _active_nodes_index.insert(root);
      _all_nodes[0].init();
      _terminal_nodes_index.clear();
      LIBSEMIGROUPS_ASSERT(_active_nodes_index.size()
                               + _inactive_nodes_index.size()
                           == _all_nodes.size());
      LIBSEMIGROUPS_ASSERT(_children.number_of_rows() == _all_nodes.size());

      return *this;
    }

    template <typename Value>
    AhoCorasickImpl<Value>::~AhoCorasickImpl() = default;

    template <typename Value>
    AhoCorasickImpl<Value>&
    AhoCorasickImpl<Value>::increase_alphabet_size_by(size_t val) {
      size_t c = _children.number_of_cols();
      _children.add_cols(val);
      for (; c < _children.number_of_cols(); ++c) {
        std::fill(
            _children.begin_column(c), _children.end_column(c), UNDEFINED);
      }
      return *this;
    }

    template <typename Value>
    [[nodiscard]] size_t
    AhoCorasickImpl<Value>::height_no_checks(index_type i) const {
      LIBSEMIGROUPS_ASSERT(i < _all_nodes.size());
      LIBSEMIGROUPS_ASSERT(_active_nodes_index.count(i) == 1);
      return _all_nodes[i].height();
    }

    template <typename Value>
    [[nodiscard]] bool
    AhoCorasickImpl<Value>::terminal_no_checks(index_type i) const {
      LIBSEMIGROUPS_ASSERT(i < _all_nodes.size());
      LIBSEMIGROUPS_ASSERT(_active_nodes_index.count(i) == 1);
      LIBSEMIGROUPS_ASSERT(_all_nodes[i].terminal()
                           == (_terminal_nodes_index.count(i) != 0));
      return _all_nodes[i].terminal();
    }

    template <typename Value>
    [[nodiscard]] typename AhoCorasickImpl<Value>::index_type
    AhoCorasickImpl<Value>::new_active_node_no_checks(index_type  parent_index,
                                                      letter_type a) {
      LIBSEMIGROUPS_ASSERT(parent_index < _all_nodes.size());
      LIBSEMIGROUPS_ASSERT(_active_nodes_index.count(parent_index) == 1);

      if (_inactive_nodes_index.empty()) {
        size_t const old_nodes_size         = _all_nodes.size();
        size_t const old_num_inactive_nodes = _inactive_nodes_index.size();

        _all_nodes.resize(2 * old_nodes_size);
        _inactive_nodes_index.resize(old_num_inactive_nodes + old_nodes_size);
        std::iota(_inactive_nodes_index.begin() + old_num_inactive_nodes,
                  _inactive_nodes_index.end(),
                  index_type(old_nodes_size));
        std::sort(_inactive_nodes_index.begin(),
                  _inactive_nodes_index.end(),
                  std::greater{});
        _children.add_rows(old_nodes_size);
        return new_active_node_no_checks(parent_index, a);
      }

      index_type new_node_index = _inactive_nodes_index.back();
      _inactive_nodes_index.pop_back();
      _active_nodes_index.insert(new_node_index);
      _all_nodes[new_node_index].init(parent_index, a);
      std::fill(_children.begin_row(new_node_index),
                _children.end_row(new_node_index),
                UNDEFINED);

      // Set the suffix link and height of new node
      auto&      new_node   = _all_nodes[new_node_index];
      index_type link_index = traverse_no_checks(
          suffix_link_no_checks(new_node.parent()), new_node.parent_letter());
      LIBSEMIGROUPS_ASSERT(link_index != UNDEFINED);
      new_node.suffix_link(link_index);
      new_node.height(_all_nodes[new_node.parent()].height() + 1);

      // We have to collect the node indices to update, and then update them,
      // because we must traverse the suffix link sources here, and so we cannot
      // change them at the same time.
      _node_indices_to_update.clear();
      populate_node_indices_to_update(parent_index, new_node_index, a);
      for (index_type node_index : _node_indices_to_update) {
        auto& node = _all_nodes[node_index];
        LIBSEMIGROUPS_ASSERT(node_index != new_node_index);
        LIBSEMIGROUPS_ASSERT(node.suffix_link() != new_node_index);
        rm_suffix_link_source(node_index, node.suffix_link());
        node.suffix_link(new_node_index);
        add_suffix_link_source(node_index, new_node_index);
      }

      // Add new node as a source of its suffix link
      add_suffix_link_source(new_node_index, link_index);
      // set new_node_index as child of parent
      _children.set(parent_index, a, new_node_index);

      return new_node_index;
    }

    template <typename Value>
    void
    AhoCorasickImpl<Value>::deactivate_node_no_checks(index_type node_index) {
      LIBSEMIGROUPS_ASSERT(node_index < _all_nodes.size());
      // For each active suffix link source <current_source> of <node_index>,
      // push <current_source> to the vector of nodes which need to have their
      // suffix link updated.
      auto& node = _all_nodes[node_index];
      for (auto current_source_index : node.suffix_link_sources()) {
        LIBSEMIGROUPS_ASSERT(_all_nodes[current_source_index].suffix_link()
                             == node_index);
        if (is_active_node(current_source_index)) {
          auto&      current_source    = _all_nodes[current_source_index];
          index_type suffix_link_index = current_source.suffix_link();
          index_type next_suffix_link_index
              = _all_nodes[suffix_link_index].suffix_link();
          while (!is_active_node(next_suffix_link_index)) {
            suffix_link_index = next_suffix_link_index;
            next_suffix_link_index
                = _all_nodes[next_suffix_link_index].suffix_link();
          }
          current_source.suffix_link(next_suffix_link_index);
          add_suffix_link_source(current_source_index, next_suffix_link_index);
        }
      }
      rm_suffix_link_source(node_index, _all_nodes[node_index].suffix_link());

#ifdef LIBSEMIGROUPS_DEBUG
      auto num_removed =
#endif
          _active_nodes_index.erase(node_index);
      LIBSEMIGROUPS_ASSERT(num_removed == 1);
      _terminal_nodes_index.erase(node_index);
      _inactive_nodes_index.push_back(node_index);
    }

    template <typename Value>
    void AhoCorasickImpl<Value>::throw_if_node_index_out_of_range(
        index_type i) const {
      if (i >= _all_nodes.size()) {
        LIBSEMIGROUPS_EXCEPTION(
            "invalid index, expected value in range [0, {}), found {}",
            _all_nodes.size(),
            i);
      }
    }

    template <typename Value>
    void
    AhoCorasickImpl<Value>::throw_if_node_index_not_active(index_type i) const {
      throw_if_node_index_out_of_range(i);
      if (_active_nodes_index.count(i) != 1) {
        LIBSEMIGROUPS_EXCEPTION(
            "invalid index, expected an index of an active node, found {}", i);
      }
    }

    template <typename Value>
    void
    AhoCorasickImpl<Value>::throw_if_letter_out_of_range(index_type i) const {
      if (i >= alphabet_size()) {
        LIBSEMIGROUPS_EXCEPTION(
            "expected a value [0, {}), found {}", alphabet_size(), i);
      }
    }

    // Add <source_index> as a suffix link source of <target_index>, i.e.
    // _all_nodes[source_index].suffix_link() == target_index
    template <typename Value>
    void
    AhoCorasickImpl<Value>::add_suffix_link_source(index_type source_index,
                                                   index_type target_index) {
      LIBSEMIGROUPS_ASSERT(source_index != target_index);
#ifdef LIBSEMIGROUPS_DEBUG
      auto [it, inserted] =
#endif
          _all_nodes[target_index].suffix_link_sources().insert(source_index);
      LIBSEMIGROUPS_ASSERT(inserted);
    }

    // Remove <source_index> as a suffix link source of <target_index>, i.e.
    // _all_nodes[source_index].suffix_link() == target_index
    template <typename Value>
    void
    AhoCorasickImpl<Value>::rm_suffix_link_source(index_type source_index,
                                                  index_type target_index) {
      LIBSEMIGROUPS_ASSERT(source_index != target_index);

#ifdef LIBSEMIGROUPS_DEBUG
      auto num_erased =
#endif
          _all_nodes[target_index]._suffix_link_sources.erase(source_index);
      LIBSEMIGROUPS_ASSERT(num_erased == 1);
    }

    template <typename Value>
    void AhoCorasickImpl<Value>::populate_node_indices_to_update(
        index_type  target_index,
        index_type  new_node_index,
        letter_type a) {
      auto& target = _all_nodes[target_index];

      for (auto current_source_index : target._suffix_link_sources) {
        LIBSEMIGROUPS_ASSERT(current_source_index != new_node_index);
        index_type child_index = _children.get(current_source_index, a);
        if (child_index == UNDEFINED) {
          populate_node_indices_to_update(
              current_source_index, new_node_index, a);
        } else {
          _node_indices_to_update.push_back(child_index);
        }
      }
    }

    namespace aho_corasick_impl {

      template <typename Value, typename Iterator>
      typename AhoCorasickImpl<Value>::index_type
      traverse_word_no_checks(AhoCorasickImpl<Value> const&               ac,
                              typename AhoCorasickImpl<Value>::index_type start,
                              Iterator                                    first,
                              Iterator last) {
        typename AhoCorasickImpl<Value>::index_type current = start;
        for (auto it = first; it != last; ++it) {
          current = ac.traverse_no_checks(current, *it);
        }
        return current;
      }

      template <typename Value, typename Iterator>
      SearchIterator<Value, Iterator>::SearchIterator(
          AhoCorasickImpl<Value> const& trie,
          Iterator                      first,
          Iterator                      last)
          : _first(first),
            _last(last),
            _prefix(trie.root),
            _suffix(trie.root),
            _trie(trie) {
        operator++();
      }

      template <typename Value, typename Iterator>
      SearchIterator<Value, Iterator>::SearchIterator(
          AhoCorasickImpl<Value> const& trie)
          : _first(),
            _last(),
            _prefix(UNDEFINED),
            _suffix(UNDEFINED),
            _trie(trie) {}

      // Pre-increment
      template <typename Value, typename Iterator>
      SearchIterator<Value, Iterator>&
      SearchIterator<Value, Iterator>::operator++() {
        if (_suffix == UNDEFINED) {
          // We're at the end
          return *this;
        }
        // Every subword is a suffix of a prefix, so we follow the edges
        // labeled by _first to _last to some node _prefix, then consider
        // all the suffixes of _prefix by following the suffix links back to
        // the root.
        while (_suffix != _trie.root) {
          _suffix = _trie.suffix_link_no_checks(_suffix);
          if (_trie.node_no_checks(_suffix).terminal()) {
            // the _suffix of the _prefix of [first, last) is a match so
            // return.
            return *this;
          }
        }
        // TODO(1) Can this be improved so that we don't revisit suffixes that
        // we have already checked?
        while (_first != _last && _prefix != UNDEFINED) {
          auto x = *_first;
          ++_first;
          _prefix
              = _trie.traverse_no_checks(_prefix, static_cast<letter_type>(x));
          _suffix = _prefix;
          do {
            if (_trie.node_no_checks(_suffix).terminal()) {
              return *this;
            }
            _suffix = _trie.suffix_link_no_checks(_suffix);
          } while (_suffix != _trie.root);
        }
        _prefix = UNDEFINED;
        _suffix = UNDEFINED;
        return *this;
      }

    }  // namespace aho_corasick_impl
  }  // namespace detail
}  // namespace libsemigroups
