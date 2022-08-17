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
// congruence" algorithm for semigroups and monoids.
// TODO:
// * implement joins, meets, containment?
// * generating pairs for congruences defined by "action digraph"
// * minimum degree transformation representations of semigroups/monoids
//
// Notes:
// 1. In 2022, when first writing this file, JDM tried templating the word_type
//    used by the presentations in Sims1 (so that we could use StaticVector1
//    for example, using smaller integer types for letters, and the stack to
//    hold the words rather than the heap), but this didn't seem to give any
//    performance improvement, and so I backed out the changes.

#ifndef LIBSEMIGROUPS_SIMS1_HPP_
#define LIBSEMIGROUPS_SIMS1_HPP_

#include <algorithm>  // for find_if
#include <cstddef>    // for size_t
#include <cstdint>    // for uint64_t
#include <deque>
#include <iterator>  // for forward_iterator_tag
#include <thread>
#include <type_traits>  // for is_base_of
#include <vector>       // for vector

#include "config.hpp"          // for LIBSEMIGROUPS_ENABLE_STATS
#include "digraph.hpp"         // for ActionDigraph
#include "felsch-digraph.hpp"  // for FelschDigraph
#include "make-present.hpp"    // for make
#include "present.hpp"         // for Presentation
#include "types.hpp"           // for word_type, congruence_kind

#include "report.hpp"

namespace libsemigroups {

#ifdef LIBSEMIGROUPS_ENABLE_STATS
  namespace sims1 {
    struct Stats {
      double   mean_depth     = 0;
      uint64_t max_depth      = 0;
      uint64_t max_pending    = 0;
      uint64_t num_nodes      = 0;
      uint64_t num_good_nodes = 0;
      uint64_t depth          = 0;
    };
  }  // namespace sims1
#endif

  namespace detail {
    // From p, 275, Section 8 of C++ concurrency in action, 2nd edition, by
    // Anthony Williams.
    class JoinThreads {
      std::vector<std::thread>& _threads;

     public:
      explicit JoinThreads(std::vector<std::thread>& threads)
          : _threads(threads) {}

      ~JoinThreads() {
        for (size_t i = 0; i < _threads.size(); ++i) {
          if (_threads[i].joinable()) {
            _threads[i].join();
          }
        }
      }
    };

  }  // namespace detail

  //! Defined in ``sims1.hpp``.
  //!
  //! On this page we describe the functionality relating to the small index
  //! congruence algorithm. The algorithm implemented by this class template is
  //! essentially the low index subgroup algorithm for finitely presented
  //! groups described in Section 5.6 of [Computation with Finitely Presented
  //! Groups](https://doi.org/10.1017/CBO9780511574702) by C. Sims. The low
  //! index subgroups algorithm was adapted for semigroups and monoids by J. D.
  //! Mitchell and M. Tsalakou.
  //!
  //! The purpose of this class is to provide the functions \ref cbegin and
  //! \ref cend, which permit iterating through the one-sided congruences of a
  //! semigroup or monoid defined by a presentation containing (a possibly
  //! empty) set of pairs and with at most a given number of classes. An
  //! iterator returned by \ref cbegin points at an ActionDigraph instance
  //! containing the action of the semigroup or monoid on the classes of a
  //! congruence.
  template <typename T>
  class Sims1 {
   public:
    //! Type for the nodes in the associated ActionDigraph objects.
    using node_type = T;

    //! Type for letters in the underlying presentation.
    using letter_type = typename word_type::value_type;

    //! The size_type of the associated ActionDigraph objects.
    using size_type = typename ActionDigraph<node_type>::size_type;

    //! The type of the associated ActionDigraph objects.
    // We use ActionDigraph, even though the iterators produced by this class
    // hold FelschDigraph's, none of the features of FelschDigraph are useful
    // for the output, only for the implementation
    using digraph_type = ActionDigraph<node_type>;

   private:
    Presentation<word_type> _extra;
    Presentation<word_type> _final;
    Presentation<word_type> _presentation;
    // Reporting can be handled outside the class in any code using this

   public:
    //! Construct from \ref congruence_kind and Presentation.
    //!
    //! \param ck the handedness of the congruences (left or right)
    //! \param p the presentation
    //!
    //! \throws LibsemigroupsException if \p ck is \ref
    //! congruence_kind::twosided
    //! \throws LibsemigroupsException if `p.validate()` throws.
    //!
    //! \sa \ref cbegin and \ref cend for a description of the meaning of the
    //! parameters.
    Sims1(congruence_kind ck, Presentation<word_type> const& p);

    //! Construct from \ref congruence_kind and two Presentation objects.
    //!
    //! \param ck the handedness of the congruences (left or right)
    //! \param p the presentation defining the semigroup
    //! \param e presentation containing additional relations
    //!
    //! \throws LibsemigroupsException if \p ck is \ref
    //! congruence_kind::twosided
    //! \throws LibsemigroupsException if `p.validate()` throws.
    //!
    //! \sa \ref cbegin and \ref cend for a description of the meaning of the
    //! parameters.
    //!
    //! \note The presentations provided are copied when an instance of Sims1
    //! is created, and the return values of \ref presentation and \ref extra
    //! may not be identical to \p p and \p e. See \ref presentation for
    //! further details.
    Sims1(congruence_kind                ck,
          Presentation<word_type> const& p,
          Presentation<word_type> const& e);

    //! Construct from \ref congruence_kind and Presentation.
    //!
    //! \param ck the handedness of the congruences (left or right)
    //! \param p the presentation
    //!
    //! \throws LibsemigroupsException if \p ck is \ref
    //! congruence_kind::twosided
    //! \throws LibsemigroupsException if `p.validate()` throws.
    //!
    //! \sa \ref cbegin and \ref cend for a description of the meaning of the
    //! parameters.
    template <typename P>
    Sims1(congruence_kind ck, P const& p) : Sims1(ck, p, P()) {}

    //! Construct from \ref congruence_kind and two Presentation objects.
    //!
    //! \param ck the handedness of the congruences (left or right)
    //! \param p the presentation defining the semigroup
    //! \param e presentation containing additional relations
    //!
    //! \throws LibsemigroupsException if \p ck is
    //! `congruence_kind::twosided`
    //! \throws LibsemigroupsException if `p.validate()` throws.
    //!
    //! \sa \ref cbegin and \ref cend for a description of the meaning of the
    //! parameters.
    //!
    //! \note The presentations provided are copied when an instance of Sims1
    //! is created, and the return values of \ref presentation and \ref extra
    //! may not be identical to \p p and \p e. See \ref presentation for
    //! further details.
    template <typename P>
    Sims1(congruence_kind ck, P const& p, P const& e)
        : Sims1(ck,
                make<Presentation<word_type>>(p),
                make<Presentation<word_type>>(e)) {
      static_assert(std::is_base_of<PresentationBase, P>::value,
                    "the template parameter P must be derived from "
                    "PresentationBase");
    }

    //! Default constructor - deleted!
    Sims1() = delete;

    //! Default copy constructor.
    Sims1(Sims1 const&) = default;

    //! Default move constructor.
    Sims1(Sims1&&) = default;

    //! Default copy assignment operator.
    Sims1& operator=(Sims1 const&) = default;

    //! Default move assignment operator.
    Sims1& operator=(Sims1&&) = default;

    ~Sims1();

    //! Returns a const reference to the defining presentation.
    //!
    //! This function returns the defining presentation of a Sims1 instance.
    //! The congruences computed by \ref cbegin and \ref cend are defined over
    //! the semigroup or monoid defined by this presentation.
    //!
    //! Note that it might not be the case that the value returned by this
    //! function and the presentation used to construct the object are the
    //! same. A Sims1 object requires the generators of the defining
    //! presentation \f$\mathcal{P}\f$ to be \f$\{0, \ldots, n - 1\}\f$ where
    //! \f$n\f$ is the size of the alphabet of \f$\mathcal{P}\f$. Every
    //! occurrence of every generator \c a in the presentation \c p used to
    //! construct a Sims1 instance is replaced by `p.index(a)`.
    //!
    //! \parameters
    //! (None)
    //!
    //! \returns
    //! A const reference to a Presentation object.
    //!
    //! \exceptions
    //! \noexcept
    //!
    //! \warning
    //! If \ref split_at has been called, then some of the defining relations
    //! may have been removed from the presentation.
    Presentation<word_type> const& presentation() const noexcept {
      return _presentation;
    }

    //! Returns a const reference to the additional defining pairs.
    //!
    //! The congruences computed by \ref cbegin and \ref cend always contain
    //! the relations of this presentation. In other words, the congruences
    //! computed by this instance are only taken among those that contains the
    //! pairs of elements of the underlying semigroup (defined by the
    //! presentation returned by presentation()) represented by the
    //! relations of the presentation returned by extra().
    //!
    //! \sa \ref presentation for further details about the return value of
    //! this function.
    //!
    //! \exceptions
    //! \noexcept
    Presentation<word_type> const& extra() const noexcept {
      return _extra;
    }

    //! Only apply certain relations when an otherwise compatible ActionDigraph
    //! is found.
    //!
    //! This function splits the relations in the underlying presentation into
    //! two parts: those before the relation with index \p val and those after.
    //! The order of the relations is the same as the order in the constructing
    //! presentation. In some instances if the relations after index \p val are
    //! "long" and those before are "short", then this can improve the
    //! performance. It can also make the performance worse, and should be used
    //! with care.
    //!
    //! \param val the relation to split at
    //!
    //! \returns (None)
    //!
    //! \throws LibsemigroupsException if \p val is out of bounds.
    // TODO some tests for this.
    void split_at(size_type val) {
      if (val > _presentation.rules.size() / 2 + _final.rules.size() / 2) {
        LIBSEMIGROUPS_EXCEPTION(
            "expected a value in the range [0, %llu), found %llu",
            uint64_t(_presentation.rules.size() / 2 + _final.rules.size() / 2),
            uint64_t(val));
      }

      val *= 2;
      if (val < _presentation.rules.size()) {
        _final.rules.insert(_final.rules.begin(),
                            _presentation.rules.begin() + val,
                            _presentation.rules.end());
        _presentation.rules.erase(_presentation.rules.begin() + val,
                                  _presentation.rules.end());
      } else {
        val -= _presentation.rules.size();
        _presentation.rules.insert(_presentation.rules.end(),
                                   _final.rules.begin(),
                                   _final.rules.begin() + val);
        _final.rules.erase(_final.rules.begin(), _final.rules.begin() + val);
      }
    }

    struct const_iterator_base {
      friend class Den;
      //! No doc
      using size_type = typename std::vector<digraph_type>::size_type;
      //! No doc
      using difference_type =
          typename std::vector<digraph_type>::difference_type;
      //! No doc
      using const_pointer = typename std::vector<digraph_type>::const_pointer;
      //! No doc
      using pointer = typename std::vector<digraph_type>::pointer;
      //! No doc
      using const_reference =
          typename std::vector<digraph_type>::const_reference;
      //! No doc
      using reference = typename std::vector<digraph_type>::reference;
      //! No doc
      using value_type = digraph_type;
      //! No doc
      using iterator_category = std::forward_iterator_tag;

      struct PendingDef {
        PendingDef() = default;

        PendingDef(node_type   s,
                   letter_type g,
                   node_type   t,
                   size_type   e,
                   size_type   n) noexcept
            : source(s), generator(g), target(t), num_edges(e), num_nodes(n) {}
        node_type   source;
        letter_type generator;
        node_type   target;
        size_type   num_edges;  // Number of edges in the graph when *this was
                                // added to the stack
        size_type num_nodes;    // Number of nodes in the graph after the
                                // definition is made
      };

      Presentation<word_type>             _extra;
      FelschDigraph<word_type, node_type> _felsch_graph;
      Presentation<word_type>             _final;
      size_type                           _max_num_classes;
      size_type                           _min_target_node;
      size_type                           _num_active_nodes;
      size_type                           _num_gens;

      //! No doc
      const_iterator_base(Presentation<word_type> const& p,
                          Presentation<word_type> const& e,
                          Presentation<word_type> const& f,
                          size_type                      n);

      // None of the constructors are noexcept because the corresponding
      // constructors for std::vector aren't (until C++17).
      //! No doc
      const_iterator_base() = delete;
      //! No doc
      const_iterator_base(const_iterator_base const&) = default;
      //! No doc
      const_iterator_base(const_iterator_base&&) = default;
      //! No doc
      const_iterator_base& operator=(const_iterator_base const&) = default;
      //! No doc
      const_iterator_base& operator=(const_iterator_base&&) = default;

      //! No doc
      virtual ~const_iterator_base() = default;

      //! No doc
      bool operator==(const_iterator_base const& that) const noexcept {
        if (_num_active_nodes == 0 && that._num_active_nodes == 0) {
          return true;
        }
        return _num_active_nodes == that._num_active_nodes
               && _felsch_graph == that._felsch_graph;
      }

      //! No doc
      bool operator!=(const_iterator_base const& that) const noexcept {
        return !(this->operator==(that));
      }

      //! No doc
      const_reference operator*() const noexcept {
        return _felsch_graph;
      }

      //! No doc
      const_pointer operator->() const noexcept {
        return &_felsch_graph;
      }

      //! No doc
      void swap(const_iterator_base& that) noexcept {
        std::swap(_extra, that._extra);
        std::swap(_felsch_graph, that._felsch_graph);
        std::swap(_max_num_classes, that._max_num_classes);
        std::swap(_min_target_node, that._min_target_node);
        std::swap(_num_active_nodes, that._num_active_nodes);
        std::swap(_num_gens, that._num_gens);
      }

      void clone(const_iterator_base const& that) {
        _felsch_graph     = that._felsch_graph;
        _num_active_nodes = that._num_active_nodes;
      }
    };

    //! No doc
    class const_iterator : public const_iterator_base {
     public:
      //! No doc
      using size_type = typename const_iterator_base::size_type;
      //! No doc
      using difference_type = typename const_iterator_base::difference_type;
      //! No doc
      using const_pointer = typename const_iterator_base::const_pointer;
      //! No doc
      using pointer = typename const_iterator_base::pointer;
      //! No doc
      using const_reference = typename const_iterator_base::const_reference;
      //! No doc
      using reference = typename const_iterator_base::reference;
      //! No doc
      using value_type = typename const_iterator_base::value_type;
      //! No doc
      using iterator_category = typename const_iterator_base::iterator_category;

     private:
      using PendingDef = typename const_iterator_base::PendingDef;

      std::vector<PendingDef> _pending;
#ifdef LIBSEMIGROUPS_ENABLE_STATS

     public:
      sims1::Stats const& stats() const noexcept;

     private:
      sims1::Stats _stats;
      void         stats_update(size_type);

#endif

     public:
      const_iterator(Presentation<word_type> const& p,
                     Presentation<word_type> const& e,
                     Presentation<word_type> const& f,
                     size_type                      n)
          : const_iterator_base(p, e, f, n) {
        if (this->_num_active_nodes == 0) {
          return;
        }
        if (n > 1) {
          _pending.emplace_back(0, 0, 1, 0, 2);
        }
        if (this->_min_target_node == 0) {
          _pending.emplace_back(0, 0, 0, 0, 1);
        }
        ++(*this);
        // The increment above is required so that when dereferencing any
        // instance of this type we obtain a valid word graph (o/w the value
        // pointed to here is empty).
      }

      using const_iterator_base::const_iterator_base;

      ~const_iterator() = default;

      // prefix
      //! No doc
      const_iterator const& operator++();

      //! No doc
      // postfix
      const_iterator operator++(int) {
        const_iterator copy(*this);
        ++(*this);
        return copy;
      }

      //! No doc
      void swap(const_iterator& that) noexcept {
        const_iterator_base::swap(that);
        std::swap(_pending, that._pending);
      }
    };

   public:
    //! Returns a forward iterator pointing at the first congruence.
    //!
    //! Returns a forward iterator pointing to the ActionDigraph representing
    //! the first congruence described by Sims1 object with at most \p n
    //! classes.
    //!
    //! If incremented, the iterator will point to the next such congruence.
    //! The order which the congruences are returned in is implementation
    //! specific. Iterators of the type returned by this function are equal
    //! whenever they point to equal objects. The iterator is exhausted if and
    //! only if it points to an ActionDigraph with zero nodes.
    //!
    //! \param n the maximum number of classes in a congruence.
    //!
    //! \returns
    //! An iterator \c it of type \c const_iterator pointing to an
    //! ActionDigraph with at most \p n nodes.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \warning
    //! Copying iterators of this type is expensive.  As a consequence, prefix
    //! incrementing \c ++it the returned  iterator \c it significantly cheaper
    //! than postfix incrementing \c it++.
    //!
    //! \sa
    //! \ref cend
    const_iterator cbegin(size_type n) const {
      return const_iterator(presentation(), _extra, _final, n);
    }

    //! Returns a forward iterator pointing one beyond the last congruence.
    //!
    //! Returns a forward iterator pointing to the empty ActionDigraph.
    //! If incremented, the returned iterator remains valid and continues to
    //! point at the empty ActionDigraph.
    //!
    //! \param n the maximum number of classes in a congruence.
    //!
    //! \returns
    //! An iterator \c it of type \c const_iterator pointing to an
    //! ActionDigraph with at most \p 0 nodes.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \warning
    //! Copying iterators of this type is expensive.  As a consequence, prefix
    //! incrementing \c ++it the returned  iterator \c it significantly cheaper
    //! than postfix incrementing \c it++.
    //!
    //! \sa
    //! \ref cbegin
    const_iterator cend(size_type) const {
      return const_iterator(presentation(), _extra, _final, 0);
    }

    //! Returns the number of one-sided congruences with up to a given number
    //! of classes.
    //!
    //! This function is synonymous with `std::distance(begin(), end())` and
    //! exists only to provide some feedback on the progress of the computation
    //! if it runs for more than 1 second.
    //!
    //! \param n the maximum number of congruence classes.
    //! \param num_threads TODO(Sims1)
    //!
    //! \returns A value of type \c uint64_t.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    // TODO(later): this should be in the sims1 helper namespace
    uint64_t number_of_congruences(size_type n,
                                   size_type num_threads = 1) const;

    // Apply the function pred to every one-sided congruence with at
    // most n classes
    void for_each(size_type                                n,
                  size_type                                num_threads,
                  std::function<void(digraph_type const&)> pred) const;

    // Apply the function pred to every one-sided congruence with at
    // most n classes, until pred returns true
    digraph_type find_if(size_type                                n,
                         size_type                                num_threads,
                         std::function<bool(digraph_type const&)> pred) const;

   private:
    using time_point = std::chrono::high_resolution_clock::time_point;

    // Can't be static because REPORT_DEFAULT uses this
    template <typename S>
    void report_number_of_congruences(time_point& last_report,
                                      S&          last_count,
                                      uint64_t    count) const {
      if (count - last_count > 2'048) {
        // Avoid calling high_resolution_clock::now too often
        auto now     = std::chrono::high_resolution_clock::now();
        auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
            now - last_report);
        if (elapsed > std::chrono::duration_cast<std::chrono::nanoseconds>(
                std::chrono::seconds(1))) {
          std::swap(now, last_report);
          last_count = count;
          REPORT_DEFAULT("found %llu congruences so far!\n", count);
        }
      }
    }

    // TODO(Sims1) move to cpp file
    class Thief : public const_iterator_base {
     private:
      using PendingDef = typename const_iterator_base::PendingDef;

      std::deque<PendingDef> _pending;
      mutable std::mutex     _mutex;

     public:
      //! No doc
      Thief(Presentation<word_type> const& p,
            Presentation<word_type> const& e,
            Presentation<word_type> const& f,
            size_type                      n)
          : const_iterator_base(p, e, f, n) {}

      // None of the constructors are noexcept because the corresponding
      // constructors for std::vector aren't (until C++17).
      //! No doc
      Thief() = delete;
      //! No doc
      Thief(Thief const&) = delete;
      //! No doc
      Thief(Thief&&) = delete;
      //! No doc
      Thief& operator=(Thief const&) = delete;
      //! No doc
      Thief& operator=(Thief&&) = delete;

      //! No doc
      ~Thief() = default;

      size_t size() const {
        return _pending.size();
      }

      // prefix
      //! No doc
      bool increment(PendingDef const& current) {
        LIBSEMIGROUPS_ASSERT(current.target < current.num_nodes);
        LIBSEMIGROUPS_ASSERT(current.num_nodes <= this->_max_num_classes);

        {
          std::lock_guard<std::mutex> lock(_mutex);
          LIBSEMIGROUPS_ASSERT(this->_felsch_graph.number_of_edges()
                               >= current.num_edges);
          // Backtrack if necessary
          this->_felsch_graph.reduce_number_of_edges_to(current.num_edges);

          // It might be that current.target is a new node, in which case
          // _num_active_nodes includes this new node even before the edge
          // current.source -> current.target is defined.
          this->_num_active_nodes = current.num_nodes;

          LIBSEMIGROUPS_ASSERT(this->_felsch_graph.unsafe_neighbor(
                                   current.source, current.generator)
                               == UNDEFINED);

#ifdef LIBSEMIGROUPS_DEBUG
          for (node_type next = 0; next < current.source; ++next) {
            for (letter_type a = 0; a < this->_num_gens; ++a) {
              LIBSEMIGROUPS_ASSERT(this->_felsch_graph.unsafe_neighbor(next, a)
                                   != UNDEFINED);
            }
          }
          for (letter_type a = 0; a < current.generator; ++a) {
            LIBSEMIGROUPS_ASSERT(
                this->_felsch_graph.unsafe_neighbor(current.source, a)
                != UNDEFINED);
          }

#endif
          size_type start = this->_felsch_graph.number_of_edges();

          this->_felsch_graph.def_edge(
              current.source, current.generator, current.target);
          if (!this->_felsch_graph.process_definitions(start)) {
            return false;
          }
        }

        for (auto it = this->_extra.rules.cbegin();
             it != this->_extra.rules.cend();
             it += 2) {
          if (!this->_felsch_graph.compatible(0, *it, *(it + 1))) {
            return false;
          }
        }

        letter_type a = current.generator + 1;
        for (node_type next = current.source; next < this->_num_active_nodes;
             ++next) {
          for (; a < this->_num_gens; ++a) {
            if (this->_felsch_graph.unsafe_neighbor(next, a) == UNDEFINED) {
              std::lock_guard<std::mutex> lock(_mutex);
              for (node_type b = this->_min_target_node;
                   b < this->_num_active_nodes;
                   ++b) {
                _pending.emplace_back(next,
                                      a,
                                      b,
                                      this->_felsch_graph.number_of_edges(),
                                      this->_num_active_nodes);
              }
              if (this->_num_active_nodes < this->_max_num_classes) {
                _pending.emplace_back(next,
                                      a,
                                      this->_num_active_nodes,
                                      this->_felsch_graph.number_of_edges(),
                                      this->_num_active_nodes + 1);
              }
              return false;
            }
          }
          a = 0;
        }

        LIBSEMIGROUPS_ASSERT(this->_felsch_graph.number_of_edges()
                             == this->_num_active_nodes
                                    * this->_felsch_graph.out_degree());
        // No undefined edges, word graph is complete
        for (auto it = this->_final.rules.cbegin();
             it != this->_final.rules.cend();
             it += 2) {
          for (node_type n = 0; n < this->_num_active_nodes; ++n) {
            if (!this->_felsch_graph.compatible(n, *it, *(it + 1))) {
              return false;
            }
          }
        }
        // REPORT_DEFAULT(detail::to_string(this->_felsch_graph) + "\n");
        return true;
      }

     public:
      // TODO (Sims1) by value, maybe not a good idea?
      void push(PendingDef pd) {
        std::lock_guard<std::mutex> lock(_mutex);
        _pending.push_back(std::move(pd));
      }

      bool empty() const {
        std::lock_guard<std::mutex> lock(_mutex);
        return _pending.empty();
      }

      bool try_pop(PendingDef& pd) {
        std::lock_guard<std::mutex> lock(_mutex);
        if (_pending.empty()) {
          return false;
        }
        pd = std::move(_pending.back());
        _pending.pop_back();
        return true;
      }

      void clone(Thief& that) {
        std::lock_guard<std::mutex> lock(_mutex);
        LIBSEMIGROUPS_ASSERT(_pending.empty());
        const_iterator_base::clone(that);
        // TODO(Sims1) could steal in a different way: maybe interlaced (steal
        // every other item); steal a fixed proportion of every queue
        _pending.insert(_pending.cbegin(),
                        that._pending.begin() + that._pending.size() / 2,
                        that._pending.end());
      }

      bool try_steal(Thief& q) {
        std::lock_guard<std::mutex> lock(_mutex);
        if (_pending.empty()) {
          return false;
        }
        LIBSEMIGROUPS_ASSERT(q.empty());
        q.clone(*this);  // Copy the digraph from this into q
        _pending.erase(_pending.cbegin() + _pending.size() / 2,
                       _pending.cend());
        return true;
      }
    };

    class Den {
     private:
      using PendingDef = typename const_iterator_base::PendingDef;

      std::atomic_bool                    _done;
      std::vector<std::unique_ptr<Thief>> _theives;
      std::vector<std::thread>            _threads;
      size_type                           _num_threads;

      void worker_thread(unsigned                                 my_index,
                         std::function<bool(digraph_type const&)> hook) {
        PendingDef pd;
        while ((pop_from_local_queue(pd, my_index)
                || pop_from_other_thread_queue(pd, my_index))
               && !_done) {
          if (_theives[my_index]->increment(pd)) {
            if (!hook(**_theives[my_index])) {
              _done = true;
              // hook returns false to indicate that we should stop early
              return;
            }
          }
        }
      }

      bool pop_from_local_queue(PendingDef& pd, unsigned my_index) {
        return _theives[my_index]->try_pop(pd);
      }

      bool pop_from_other_thread_queue(PendingDef& pd, unsigned my_index) {
        // report_queue_sizes("BEFORE: ");

        for (size_t i = 0; i < _theives.size() - 1; ++i) {
          unsigned const index = (my_index + i + 1) % _theives.size();
          // TODO(Sims1) could always do something different here, like find
          // the largest queue and steal from that.
          if (_theives[index]->try_steal(*_theives[my_index])) {
            // REPORT_DEFAULT(FORMAT("Q{} stole from Q{}\n", my_index,
            // index)); report_queue_sizes("AFTER: ");
            return pop_from_local_queue(pd, my_index);
          }
        }
        return false;
      }

      void report_queue_sizes(std::string prefix) const {
        if (report::should_report()) {
          std::string msg = prefix + "Queues have sizes ";
          for (auto const& q : _theives) {
            msg += FORMAT("{}, ", q->size());
          }
          msg += "\n";
          REPORT_DEFAULT(msg);
        }
      }

     public:
      Den(Presentation<word_type> const& p,
          Presentation<word_type> const& e,
          Presentation<word_type> const& f,
          size_type                      n,
          size_type                      num_threads)
          : _done(false),  // TODO init other data members
            _num_threads(num_threads) {
        for (size_t i = 0; i < _num_threads; ++i) {
          // TODO(Sims1) use make_unique
          _theives.push_back(std::unique_ptr<Thief>(new Thief(p, e, f, n)));
        }

        if (n > 1) {
          _theives.front()->push({0, 0, 1, 0, 2});
        }
        if (_theives.front()->_min_target_node == 0) {
          _theives.front()->push({0, 0, 0, 0, 1});
        }
      }

      ~Den() = default;

      void run(std::function<bool(digraph_type const&)> hook) {
        detail::JoinThreads joiner(_threads);
        for (size_t i = 0; i < _num_threads; ++i) {
          _threads.push_back(
              std::thread(&Den::worker_thread, this, i, std::ref(hook)));
        }
      }
    };
  };

#ifdef LIBSEMIGROUPS_ENABLE_STATS
  std::ostream& operator<<(std::ostream&                os,
                           typename sims1::Stats const& stats);
#endif  // LIBSEMIGROUPS_ENABLE_STATS

}  // namespace libsemigroups

#include "sims1.tpp"

#endif  // LIBSEMIGROUPS_SIMS1_HPP_
