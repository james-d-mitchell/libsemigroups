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
// * implement joins (HopcroftKarp), meets (not sure), containment (find join
//   and check equality)?
// * generating pairs for congruences defined by "action digraph"?
// * is 2-sided congruence method. One approach would be to compute the kernel
//   of the associated homomorphism, which is the largest 2-sided congruence
//   contained in the right congruence. Not sure if this is a good approach.
//
// Notes:
// 1. In 2022, when first writing this file, JDM tried templating the word_type
//    used by the presentations in Sims1 (so that we could use StaticVector1
//    for example, using smaller integer types for letters, and the stack to
//    hold the words rather than the heap), but this didn't seem to give any
//    performance improvement, and so I backed out the changes.

#ifndef LIBSEMIGROUPS_SIMS1_HPP_
#define LIBSEMIGROUPS_SIMS1_HPP_

#include <atomic>       // for atomic_bool
#include <cstddef>      // for size_t
#include <cstdint>      // for uint64_t, uint32_t
#include <iostream>     // for string, ostream
#include <string>       // for operator+, basic_string
#include <thread>       // for thread, yield
#include <type_traits>  // for is_base_of
#include <vector>       // for vector

#include <fmt/chrono.h>  // for group_digits

#include "config.hpp"          // for LIBSEMIGROUPS_ENABLE_STATS
#include "constants.hpp"       // for UNDEFINED
#include "debug.hpp"           // for LIBSEMIGROUPS_ASSERT
#include "digraph.hpp"         // for ActionDigraph
#include "exception.hpp"       // for LIBSEMIGROUPS_EXCEPTION
#include "felsch-digraph.hpp"  // for FelschDigraph
#include "froidure-pin.hpp"    // for FroidurePin
#include "present.hpp"         // for Presentation, Presentati...
#include "report.hpp"          // for REPORT_DEFAULT, Reporter
#include "timer.hpp"           // for Timer
#include "transf.hpp"          // for Transf
#include "types.hpp"           // for word_type, congruence_kind

namespace libsemigroups {

#ifdef LIBSEMIGROUPS_ENABLE_STATS
  // This isn't inside Sims1 because it doesn't depend on the template args at
  // all.
  struct Sims1Stats {
    double   mean_depth     = 0;
    uint64_t max_depth      = 0;
    uint64_t max_pending    = 0;
    uint64_t num_nodes      = 0;
    uint64_t num_good_nodes = 0;
    uint64_t depth          = 0;
  };
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
    size_type               _num_threads;
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

    size_type number_of_threads() const noexcept {
      return _num_threads;
    }

    // TODO(Sims1): noexcept?
    Sims1& number_of_threads(size_t val) {
      _num_threads = val;
      return *this;
    }

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
      size_type _num_gens;  // TODO(Sims1) This can be removed it's just
                            // _felsch_graph.out_degree()

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
        return _felsch_graph == that._felsch_graph;
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
        std::swap(_num_gens, that._num_gens);
      }

      void clone(const_iterator_base const& that) {
        _felsch_graph = that._felsch_graph;
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
      Sims1Stats const& stats() const noexcept;

     private:
      Sims1Stats _stats;
      void       stats_update(size_type);

#endif

     public:
      const_iterator(Presentation<word_type> const& p,
                     Presentation<word_type> const& e,
                     Presentation<word_type> const& f,
                     size_type                      n)
          : const_iterator_base(p, e, f, n) {
        if (this->_felsch_graph.number_of_active_nodes() == 0) {
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
    //! The meaning of the ActionDigraph pointed at by Sims1 iterators depends
    //! on whether the input is a monoid presentation (i.e.
    //! Presentation::contains_empty_word() returns \c true) or a semigroup
    //! presentation. If the input is a monoid presentation for a monoid
    //! \f$M\f$, then the ActionDigraph pointed to by an iterator of this type
    //! has precisely \p n nodes, and the right action of \f$M\f$ on the nodes
    //! of the digraph is isomorphic to the action of \f$M\f$ on the classes of
    //! a right congruence.
    //!
    //! If the input is a semigroup presentation for a semigroup $\fS\f$, then
    //! the ActionDigraph has \p n + 1 nodes, and the right action of \f$S\f$
    //! on the nodes \f$\{1, \ldots, n\}\f$ of the ActionDigraph is isomorphic
    //! to the action of \f$S\f$ on the classes of a right congruence. It'd
    //! probably be better if node \f$0\f$ was not included in the
    //! output ActionDigraph, but it is required in the implementation of the
    //! low-index congruence algorithm, and to avoid unnecessary copies, we've
    //! left it in for the time being.
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

    // If we don't include the extra node 0 when input is a semigroup
    // presentation, then we don't get the correct number of congruences in
    // test case 036, returns 8 instead of 6, so should figure out what's going
    // on there. TOOD(Sims1)
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
    //!
    //! \returns A value of type \c uint64_t.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    // TODO(v3): this should be in the sims1 helper namespace
    uint64_t number_of_congruences(size_type n) const;

    // Apply the function pred to every one-sided congruence with at
    // most n classes
    void for_each(size_type                                n,
                  std::function<void(digraph_type const&)> pred) const;

    // Apply the function pred to every one-sided congruence with at
    // most n classes, until pred returns true
    digraph_type find_if(size_type                                n,
                         std::function<bool(digraph_type const&)> pred) const;

   private:
    using time_point = std::chrono::high_resolution_clock::time_point;

    // Can't be static because REPORT_DEFAULT uses this
    // TODO(Sims1) move to tpp file
    template <typename S>
    void report_number_of_congruences(time_point&   last_report,
                                      S&            last_count,
                                      uint64_t      count,
                                      detail::Timer t) const {
      // TODO(Sims1) add 2'048 as a setting
      // if (count - last_count > 2'048) {
      // Avoid calling high_resolution_clock::now too often
      auto now     = std::chrono::high_resolution_clock::now();
      auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
          now - last_report);
      if (elapsed > std::chrono::duration_cast<std::chrono::nanoseconds>(
              std::chrono::seconds(1))) {
        std::swap(now, last_report);
        last_count = count;
        using float_seconds
            = std::chrono::duration<float, std::chrono::seconds::period>;
        auto seconds = std::chrono::duration_cast<float_seconds>(t.elapsed());
        REPORT_DEFAULT(FORMAT("found {} congruences in {}!\n", count, seconds));
      }
      //}
    }

    // TODO(Sims1) move to cpp file
    class Thief : public const_iterator_base {
     private:
      using PendingDef = typename const_iterator_base::PendingDef;

      std::vector<PendingDef> _pending;
      mutable std::mutex      _mutex;
      uint64_t&               _total_pending;

     public:
      //! No doc
      Thief(Presentation<word_type> const& p,
            Presentation<word_type> const& e,
            Presentation<word_type> const& f,
            size_type                      n,
            uint64_t&                      total_pending)
          : const_iterator_base(p, e, f, n), _total_pending(total_pending) {}

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
          // _felsch_graph.number_of_active_nodes() includes this new node
          // even before the edge current.source -> current.target is defined.
          this->_felsch_graph.number_of_active_nodes(current.num_nodes);

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

        letter_type     a = current.generator + 1;
        size_type const M = this->_felsch_graph.number_of_active_nodes();
        size_type const N = this->_felsch_graph.number_of_edges();
        for (node_type next = current.source; next < M; ++next) {
          for (; a < this->_num_gens; ++a) {
            if (this->_felsch_graph.unsafe_neighbor(next, a) == UNDEFINED) {
              std::lock_guard<std::mutex> lock(_mutex);
              if (M < this->_max_num_classes) {
                _total_pending++;
                _pending.emplace_back(next, a, M, N, M + 1);
              }
              for (node_type b = M; b-- > this->_min_target_node;) {
                _total_pending++;
                _pending.emplace_back(next, a, b, N, M);
              }
              return false;
            }
          }
          a = 0;
        }

        LIBSEMIGROUPS_ASSERT(N == M * this->_num_gens);

        // No undefined edges, word graph is complete
        for (auto it = this->_final.rules.cbegin();
             it != this->_final.rules.cend();
             it += 2) {
          for (node_type m = 0; m < M; ++m) {
            if (!this->_felsch_graph.compatible(m, *it, *(it + 1))) {
              return false;
            }
          }
        }
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

        for (size_t i = 0; i < that._pending.size(); i += 2) {
          _pending.push_back(std::move(that._pending[i]));
          that._pending[i / 2] = std::move(that._pending[i + 1]);
        }

        // _pending.insert(_pending.cbegin(),
        //                 that._pending.begin() + that._pending.size() / 2,
        //                 that._pending.end());
        // that._pending.cbegin(),
        // that._pending.cbegin() + that._pending.size() / 2);
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
        // _pending.erase(_pending.cbegin(),
        //               _pending.cbegin() + _pending.size() / 2);
        return true;
      }
    };

    class Den {
     private:
      using PendingDef = typename const_iterator_base::PendingDef;

      std::atomic_bool                    _done;
      std::vector<std::unique_ptr<Thief>> _theives;
      std::vector<std::thread>            _threads;
      std::vector<uint64_t>               _total_pending;
      size_type                           _num_threads;
      digraph_type                        _result;
      std::mutex                          _mtx;

      void worker_thread(unsigned                                 my_index,
                         std::function<bool(digraph_type const&)> hook) {
        PendingDef pd;
        for (auto i = 0; i < 128; ++i) {
          while ((pop_from_local_queue(pd, my_index)
                  || pop_from_other_thread_queue(pd, my_index))
                 && !_done) {
            if (_theives[my_index]->increment(pd)) {
              if (hook(**_theives[my_index])) {
                // hook returns true to indicate that we should stop early
                std::lock_guard<std::mutex> lock(_mtx);
                if (!_done) {
                  _done   = true;
                  _result = **_theives[my_index];
                }
                return;
              }
            }
          }
          std::this_thread::yield();
          // It's possible to reach here before all of the work is done, because
          // by coincidence there's nothing in the local queue and nothing in
          // any other queue either, this sometimes leads to threads shutting
          // down earlier than desirable. On the other hand, maybe this is a
          // desirable.
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
            // REPORT_DEFAULT(FORMAT("Q{} stole from Q{}\n", my_index, index));
            // report_queue_sizes("AFTER: ");
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
            _total_pending(num_threads, 0),
            _num_threads(num_threads) {
        for (size_t i = 0; i < _num_threads; ++i) {
          // TODO(Sims1) use make_unique
          _theives.push_back(
              std::unique_ptr<Thief>(new Thief(p, e, f, n, _total_pending[i])));
        }

        if (n > 1) {
          _total_pending[0]++;
          _theives.front()->push({0, 0, 1, 0, 2});
        }
        if (_theives.front()->_min_target_node == 0) {
          _total_pending[0]++;
          _theives.front()->push({0, 0, 0, 0, 1});
        }
      }

      ~Den() = default;

      digraph_type const& digraph() const {
        // REPORT_DEFAULT(FORMAT("number of nodes created in each thread {}\n",
        //                      detail::to_string(_total_pending)));
        REPORT_DEFAULT(FORMAT(
            "total number of nodes in search tree was {}\n",
            fmt::group_digits(std::accumulate(
                _total_pending.cbegin(), _total_pending.cend(), uint64_t(0)))));
        return _result;
      }

      void run(std::function<bool(digraph_type const&)> hook) {
        detail::JoinThreads joiner(_threads);
        try {
          for (size_t i = 0; i < _num_threads; ++i) {
            _threads.push_back(
                std::thread(&Den::worker_thread, this, i, std::ref(hook)));
          }
        } catch (...) {
          _done = true;
          throw;
        }
      }
    };
  };

#ifdef LIBSEMIGROUPS_ENABLE_STATS
  std::ostream& operator<<(std::ostream& os, Sims1Stats const& stats);
#endif  // LIBSEMIGROUPS_ENABLE_STATS

  // TODO(Sims1) delete
  // template <typename T, typename W>
  // ActionDigraph<T>
  // cyclic_rep(Presentation<W> const& p, size_t min, size_t max, size_t size)
  // {
  //  // TODO check that min != 0
  //  std::cout << "Trying to find a representation with degree in [" << min
  //            << ", " << max << "]:" << std::endl;
  //  Sims1<T> C(congruence_kind::right, p);
  //  using node_type = typename Sims1<T>::digraph_type::node_type;

  //  auto   it    = C.cbegin(max);
  //  size_t count = 0;

  //  for (; it != C.cend(max); ++it) {
  //    std::cout << "\rat " << ++count << std::flush;
  //    if (it->number_of_active_nodes() >= min
  //        && it->number_of_active_nodes() <= max) {
  //      auto S = make<FroidurePin<Transf<0, node_type>>>(
  //          *it, it->number_of_active_nodes());
  //      if (p.contains_empty_word()) {
  //        auto one = S.generator(0).identity();
  //        if (!S.contains(one)) {
  //          S.add_generator(one);
  //        }
  //      }
  //      if (S.size() == size) {
  //        break;
  //      }
  //    }
  //  }

  // TODO(Sims1) is this correct?
  // ActionDigraph<T> result(*it);
  // if (result.number_of_active_nodes() == 0) {
  //   result.restrict(0);
  //   result.number_of_active_nodes(0);
  // } else {
  //   result.restrict(result.number_of_active_nodes());
  // }

  // std::cout << "\r* " << count << " congruences analysed, ";
  // if (result.number_of_nodes() == 0) {
  //   std::cout << "no faithful representations found!";
  // } else {
  //   std::cout << "faithful representations of degree "
  //             << result.number_of_nodes() << " found!";
  // }
  // std::cout << std::endl;
  // return result;
  // }

  class RepOrc {
   private:
    size_t                         _min;
    size_t                         _max;
    size_t                         _num_threads;
    Presentation<word_type> const& _presentation;
    size_t                         _size;

   public:
    explicit RepOrc(Presentation<word_type> const& p)
        : _min(), _max(), _num_threads(1), _presentation(p), _size() {}
    // TODO(Sims1) the other ctors
    // TODO(Sims1) another constructor for other types of Presentation

    RepOrc& min_nodes(size_t val) {
      _min = val;
      return *this;
    }

    RepOrc& max_nodes(size_t val) {
      _max = (_presentation.contains_empty_word() ? val : val + 1);
      return *this;
    }

    RepOrc& target_size(size_t val) {
      _size = val;
      return *this;
    }

    RepOrc& number_of_threads(size_t val) {
      _num_threads = val;
      return *this;
    }

    template <typename T = uint32_t>
    ActionDigraph<T> digraph() const {
      using digraph_type = typename Sims1<T>::digraph_type;
      using node_type    = typename digraph_type::node_type;

      auto hook = [&](digraph_type const& x) {
        if (x.number_of_active_nodes() >= _min
            && x.number_of_active_nodes() <= _max) {
          // TODO(Sims1) the <= _max shouldn't be necessary
          auto first = (_presentation.contains_empty_word() ? 0 : 1);
          auto S     = make<FroidurePin<Transf<0, node_type>>>(
              x, first, x.number_of_active_nodes());
          if (_presentation.contains_empty_word()) {
            auto one = S.generator(0).identity();
            if (!S.contains(one)) {
              S.add_generator(one);
            }
          }
          if (S.size() == _size) {
            return true;
          }
        }
        return false;
      };

      Sims1<T> C(congruence_kind::right, _presentation);
      auto     result = C.number_of_threads(_num_threads).find_if(_max, hook);
      if (result.number_of_active_nodes() == 0) {
        result.restrict(0);
      } else {
        if (_presentation.contains_empty_word()) {
          result.restrict(result.number_of_active_nodes());
        } else {
          result.induced_subdigraph(1, result.number_of_active_nodes());
          std::for_each(result.begin(), result.end(), [](auto& val) { --val; });
          result.number_of_active_nodes(result.number_of_active_nodes() - 1);
        }
      }
      return result;
    }
  };

  // TODO(Sims1): check that the returned representation is strictly cyclic,
  // when the argument is a semigroup
  class MinimalRepOrc {
   private:
    size_t _num_threads;
    // TODO(later): we were using a reference to the presentation here, but
    // then the non-word_type Presentation ctor below doesn't work.
    Presentation<word_type> _presentation;
    size_t                  _size;

   public:
    MinimalRepOrc(Presentation<word_type> const& p)
        : _num_threads(1), _presentation(p), _size() {}

    template <typename P>
    MinimalRepOrc(P const& p)
        : MinimalRepOrc(make<Presentation<word_type>>(p)) {
      static_assert(std::is_base_of<PresentationBase, P>::value,
                    "the template parameter P must be derived from "
                    "PresentationBase");
    }

    MinimalRepOrc& target_size(size_t val) {
      _size = val;
      return *this;
    }

    MinimalRepOrc& number_of_threads(size_t val) {
      _num_threads = val;
      return *this;
    }

    template <typename T = uint32_t>
    ActionDigraph<T> digraph() {
      auto cr = RepOrc(_presentation).number_of_threads(_num_threads);

      size_t hi = (_presentation.contains_empty_word() ? _size : _size + 1);
      REPORT_DEFAULT(
          "trying to find faithful cyclic rep. on [1, %llu) points\n", hi + 1);
      auto best = cr.min_nodes(1).max_nodes(hi).target_size(_size).digraph();

      if (best.number_of_nodes() == 0) {
        REPORT_DEFAULT("no faithful cyclic rep. on [1, %llu) points found\n",
                       hi + 1);
        // No faithful representation on up to <size> points, or trivial
        return best;
      } else if (best.number_of_nodes() == 1) {
        REPORT_DEFAULT("found a faithful cyclic rep. on 1 point\n");
        return best;
      }
      hi = best.number_of_nodes();
      REPORT_DEFAULT("found a faithful cyclic rep. on %llu points\n", hi);

      REPORT_DEFAULT(
          "trying to find faithful cyclic rep. on [1, %llu) points\n", hi);
      ActionDigraph<T> next = std::move(cr.max_nodes(hi - 1).digraph());
      while (next.number_of_nodes() != 0) {
        hi = next.number_of_nodes();
        REPORT_DEFAULT("found a faithful cyclic rep. on %llu points\n", hi);
        best = std::move(next);
        REPORT_DEFAULT(
            "trying to find faithful cyclic rep. on [1, %llu) points\n", hi);
        next = std::move(cr.max_nodes(hi - 1).digraph());
      }
      REPORT_DEFAULT("no faithful cyclic rep. on [1, %llu) points found\n", hi);
      return best;
    }
  };

  // The following is an alternative implementation that does a sort of
  // binary search, this might be useful if there are examples where the
  // minimal degree representation is much smaller than the initial
  // representation found.
  /*template <typename T, typename W>
  ActionDigraph<T> minimal_representation(Presentation<W> const& p,
                                          size_t                 size) {
    auto             best = representation<T>(p, 1, size, size);
    ActionDigraph<T> next;
    size_t           hi = best.number_of_nodes(

    if (hi == 0) {
      // No faithful representation on up to <size> points
      return best;
    }

    size_t lo = representation<T>(p, 1, 1, size).number_of_nodes();

    // TODO handle the case when there is a 1 degree rep
    if (lo == 0) {
      lo = 1;
    }

    auto mid = (hi + lo) / 2;
    mid      = (mid == 1 ? 2 : mid);
    std::cout << "hi = " << hi << ", lo = " << lo << ", mid = " << mid
              << std::endl;
    while (lo != mid) {
      next = std::move(representation<T>(p, lo + 1, mid, size));
      if (next.number_of_nodes() == 0) {
        lo = mid;
      } else if (next.number_of_nodes() < hi) {
        hi   = next.number_of_nodes();
        best = std::move(next);
      }
      mid = (hi + lo) / 2;
      std::cout << "hi = " << hi << ", lo = " << lo << ", mid = " << mid
                << std::endl;
    }
    return best;
  }*/

}  // namespace libsemigroups

#include "sims1.tpp"

#endif  // LIBSEMIGROUPS_SIMS1_HPP_
