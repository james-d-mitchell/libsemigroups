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
// TODO(Sims1):
// * improve the reporting from MinimalRepOrc so that it:
//   - states all settings at the start of the run
//   - the number of congruences considered is shown
// * code coverage, iwyu
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

#include "config.hpp"          // for LIBSEMIGROUPS_ENABLE_STATS
#include "constants.hpp"       // for UNDEFINED
#include "debug.hpp"           // for LIBSEMIGROUPS_ASSERT
#include "digraph.hpp"         // for ActionDigraph
#include "exception.hpp"       // for LIBSEMIGROUPS_EXCEPTION
#include "felsch-digraph.hpp"  // for FelschDigraph
#include "froidure-pin.hpp"    // for FroidurePin
#include "present.hpp"         // for Presentation, Presentati...
#include "report.hpp"          // for REPORT_DEFAULT, Reporter
#include "stl.hpp"             // for JoinThreads
#include "timer.hpp"           // for Timer
#include "transf.hpp"          // for Transf
#include "types.hpp"           // for word_type, congruence_kind

namespace libsemigroups {

#ifdef LIBSEMIGROUPS_ENABLE_STATS
  // TODO(Sims1) ensure that this still makes sense in the multi threaded world
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

  // This class allows us to use the same interface for settings for Sims1,
  // RepOrc, and MinimalRepOrc without duplicating the code.
  // TODO(Sims1) doc
  template <typename T>
  class Sims1Settings {
   private:
    size_t _num_threads;
    size_t _report_interval;
    size_t _split_at;

    Sims1Settings(size_t n, size_t r, size_t s)
        : _num_threads(n), _report_interval(r), _split_at(s) {}

   public:
    Sims1Settings() : Sims1Settings(1, 1'000, UNDEFINED) {}

    template <typename S>
    Sims1Settings(Sims1Settings<S> const& s)
        : Sims1Settings(s.number_of_threads(),
                        s.report_interval(),
                        s.split_at()) {}

    // TODO(Sims1) doc
    T& split_at(size_t val) noexcept {
      _split_at = val;
      return static_cast<T&>(*this);
    }

    // TODO(Sims1) doc
    size_t split_at() const noexcept {
      return _split_at;
    }

    // TODO(Sims1) doc
    T& number_of_threads(size_t val) noexcept {
      _num_threads = val;
      return static_cast<T&>(*this);
    }

    // TODO(Sims1) doc
    size_t number_of_threads() const noexcept {
      return _num_threads;
    }

    // TODO(Sims1) doc
    T& report_interval(size_t val) noexcept {
      _report_interval = val;
      return static_cast<T&>(*this);
    }
    // TODO(Sims1) doc
    size_t report_interval() const noexcept {
      return _report_interval;
    }
  };

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
  // TODO(v3) remove the template T here
  template <typename T>
  class Sims1 : public Sims1Settings<Sims1<T>> {
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

   public:
    // TODO(Sims1) doc
    template <typename S>
    Sims1(congruence_kind                ck,
          Presentation<word_type> const& p,
          Presentation<word_type> const& e,
          Sims1Settings<S> const&        s);

    // TODO(Sims1) doc
    template <typename S>
    Sims1(congruence_kind                ck,
          Presentation<word_type> const& p,
          Sims1Settings<S> const&        s);

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

    //! Only apply certain relations when an otherwise compatible
    //! ActionDigraph is found.
    //!
    //! This function splits the relations in the underlying presentation into
    //! two parts: those before the relation with index \p val and those
    //! after. The order of the relations is the same as the order in the
    //! constructing presentation. In some instances if the relations after
    //! index \p val are "long" and those before are "short", then this can
    //! improve the performance. It can also make the performance worse, and
    //! should be used with care.
    //!
    //! \param val the relation to split at
    //!
    //! \returns (None)
    //!
    //! \throws LibsemigroupsException if \p val is out of bounds.
    // TODO(Sims1) some tests for this.
    Sims1& split_at(size_type val);

   private:
    void perform_split();

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
    // This class collects some common aspects of the const_iterator and Thief
    // nested classes.
    class IteratorAndThiefBase {
      friend class Den;

     public:
      using const_reference =
          typename std::vector<digraph_type>::const_reference;

      using const_pointer = typename std::vector<digraph_type>::const_pointer;

     protected:
      Presentation<word_type>             _extra;
      FelschDigraph<word_type, node_type> _felsch_graph;
      Presentation<word_type>             _final;
      size_type                           _max_num_classes;
      size_type                           _min_target_node;
#ifdef LIBSEMIGROUPS_ENABLE_STATS
      Sims1Stats _stats;
#endif

     public:
      //! No doc
      IteratorAndThiefBase(Presentation<word_type> const& p,
                           Presentation<word_type> const& e,
                           Presentation<word_type> const& f,
                           size_type                      n);

      // None of the constructors are noexcept because the corresponding
      // constructors for Presentation aren't (until C++17).

      //! No doc
      IteratorAndThiefBase() = delete;
      //! No doc
      IteratorAndThiefBase(IteratorAndThiefBase const&) = default;
      //! No doc
      IteratorAndThiefBase(IteratorAndThiefBase&&) = default;
      //! No doc
      IteratorAndThiefBase& operator=(IteratorAndThiefBase const&) = default;
      //! No doc
      IteratorAndThiefBase& operator=(IteratorAndThiefBase&&) = default;

      //! No doc
      virtual ~IteratorAndThiefBase() = default;

      //! No doc
      bool operator==(IteratorAndThiefBase const& that) const noexcept {
        return _felsch_graph == that._felsch_graph;
      }

      //! No doc
      bool operator!=(IteratorAndThiefBase const& that) const noexcept {
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
      void swap(IteratorAndThiefBase& that) noexcept {
        std::swap(_extra, that._extra);
        std::swap(_felsch_graph, that._felsch_graph);
        std::swap(_max_num_classes, that._max_num_classes);
        std::swap(_min_target_node, that._min_target_node);
      }

      // We could use the copy constructor, but there's no point in copying
      // anything except the FelschDigraph and so we only copy that.
      void copy_felsch_graph(IteratorAndThiefBase const& that) {
        _felsch_graph = that._felsch_graph;
      }

      size_type min_target_node() const noexcept {
        return _min_target_node;
      }
    };

   public:
    //! No doc
    class const_iterator : public IteratorAndThiefBase {
     public:
      //! No doc
      using const_pointer = typename IteratorAndThiefBase::const_pointer;
      //! No doc
      using const_reference = typename IteratorAndThiefBase::const_reference;

      //! No doc
      using size_type = typename std::vector<digraph_type>::size_type;
      //! No doc
      using difference_type =
          typename std::vector<digraph_type>::difference_type;
      //! No doc
      using pointer = typename std::vector<digraph_type>::pointer;
      //! No doc
      using reference = typename std::vector<digraph_type>::reference;
      //! No doc
      using value_type = digraph_type;
      //! No doc
      using iterator_category = std::forward_iterator_tag;

     private:
      std::vector<PendingDef> _pending;
#ifdef LIBSEMIGROUPS_ENABLE_STATS
      Sims1Stats _stats;
#endif

     public:
      //! No doc
      const_iterator(Presentation<word_type> const& p,
                     Presentation<word_type> const& e,
                     Presentation<word_type> const& f,
                     size_type                      n);

      //! No doc
      using IteratorAndThiefBase::IteratorAndThiefBase;

      //! No doc
      ~const_iterator() = default;

      // prefix
      //! No doc
      const_iterator const& operator++();

      // postfix
      //! No doc
      const_iterator operator++(int) {
        const_iterator copy(*this);
        ++(*this);
        return copy;
      }

      //! No doc
      void swap(const_iterator& that) noexcept {
        IteratorAndThiefBase::swap(that);
        std::swap(_pending, that._pending);
      }

#ifdef LIBSEMIGROUPS_ENABLE_STATS
      Sims1Stats const& stats() const noexcept;

     private:
      bool try_define(PendingDef const&);
      void stats_update(size_type);
#endif
    };  // class const_iterator

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
    //! of the digraph is isomorphic to the action of \f$M\f$ on the classes
    //! of a right congruence.
    //!
    //! If the input is a semigroup presentation for a semigroup $\fS\f$, then
    //! the ActionDigraph has \p n + 1 nodes, and the right action of \f$S\f$
    //! on the nodes \f$\{1, \ldots, n\}\f$ of the ActionDigraph is isomorphic
    //! to the action of \f$S\f$ on the classes of a right congruence. It'd
    //! probably be better in this case if node \f$0\f$ was not included in the
    //! output ActionDigraph, but it is required in the implementation of the
    //! low-index congruence algorithm, and to avoid unnecessary copies, we've
    //! left it in for the time being.
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
    //! incrementing \c ++it the returned  iterator \c it significantly
    //! cheaper than postfix incrementing \c it++.
    //!
    //! \sa
    //! \ref cend
    // TODO(Sims1) it'd be good to remove node 0 to avoid confusion.
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
    //! incrementing \c ++it the returned  iterator \c it significantly
    //! cheaper than postfix incrementing \c it++.
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
    //! exists only to provide some feedback on the progress of the
    //! computation if it runs for more than 1 second.
    //!
    //! TODO(Sims1): update doc for multi threading
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
    //! TODO(Sims1): doc
    void for_each(size_type                                n,
                  std::function<void(digraph_type const&)> pred) const;

    // Apply the function pred to every one-sided congruence with at
    // most n classes, until pred returns true
    //! TODO(Sims1): doc
    digraph_type find_if(size_type                                n,
                         std::function<bool(digraph_type const&)> pred) const;

   private:
    using time_point = std::chrono::high_resolution_clock::time_point;

    template <typename S>
    void report_number_of_congruences(time_point&   last_report,
                                      S&            last_count,
                                      uint64_t      count,
                                      detail::Timer t) const;
    class Thief;
    class Den;
  };

#ifdef LIBSEMIGROUPS_ENABLE_STATS
  std::ostream& operator<<(std::ostream& os, Sims1Stats const& stats);
#endif  // LIBSEMIGROUPS_ENABLE_STATS

  // TODO(Sims1) doc
  class RepOrc : public Sims1Settings<RepOrc> {
   private:
    size_t                         _min;
    size_t                         _max;
    Presentation<word_type> const& _presentation;
    size_t                         _size;

   public:
    explicit RepOrc(Presentation<word_type> const& p)
        : RepOrc(p, Sims1Settings<RepOrc>()) {}

    template <typename S>
    RepOrc(Presentation<word_type> const& p, Sims1Settings<S> const& s)
        : Sims1Settings<RepOrc>(s), _min(), _max(), _presentation(p), _size() {}

    RepOrc& min_nodes(size_t val) noexcept {
      _min = val;
      return *this;
    }

    size_t min_nodes() const noexcept {
      return _min;
    }

    RepOrc& max_nodes(size_t val) noexcept {
      _max = val;
      return *this;
    }

    size_t max_nodes() const noexcept {
      return _max;
    }

    RepOrc& target_size(size_t val) noexcept {
      _size = val;
      return *this;
    }

    size_t target_size() const noexcept {
      return _size;
    }

    template <typename T = uint32_t>
    ActionDigraph<T> digraph() const;
  };

  // TODO(Sims1) doc
  class MinimalRepOrc : public Sims1Settings<MinimalRepOrc> {
   private:
    // We require a copy of the presentation, rather than a reference otherwise
    // the non-word_type Presentation ctor below doesn't work.
    Presentation<word_type> _presentation;
    size_t                  _size;

   public:
    MinimalRepOrc(Presentation<word_type> const& p)
        : _presentation(p), _size() {}

    template <typename P>
    MinimalRepOrc(P const& p)
        : MinimalRepOrc(make<Presentation<word_type>>(p)) {
      static_assert(std::is_base_of<PresentationBase, P>::value,
                    "the template parameter P must be derived from "
                    "PresentationBase");
    }

    MinimalRepOrc& target_size(size_t val) noexcept {
      _size = val;
      return *this;
    }

    size_t target_size() const noexcept {
      return _size;
    }

    // An alternative to the approach used below would be to do a sort of
    // binary search for a minimal representation. It seems that in most
    // examples that I've tried, this actually finds the minimal rep close to
    // the start of the search. The binary search approach would only really be
    // useful if the rep found at the start of the search was much larger than
    // the minimal one, and that the minimal one would not be found until late
    // in the search through all the reps with [1, best rep so far). It seems
    // that in most examples, binary search will involve checking many of the
    // same graphs repeatedly, i.e. if we check [1, size = 1000) find a rep on
    // 57 points, then check [1, 57 / 2) find nothing, then check [57/2, 57)
    // and find nothing, then the search through [57/2, 57) actually iterates
    // through all the digraphs with [1, 57 / 2) again (just doesn't construct
    // a FroidurePin object for these). So, it seems to be best to just search
    // through the digraphs with [1, 57) nodes once.
    template <typename T = uint32_t>
    ActionDigraph<T> digraph();
  };

}  // namespace libsemigroups

#include "sims1.tpp"

#endif  // LIBSEMIGROUPS_SIMS1_HPP_
