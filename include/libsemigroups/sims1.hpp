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
// * be useful to have output when no congruences are found too (i.e. in
//   Heineken group example).
// * add presentation::longest_rule, shortest_rule, number of rules less than a
//   given size.
// * fix sorting in presentation (so that is uses both sides of the rules)
// * figure out how to suppress FroidurePin reporting
// * improve the reporting from MinimalRepOrc so that it:
//   - states all settings at the start of the run
//   - the number of congruences considered is shown
//  * check for the case that we've constructed a Sims1 but haven't added any
//    relations or anything
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
#include "make-present.hpp"    // for make
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
    uint64_t max_pending   = 0;
    uint64_t total_pending = 0;

    Sims1Stats& operator+=(Sims1Stats const& that) {
      max_pending = std::max(max_pending, that.max_pending);
      total_pending += that.total_pending;
      return *this;
    }
  };
#endif

  // This class allows us to use the same interface for settings for Sims1,
  // RepOrc, and MinimalRepOrc without duplicating the code.
  // TODO(Sims1) doc
  template <typename T>
  class Sims1Settings {
   private:
    Presentation<word_type> _longs;
    size_t                  _num_threads;
    size_t                  _report_interval;
    Presentation<word_type> _shorts;
#ifdef LIBSEMIGROUPS_ENABLE_STATS
    mutable Sims1Stats _stats;

#endif

   public:
    Sims1Settings()
        // TODO(Sims1) _stats only if LIBSEMIGROUPS_ENABLE_STATS
        : _longs(), _num_threads(), _report_interval(), _shorts(), _stats() {
      number_of_threads(1);
      report_interval(999);
    }

    template <typename S>
    Sims1Settings(Sims1Settings<S> const& that)
        : _longs(that.long_rules()),
          _num_threads(that.number_of_threads()),
          _report_interval(that.report_interval()),
          _shorts(that.short_rules()),
          _stats(that.stats()) {}

    Sims1Settings const& settings() {
      return *this;
    }

    // Copy the settings from that into this, used in builder in derived
    // classes.
    T& settings(Sims1Settings const& that) {
      *this = that;
      return static_cast<T&>(*this);
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

    T& short_rules(Presentation<word_type> const& p) {
      validate_presentation(p, _longs);
      _shorts = p;
      return static_cast<T&>(*this);
    }

    template <typename P>
    T& short_rules(P const& p) {
      static_assert(std::is_base_of<PresentationBase, P>::value,
                    "the template parameter P must be derived from "
                    "PresentationBase");
      return short_rules(make<Presentation<word_type>>(p));
    }

    Presentation<word_type> const& short_rules() const noexcept {
      return _shorts;
    }

    T& long_rules(Presentation<word_type> const& p) {
      validate_presentation(p, _shorts);
      _longs = p;
      return static_cast<T&>(*this);
    }

    template <typename P>
    T& long_rules(P const& p) {
      static_assert(std::is_base_of<PresentationBase, P>::value,
                    "the template parameter P must be derived from "
                    "PresentationBase");
      return long_rules(make<Presentation<word_type>>(p));
    }

    Presentation<word_type> const& long_rules() const noexcept {
      return _longs;
    }

    Sims1Stats const& stats() const noexcept {
      return _stats;
    }

    T const& stats(Sims1Stats const& stts) const {
      _stats = std::move(stts);
      return static_cast<T const&>(*this);
    }

    T& large_rule_length(size_t val) {
      auto partition = [&val](auto first, auto last) {
        for (; first != last; first += 2) {
          if (first->size() + (first + 1)->size() >= val) {
            break;
          }
        }
        if (first == last) {
          return first;
        }

        for (auto lhs = first + 2; lhs < last; lhs += 2) {
          auto rhs = lhs + 1;
          if (lhs->size() + rhs->size() < val) {
            std::iter_swap(lhs, first++);
            std::iter_swap(rhs, first++);
          }
        }
        return first;
      };

      // points at the lhs of the first rule of length at least val
      auto its = partition(_shorts.rules.begin(), _shorts.rules.end());
      _longs.rules.insert(_longs.rules.end(),
                          std::make_move_iterator(its),
                          std::make_move_iterator(_shorts.rules.end()));
      auto lastl = _longs.rules.end() - std::distance(its, _shorts.rules.end());
      _shorts.rules.erase(its, _shorts.rules.end());

      // points at the lhs of the first rule of length at least val
      auto itl = partition(_longs.rules.begin(), lastl);
      _shorts.rules.insert(_shorts.rules.end(),
                           std::make_move_iterator(_longs.rules.begin()),
                           std::make_move_iterator(itl));
      _longs.rules.erase(_longs.rules.begin(), itl);
      return static_cast<T&>(*this);
    }

   protected:
    void validate_presentation(Presentation<word_type> const& arg,
                               Presentation<word_type> const& existing) {
      if (!arg.alphabet().empty() && !existing.alphabet().empty()
          && arg.alphabet() != existing.alphabet()) {
        LIBSEMIGROUPS_EXCEPTION(
            "the argument (a presentation) is not defined over "
            "the correct alphabet, expected alphabet %s got %s",
            detail::to_string(existing.alphabet()).c_str(),
            detail::to_string(arg.alphabet()).c_str());
      }
      arg.validate();
    }
  };

  //! Defined in ``sims1.hpp``.
  //!
  //! On this page we describe the functionality relating to the small index
  //! congruence algorithm. The algorithm implemented by this class template
  //! is essentially the low index subgroup algorithm for finitely presented
  //! groups described in Section 5.6 of [Computation with Finitely Presented
  //! Groups](https://doi.org/10.1017/CBO9780511574702) by C. Sims. The low
  //! index subgroups algorithm was adapted for semigroups and monoids by J.
  //! D. Mitchell and M. Tsalakou.
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
    congruence_kind         _kind;

    using Sims1Settings<Sims1>::validate_presentation;

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
    Sims1(congruence_kind ck);

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

    using Sims1Settings<Sims1>::short_rules;
    using Sims1Settings<Sims1>::long_rules;
    using Sims1Settings<Sims1>::number_of_threads;
    using Sims1Settings<Sims1>::report_interval;
    using Sims1Settings<Sims1>::stats;

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
    // TODO(Sims1) reuse documentation above

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

    // TODO(Sims1) to tpp
    template <typename P>
    Sims1& extra(P const& p) {
      static_assert(std::is_base_of<PresentationBase, P>::value,
                    "the template parameter P must be derived from "
                    "PresentationBase");
      return extra(make<Presentation<word_type>>(p));
    }

    // TODO(Sims1) to tpp
    Sims1& extra(Presentation<word_type> const& p) {
      auto normal_p = make<Presentation<word_type>>(p);
      validate_presentation(normal_p, short_rules());
      validate_presentation(normal_p, long_rules());
      if (_kind == congruence_kind::left) {
        presentation::reverse(normal_p);
      }
      _extra = normal_p;
      return *this;
    }

    // TODO(Sims1) to tpp
    Sims1& short_rules(Presentation<word_type> const& p) {
      // We call make in the next two lines to ensure that the generators of
      // the presentation are {0, ..., n - 1} where n is the size of the
      // alphabet.
      auto normal_p = make<Presentation<word_type>>(p);
      validate_presentation(normal_p, long_rules());
      validate_presentation(normal_p, _extra);
      if (_kind == congruence_kind::left) {
        presentation::reverse(normal_p);
      }
      return Sims1Settings<Sims1>::short_rules(normal_p);
    }

    // TODO(Sims1) to tpp
    Sims1& long_rules(Presentation<word_type> const& p) {
      // We call make in the next two lines to ensure that the generators of
      // the presentation are {0, ..., n - 1} where n is the size of the
      // alphabet.
      auto normal_p = make<Presentation<word_type>>(p);
      validate_presentation(normal_p, short_rules());
      validate_presentation(normal_p, _extra);
      if (_kind == congruence_kind::left) {
        presentation::reverse(normal_p);
      }
      return Sims1Settings<Sims1>::long_rules(normal_p);
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
    // TODO(Sims1) to tpp + should be helper function

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

    // This class collects some common aspects of the iterator and
    // thread_iterator nested classes. The Mutex does nothing for <iterator>
    // and is an actual std::mutex for <thread_iterator>.
    class iterator_base {
     public:
      using const_reference =
          typename std::vector<digraph_type>::const_reference;

      using const_pointer = typename std::vector<digraph_type>::const_pointer;

     private:
      Presentation<word_type> _extra;
      Presentation<word_type> _longs;
      size_type               _max_num_classes;
      size_type               _min_target_node;

     protected:
      // short_rules is stored in _felsch_graph
      FelschDigraph<word_type, node_type> _felsch_graph;
      // This mutex does nothing for iterator, only does something for
      // thread_iterator
      std::mutex              _mtx;
      std::vector<PendingDef> _pending;

#ifdef LIBSEMIGROUPS_ENABLE_STATS
      Sims1Stats _stats;
#endif

     protected:
      // Push initial PendingDef's into _pending, see tpp file for
      // explanation.
      void init(size_type n);

      // We could use the copy constructor, but there's no point in copying
      // anything except the FelschDigraph and so we only copy that.
      void copy_felsch_graph(iterator_base const& that) {
        _felsch_graph = that._felsch_graph;
      }

      // Try to make the definition represented by PendingDef, returns false
      // if it wasn't possible, and true if it was.
      bool try_define(PendingDef const&);

      // Try to pop from _pending into the argument (reference), returns true
      // if successful and false if not.
      bool try_pop(PendingDef&);

     public:
      //! No doc
      iterator_base(Presentation<word_type> const& p,
                    Presentation<word_type> const& e,
                    Presentation<word_type> const& f,
                    size_type                      n);

      // None of the constructors are noexcept because the corresponding
      // constructors for Presentation aren't currently

      //! No doc
      iterator_base() = default;

      //! No doc
      // Intentionally don't copy the mutex, it doesn't compile, wouldn't make
      // sense if the mutex was used here.
      // TODO(Sims1) to tpp file
      iterator_base(iterator_base const& that)
          : _extra(that._extra),
            _longs(that._longs),
            _max_num_classes(that._max_num_classes),
            _min_target_node(that._min_target_node),
            _felsch_graph(that._felsch_graph),
            _pending(that._pending) {}

      //! No doc
      // Intentionally don't copy the mutex, it doesn't compile, wouldn't make
      // sense if the mutex was used here.
      // TODO(Sims1) to tpp file
      iterator_base(iterator_base&& that)
          : _extra(std::move(that._extra)),
            _longs(std::move(that._longs)),
            _max_num_classes(std::move(that._max_num_classes)),
            _min_target_node(std::move(that._min_target_node)),
            _felsch_graph(std::move(that._felsch_graph)),
            _pending(std::move(that._pending)) {}

      //! No doc
      // Intentionally don't copy the mutex, it doesn't compile, wouldn't make
      // sense if the mutex was used here.
      // TODO(Sims1) to tpp file
      iterator_base& operator=(iterator_base const& that) {
        _extra           = that._extra;
        _longs           = that._longs;
        _max_num_classes = that._max_num_classes;
        _min_target_node = that._min_target_node;
        _felsch_graph    = that._felsch_graph;
        _pending         = that._pending;
        return *this;
      }

      //! No doc
      // Intentionally don't copy the mutex, it doesn't compile, wouldn't make
      // sense if the mutex was used here.
      // TODO(Sims1) to tpp file
      iterator_base& operator=(iterator_base&& that) {
        _extra           = std::move(that._extra);
        _longs           = std::move(that.long_rules());
        _max_num_classes = std::move(that._max_num_classes);
        _min_target_node = std::move(that._min_target_node);
        _felsch_graph    = std::move(that._felsch_graph);
        _pending         = std::move(that._pending);
        return *this;
      }

      //! No doc
      virtual ~iterator_base() = default;

      //! No doc
      bool operator==(iterator_base const& that) const noexcept {
        return _felsch_graph == that._felsch_graph;
      }

      //! No doc
      bool operator!=(iterator_base const& that) const noexcept {
        return !(operator==(that));
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
      // TODO(Sims1) to tpp
      void swap(iterator_base& that) noexcept {
        std::swap(_extra, that._extra);
        std::swap(_felsch_graph, that._felsch_graph);
        std::swap(_max_num_classes, that._max_num_classes);
        std::swap(_min_target_node, that._min_target_node);
        std::swap(_pending, that._pending);
      }

#ifdef LIBSEMIGROUPS_ENABLE_STATS
      Sims1Stats const& stats() const noexcept {
        return _stats;
      }
#endif
    };

   public:
    //! No doc
    class iterator : public iterator_base {
      using iterator_base::init;
      using iterator_base::try_define;
      using iterator_base::try_pop;

     public:
      //! No doc
      using const_pointer = typename iterator_base::const_pointer;
      //! No doc
      using const_reference = typename iterator_base::const_reference;

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

      //! No doc
      using iterator_base::iterator_base;

     private:
      // Only want Sims1 to be able to use this constructor.
      iterator(Presentation<word_type> const& p,
               Presentation<word_type> const& e,
               Presentation<word_type> const& f,
               size_type                      n);

      // So that we can use the constructor above.
      friend iterator Sims1::cbegin(Sims1::size_type) const;
      friend iterator Sims1::cend(Sims1::size_type) const;

     public:
      //! No doc
      ~iterator() = default;

      //! No doc
      // prefix
      iterator const& operator++();

      //! No doc
      // postfix
      iterator operator++(int) {
        iterator copy(*this);
        ++(*this);
        return copy;
      }

      using iterator_base::swap;

    };  // class iterator

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
    //! probably be better in this case if node \f$0\f$ was not included in
    //! the output ActionDigraph, but it is required in the implementation of
    //! the low-index congruence algorithm, and to avoid unnecessary copies,
    //! we've left it in for the time being. \param n the maximum number of
    //! classes in a congruence.
    //!
    //! \returns
    //! An iterator \c it of type \c iterator pointing to an
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
    iterator cbegin(size_type n) const {
      return iterator(short_rules(), _extra, long_rules(), n);
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
    //! An iterator \c it of type \c iterator pointing to an
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
    iterator cend(size_type) const {
      return iterator(short_rules(), _extra, long_rules(), 0);
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
    static void report_number_of_congruences(time_point& start_time,
                                             time_point& last_report,
                                             S&          last_count,
                                             uint64_t    count_now,
                                             std::mutex& mtx);
    class thread_iterator;
    class thread_runner;
  };

#ifdef LIBSEMIGROUPS_ENABLE_STATS
  std::ostream& operator<<(std::ostream& os, Sims1Stats const& stats);
#endif  // LIBSEMIGROUPS_ENABLE_STATS

  // TODO(Sims1) doc
  class RepOrc : public Sims1Settings<RepOrc> {
   private:
    size_t _min;
    size_t _max;
    size_t _size;

   public:
    RepOrc() = default;

    template <typename S>
    RepOrc(Sims1Settings<S> const& s)
        : Sims1Settings<RepOrc>(s), _min(), _max(), _size() {}

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

    using Sims1Settings<RepOrc>::short_rules;
    using Sims1Settings<RepOrc>::long_rules;
  };

  // TODO(Sims1) doc
  class MinimalRepOrc : public Sims1Settings<MinimalRepOrc> {
   private:
    size_t _size;

   public:
    MinimalRepOrc() : Sims1Settings<MinimalRepOrc>(), _size() {}

    MinimalRepOrc& target_size(size_t val) noexcept {
      _size = val;
      return *this;
    }

    size_t target_size() const noexcept {
      return _size;
    }

    template <typename T = uint32_t>
    ActionDigraph<T> digraph();
  };

}  // namespace libsemigroups

#include "sims1.tpp"

#endif  // LIBSEMIGROUPS_SIMS1_HPP_
