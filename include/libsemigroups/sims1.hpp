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
// * parallelise?
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

#include <cstddef>  // for size_t
#include <cstdint>  // for uint64_t
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
    // TODO(Sims1) put into cpp file
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
    //!
    //! \returns A value of type \c uint64_t.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    uint64_t number_of_congruences(size_type n) const;

    // Apply the function FunctionType to every one-sided congruence with at
    // most n classes
    template <typename FunctionType>
    void for_each(size_type n, FunctionType pred) const {}

    /* private:
      // TODO(Sims1) move to cpp file
      class work_stealing_const_iterator {
       public:
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

       private:
        using PendingDef = typename const_iterator::PendingDef;

        Presentation<word_type> _extra;
        Presentation<word_type> _final;
        size_type               _min_target_node;
        size_type               _num_gens;

        FelschDigraph<word_type, node_type> _felsch_graph;
        size_type                           _num_active_nodes;
        std::vector<PendingDef>             _pending;

       public:
        //! No doc
        work_stealing_const_iterator(Presentation<word_type> const& p,
                                     Presentation<word_type> const& e,
                                     Presentation<word_type> const& f,
                                     size_type                      n);

        // None of the constructors are noexcept because the corresponding
        // constructors for std::vector aren't (until C++17).
        //! No doc
        work_stealing_const_iterator() = delete;
        //! No doc
        work_stealing_const_iterator(work_stealing_const_iterator const&)
            = default;
        //! No doc
        work_stealing_const_iterator(work_stealing_const_iterator&&) = default;
        //! No doc
        work_stealing_const_iterator&
        operator=(work_stealing_const_iterator const&)
            = default;
        //! No doc
        work_stealing_const_iterator& operator=(work_stealing_const_iterator&&)
            = default;

        //! No doc
        ~work_stealing_const_iterator() = default;

        //! No doc
        bool operator==(work_stealing_const_iterator const& that) const noexcept
  { if (_num_active_nodes == 0 && that._num_active_nodes == 0) { return true;
          }
          return _num_active_nodes == that._num_active_nodes
                 && _felsch_graph == that._felsch_graph;
        }

        //! No doc
        bool operator!=(work_stealing_const_iterator const& that) const noexcept
  { return !(this->operator==(that));
        }

        //! No doc
        const_reference operator*() const noexcept {
          return _felsch_graph;
        }

        //! No doc
        const_pointer operator->() const noexcept {
          return &_felsch_graph;
        }

        // prefix
        //! No doc
        work_stealing_const_iterator const& operator++();

        //! No doc
        // postfix
        work_stealing_const_iterator operator++(int) {
          work_stealing_const_iterator copy(*this);
          ++(*this);
          return copy;
        }

        //! No doc
        void swap(work_stealing_const_iterator& that) noexcept {
          std::swap(_extra, that._extra);
          std::swap(_max_num_classes, that._max_num_classes);
          std::swap(_min_target_node, that._min_target_node);
          std::swap(_num_active_nodes, that._num_active_nodes);
          std::swap(_num_gens, that._num_gens);
          std::swap(_pending, that._pending);
          std::swap(_felsch_graph, that._felsch_graph);
        }
      };

     private:
      using PendingDef = typename const_iterator::PendingDef;
      std::deque<PendingDef> _queue;
      mutable std::mutex     _mutex;

     public:
      using pending_def_iterator = typename std::deque<PendingDef>::iterator;

      work_stealing_const_iterator()                                    =
  default; work_stealing_const_iterator(work_stealing_const_iterator const&) =
  delete; work_stealing_const_iterator& operator=(work_stealing_const_iterator
  const&) = delete;
      // TODO(Sims1) the move constructors
      // TODO (Sims1) by value, maybe not a good idea?
      void push(PendingDef pd) {
        std::lock_guard<std::mutex> lock(_mutex);
        _queue.push_front(std::move(pd));
      }

      void push(pending_def_iterator first, pending_def_iterator last) {
        std::lock_guard<std::mutex> lock(_mutex);
        _queue.insert(_queue.cbegin(), first, last);
      }

      bool empty() const {
        std::lock_guard<std::mutex> lock(_mutex);
        return _queue.empty();
      }

      bool try_pop(PendingDef& pd) {
        std::lock_guard<std::mutex> lock(_mutex);
        if (_queue.empty()) {
          return false;
        }
        pd = std::move(_queue.front());
        _queue.pop_front();
        return true;
      }

      bool try_steal(work_stealing_const_iterator& q) {
        std::lock_guard<std::mutex> lock(_mutex);
        if (_queue.empty()) {
          return false;
        }
        // TODO(Sims1): this probably doesn't do as expected if _queue.size()
        // == 1
        // TODO(Sims1) could steal in a different way: maybe interlaced (steal
        // every other item); steal a fixed proportion of every queue
        q._queue.push(_queue.cbegin() + _queue.size() / 2, _queue.cend());
        _queue.erase(_queue.cbegin() + _queue.size() / 2, _queue.cend());
        return true;
      }
    };

    class ThreadPool {
     private:
      using PendingDef = typename const_iterator::PendingDef;

      std::atomic_bool                                           _done;
      std::queue<PendingDef>                                     _pool_queue;
      std::vector<std::unique_ptr<work_stealing_const_iterator>> _queues;
      std::vector<std::thread>                                   _threads;
      detail::JoinThreads                                        _joiner;
      work_stealing_const_iterator*                              _local_queue;
      unsigned                                                   _my_index;
      mutable std::mutex                                         _mutex;

      void worker_thread(unsigned my_index) {
        _my_index    = my_index;
        _local_queue = _queues[my_index].get();
        while (!_done) {
          run_pending_task();
        }
      }

      bool pop_from_local_queue(PendingDef& pd) {
        return _local_queue && _local_queue->try_pop(pd);
      }

      bool pop_from_pool_queue(PendingDef& pd) {
        std::lock_guard<std::mutex> lock(_mutex);
        if (_pool_queue.empty()) {
          return false;
        }
        pd = std::move(_pool_queue.front());
        _pool_queue.pop_front();
        return true;
      }

      bool pop_from_other_thread_queue() {
        for (size_t i = 0; i < _queues.size(); ++i) {
          unsigned const index = (_my_index + i + 1) % _queues.size();
          // TODO(Sims1) could always do something different here, like find
          // the largest queue and steal from that.
          if (_queues[index]->try_steal(_local_queue)) {
            return true;
          }
        }
        return false;
      }

     public:
      ThreadPool() : _done(false), _joiner(_threads) {
        unsigned const thread_count = std::thread::hardware_concurrency();
        try {
          for (size_t i = 0; i < thread_count; ++i) {
            _queues.push_back(std::unique_ptr<work_stealing_const_iterator>(
                new work_stealing_const_iterator()));
          }
          for (size_t i = 0; i < thread_count; ++i) {
            _threads.push_back(&ThreadPool::worker_thread, this, i);
          }
        } catch (...) {
          _done = true;
          throw;
        }
      }

      ~ThreadPool() {
        _done = true;
      }

      void run_pending_task() {
        PendingDef pd;
        if (pop_from_local_queue(pd) || pop_from_pool_queue(pd)
            || pop_from_other_thread_queue()) {
          // TODO(Sims1) this is where we should be incrementing the iterator
          // using the relevant data

        } else {
          std::this_thread::yield();
        }
      }
    }; */
  };

#ifdef LIBSEMIGROUPS_ENABLE_STATS
  std::ostream& operator<<(std::ostream&                os,
                           typename sims1::Stats const& stats);
#endif  // LIBSEMIGROUPS_ENABLE_STATS

}  // namespace libsemigroups

#include "sims1.tpp"

#endif  // LIBSEMIGROUPS_SIMS1_HPP_
