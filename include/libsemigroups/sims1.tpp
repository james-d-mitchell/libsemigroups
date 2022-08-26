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
// congruence" algorithm for semigroups and monoid.

namespace libsemigroups {
#ifdef LIBSEMIGROUPS_ENABLE_STATS
  template <typename T>
  template <typename Mutex>
  void
  Sims1<T>::iterator_base<Mutex>::stats_update(size_type current_num_edges) {
    if (this->_felsch_graph.number_of_edges() > current_num_edges) {
      if (_stats.depth > 0) {
        _stats.depth--;
      }
    } else {
      _stats.depth++;
    }
    _stats.max_depth = std::max(_stats.max_depth, _stats.depth);
    _stats.max_pending
        = std::max(_stats.max_pending, static_cast<uint64_t>(_pending.size()));
    _stats.num_nodes++;
    if (_stats.depth > 0) {
      _stats.mean_depth
          += (_stats.depth - _stats.mean_depth) / _stats.num_nodes;
    }
  }

  template <typename T>
  template <typename Mutex>
  Sims1Stats const &Sims1<T>::iterator_base<Mutex>::stats() const noexcept {
    return _stats;
  }

  std::ostream &operator<<(std::ostream &os, Sims1Stats const &stats) {
    detail::PrintTable pt;
    pt.header("Summary of statistics (Sims low-index algorithm)");
    pt("mean depth ", "%'14lf", stats.mean_depth);
    pt("max depth ", "%'14llu", stats.max_depth);
    pt("max pending ", "%'14llu", stats.max_pending);
    pt("number of nodes visited ", "%'14llu", stats.num_nodes);
    pt("approx. number of good nodes ", "%'14llu*", stats.num_good_nodes);
    pt("ratio of good / bad nodes ",
       "%'14lf",
       static_cast<double>(stats.num_good_nodes) / stats.num_nodes);
    pt("");
    pt("*the number of complete digraphs found times their number of nodes, "
       "this value overcounts the number of good nodes!");
    pt.footer("End of summary (Sims low-index algorithm)");
    os << pt.emit();
    return os;
  }

#endif

  template <typename T>
  Sims1<T>::Sims1(congruence_kind                ck,
                  Presentation<word_type> const &p,
                  Presentation<word_type> const &e)
      : Sims1(ck, p, e, Sims1Settings<Sims1<T>>()) {}

  template <typename T>
  template <typename S>
  Sims1<T>::Sims1(congruence_kind                ck,
                  Presentation<word_type> const &p,
                  Sims1Settings<S> const &       s)
      : Sims1(ck, p, Presentation<word_type>(), s) {}

  template <typename T>
  Sims1<T>::Sims1(congruence_kind ck, Presentation<word_type> const &p)
      : Sims1(ck, p, Presentation<word_type>()) {}

  template <typename T>
  template <typename S>
  Sims1<T>::Sims1(congruence_kind                ck,
                  Presentation<word_type> const &p,
                  Presentation<word_type> const &e,
                  Sims1Settings<S> const &       s)
      : Sims1Settings<Sims1<T>>(s), _extra(), _final(), _presentation() {
    if (ck == congruence_kind::twosided) {
      LIBSEMIGROUPS_EXCEPTION(
          "expected congruence_kind::right or congruence_kind::left");
    } else if (p.alphabet() != e.alphabet() && !e.alphabet().empty()) {
      LIBSEMIGROUPS_EXCEPTION(
          "the 2nd and 3rd arguments (presentations) are not defined over "
          "the same alphabets, expected alphabet %s for 3rd argument got %s",
          detail::to_string(p.alphabet()).c_str(),
          detail::to_string(e.alphabet()).c_str());
    }
    p.validate();  // TODO(Sims1) Test for this

    // We call make in the next two lines to ensure that the generators of the
    // presentation are {0, ..., n - 1} where n is the size of the alphabet.
    _presentation = make<Presentation<word_type>>(p);
    _extra        = make<Presentation<word_type>>(e);
    if (ck == congruence_kind::left) {
      presentation::reverse(_presentation);
      presentation::reverse(_extra);
    }
    perform_split();
  }

  template <typename T>
  Sims1<T>::~Sims1() = default;

  template <typename T>
  void Sims1<T>::perform_split() {
    size_type val = Sims1Settings<Sims1<T>>::split_at();
    if (val == UNDEFINED) {
      return;
    }

    LIBSEMIGROUPS_ASSERT(val < _presentation.rules.size() / 2
                                   + _final.rules.size() / 2);

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

  template <typename T>
  uint64_t Sims1<T>::number_of_congruences(size_type n) const {
    if (this->number_of_threads() == 1) {
      uint64_t result = 0;
      for_each(n, [&result](digraph_type const &) { ++result; });
      return result;
    } else {
      std::atomic_int64_t result(0);
      for_each(n, [&result](digraph_type const &) { ++result; });
      return result;
    }
  }

  // Apply the function pred to every one-sided congruence with at
  // most n classes
  template <typename T>
  void
  Sims1<T>::for_each(size_type                                 n,
                     std::function<void(digraph_type const &)> pred) const {
    std::chrono::high_resolution_clock::time_point last_report
        = std::chrono::high_resolution_clock::now();

    detail::Timer t;

    if (this->number_of_threads() == 1) {
      REPORT_DEFAULT("using 0 additional threads\n");
      if (!report::should_report()) {
        std::for_each(cbegin(n), cend(n), pred);
      } else {
        auto const last       = cend(n);
        uint64_t   count      = 0;
        uint64_t   last_count = 0;
        for (auto it = cbegin(n); it != last; ++it) {
          pred(*it);
          report_number_of_congruences(last_report, last_count, ++count, t);
        }
      }
    } else {
      REPORT_DEFAULT("using %d / %d additional threads\n",
                     this->number_of_threads(),
                     std::thread::hardware_concurrency());
      Den den(presentation(), _extra, _final, n, this->number_of_threads());
      if (!report::should_report()) {
        auto pred_wrapper = [&pred](digraph_type const &ad) {
          pred(ad);
          return false;
        };
        den.run(pred_wrapper);
      } else {
        std::atomic_uint64_t count(0);
        std::atomic_uint64_t last_count(0);

        den.run([&](digraph_type const &ad) {
          report_number_of_congruences(last_report, last_count, ++count, t);
          pred(ad);
          return false;
        });
        den.digraph();  // for the printing
      }
    }
  }

  template <typename T>
  typename Sims1<T>::digraph_type
  Sims1<T>::find_if(size_type                                 n,
                    std::function<bool(digraph_type const &)> pred) const {
    std::chrono::high_resolution_clock::time_point last_report
        = std::chrono::high_resolution_clock::now();

    detail::Timer t;

    if (this->number_of_threads() == 1) {
      REPORT_DEFAULT("using 0 additional threads\n");
      if (!report::should_report()) {
        return *std::find_if(cbegin(n), cend(n), pred);
      } else {
        auto const last       = cend(n);
        uint64_t   count      = 0;
        uint64_t   last_count = 0;
        for (auto it = cbegin(n); it != last; ++it) {
          if (pred(*it)) {
            return *it;
          }
          report_number_of_congruences(last_report, last_count, ++count, t);
        }
        return *last;  // the empty digraph
      }
    } else {
      REPORT_DEFAULT("using %d / %d additional threads\n",
                     this->number_of_threads(),
                     std::thread::hardware_concurrency());
      Den den(presentation(), _extra, _final, n, this->number_of_threads());
      if (!report::should_report()) {
        den.run(pred);
      } else {
        std::atomic_uint64_t count(0);
        std::atomic_uint64_t last_count(0);
        den.run([&](digraph_type const &ad) {
          report_number_of_congruences(last_report, last_count, ++count, t);
          return pred(ad);
        });
      }
      return den.digraph();
    }
  }

  // Can't be static because REPORT_DEFAULT uses this
  template <typename T>
  template <typename S>
  void Sims1<T>::report_number_of_congruences(time_point &  last_report,
                                              S &           last_count,
                                              uint64_t      count,
                                              detail::Timer t) const {
    if (count - last_count > this->report_interval()) {
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
        REPORT_DEFAULT("found %s congruences in %.6fs!\n",
                       detail::group_digits(count).c_str(),
                       seconds.count());
      }
    }
  }

  ///////////////////////////////////////////////////////////////////////////////
  // iterator_base nested class
  ///////////////////////////////////////////////////////////////////////////////

  template <typename T>
  template <typename Mutex>
  Sims1<T>::iterator_base<Mutex>::iterator_base(
      Presentation<word_type> const &p,
      Presentation<word_type> const &extra,
      Presentation<word_type> const &final_,
      size_type                      n)
      : _extra(extra),
        _felsch_graph(p, n),
        _final(final_),
        _max_num_classes(p.contains_empty_word() ? n : n + 1),
        _min_target_node(p.contains_empty_word() ? 0 : 1),
        _mtx() {
    _felsch_graph.number_of_active_nodes(n == 0 ? 0 : 1);
    // = 0 indicates iterator is done
  }

  // The following function is separated from the constructor so that it isn't
  // called in the constructor of every thread_iterator
  template <typename T>
  template <typename Mutex>
  void Sims1<T>::iterator_base<Mutex>::init(size_type n) {
    if (n > 1) {
      _pending.emplace_back(0, 0, 1, 0, 2);
    }
    if (this->_min_target_node == 0) {
      _pending.emplace_back(0, 0, 0, 0, 1);
    }
  }

  template <typename T>
  template <typename Mutex>
  template <typename Lock>
  bool Sims1<T>::iterator_base<Mutex>::try_pop(PendingDef &pd) {
    Lock lock(_mtx);
    (void) lock;
    if (this->_pending.empty()) {
      return false;
    }
    pd = std::move(this->_pending.back());
    this->_pending.pop_back();
    return true;
  }

  template <typename T>
  template <typename Mutex>
  template <typename Lock>
  bool Sims1<T>::iterator_base<Mutex>::try_define(PendingDef const &current) {
    LIBSEMIGROUPS_ASSERT(current.target < current.num_nodes);
    LIBSEMIGROUPS_ASSERT(current.num_nodes <= this->_max_num_classes);
    {
      Lock lock(_mtx);
      (void) lock;
      // Backtrack if necessary
      this->_felsch_graph.reduce_number_of_edges_to(current.num_edges);

      // It might be that current.target is a new node, in which case
      // _felsch_graph.number_of_active_nodes() includes this new node even
      // before the edge current.source -> current.target is defined.
      this->_felsch_graph.number_of_active_nodes(current.num_nodes);

      LIBSEMIGROUPS_ASSERT(
          this->_felsch_graph.unsafe_neighbor(current.source, current.generator)
          == UNDEFINED);

      size_type const start = this->_felsch_graph.number_of_edges();

      this->_felsch_graph.def_edge(
          current.source, current.generator, current.target);

      auto first = this->_extra.rules.cbegin();
      auto last  = this->_extra.rules.cend();
      if (!felsch_digraph::compatible(this->_felsch_graph, 0, first, last)
          || !this->_felsch_graph.process_definitions(start)) {
        // Seems to be important to check _extra first then process_definitions
        return false;
      }
    }

    letter_type     a        = current.generator + 1;
    size_type const M        = this->_felsch_graph.number_of_active_nodes();
    size_type const N        = this->_felsch_graph.number_of_edges();
    size_type const num_gens = this->_felsch_graph.out_degree();

    for (node_type next = current.source; next < M; ++next) {
      for (; a < num_gens; ++a) {
        if (this->_felsch_graph.unsafe_neighbor(next, a) == UNDEFINED) {
          Lock lock(_mtx);
          (void) lock;
          if (M < this->_max_num_classes) {
            _pending.emplace_back(next, a, M, N, M + 1);
          }
          for (node_type b = M; b-- > this->_min_target_node;) {
            _pending.emplace_back(next, a, b, N, M);
          }
          return false;
        }
      }
      a = 0;
    }
    // No undefined edges, word graph is complete
    LIBSEMIGROUPS_ASSERT(N == M * num_gens);

#ifdef LIBSEMIGROUPS_ENABLE_STATS
    this->_stats.num_good_nodes += this->_felsch_graph.number_of_active_nodes();
#endif
    auto first = this->_final.rules.cbegin();
    auto last  = this->_final.rules.cend();
    return felsch_digraph::compatible(this->_felsch_graph, 0, M, first, last);
  }

  ///////////////////////////////////////////////////////////////////////////////
  // iterator nested class
  ///////////////////////////////////////////////////////////////////////////////

  template <typename T>
  Sims1<T>::iterator::iterator(Presentation<word_type> const &p,
                               Presentation<word_type> const &e,
                               Presentation<word_type> const &f,
                               size_type                      n)
      : iterator_base(p, e, f, n) {
    if (this->_felsch_graph.number_of_active_nodes() == 0) {
      return;
    }
    this->init(n);
    ++(*this);
    // The increment above is required so that when dereferencing any
    // instance of this type we obtain a valid word graph (o/w the value
    // pointed to here is empty).
  }

  // TODO(Sims1): remove code overlap with try_define
  template <typename T>
  typename Sims1<T>::iterator const &Sims1<T>::iterator::operator++() {
    PendingDef current;
    while (this->template try_pop<Noop>(current)) {
#if LIBSEMIGROUPS_ENABLE_STATS
      this->stats_update(current.num_edges);
#endif
      if (this->template try_define<Noop>(current)) {
        return *this;
      }
    }
    this->_felsch_graph.number_of_active_nodes(0);
    // indicates that the iterator is done
    this->_felsch_graph.restrict(0);
    return *this;
  }

  template <typename T>
  Sims1<T> &Sims1<T>::split_at(size_type val) {
    if (val != UNDEFINED
        && val > _presentation.rules.size() / 2 + _final.rules.size() / 2) {
      LIBSEMIGROUPS_EXCEPTION(
          "expected a value in the range [0, %llu) or UNDEFINED, found %llu",
          uint64_t(_presentation.rules.size() / 2 + _final.rules.size() / 2),
          uint64_t(val));
    }
    Sims1Settings<Sims1<T>>::split_at(val);
    perform_split();
    return *this;
  }

  ///////////////////////////////////////////////////////////////////////////////
  // thread_iterator
  ///////////////////////////////////////////////////////////////////////////////

  template <typename T>
  class Sims1<T>::thread_iterator : public iterator_base<std::mutex> {
    friend class Sims1<T>::Den;

   public:
    //! No doc
    thread_iterator(Presentation<word_type> const &p,
                    Presentation<word_type> const &e,
                    Presentation<word_type> const &f,
                    size_type                      n)
        : iterator_base<std::mutex>(p, e, f, n) {}

    // None of the constructors are noexcept because the corresponding
    // constructors for std::vector aren't (until C++17).
    //! No doc
    thread_iterator() = delete;
    //! No doc
    thread_iterator(thread_iterator const &) = delete;
    //! No doc
    thread_iterator(thread_iterator &&) = delete;
    //! No doc
    thread_iterator &operator=(thread_iterator const &) = delete;
    //! No doc
    thread_iterator &operator=(thread_iterator &&) = delete;

    //! No doc
    ~thread_iterator() = default;

    // prefix
    //! No doc
    /*    bool try_define(PendingDef const &current) {
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
              for (letter_type a = 0; a < this->_felsch_graph.out_degree(); ++a)
    { LIBSEMIGROUPS_ASSERT(this->_felsch_graph.unsafe_neighbor(next, a)
                                     != UNDEFINED);
              }
            }
            for (letter_type a = 0; a < current.generator; ++a) {
              LIBSEMIGROUPS_ASSERT(
                  this->_felsch_graph.unsafe_neighbor(current.source, a)
                  != UNDEFINED);
            }

    #endif
            size_type const start = this->_felsch_graph.number_of_edges();

            this->_felsch_graph.def_edge(
                current.source, current.generator, current.target);

            auto first = this->_extra.rules.cbegin();
            auto last  = this->_extra.rules.cend();
            if (!felsch_digraph::compatible(this->_felsch_graph, 0, first, last)
                || !this->_felsch_graph.process_definitions(start)) {
              return false;
            }
          }

          letter_type     a        = current.generator + 1;
          size_type const M        =
    this->_felsch_graph.number_of_active_nodes(); size_type const N        =
    this->_felsch_graph.number_of_edges(); size_type const num_gens =
    this->_felsch_graph.out_degree();

          for (node_type next = current.source; next < M; ++next) {
            for (; a < num_gens; ++a) {
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

          LIBSEMIGROUPS_ASSERT(N == M * num_gens);

          // No undefined edges, word graph is complete
          auto first = this->_final.rules.cbegin();
          auto last  = this->_final.rules.cend();
          return felsch_digraph::compatible(this->_felsch_graph, 0, M, first,
    last);
        } */

   public:
    void push(PendingDef pd) {
      this->_pending.push_back(std::move(pd));
    }

    void steal_from(thread_iterator &that) {
      // WARNING <that> must be locked before calling this function
      std::lock_guard<std::mutex> lock(this->_mtx);
      LIBSEMIGROUPS_ASSERT(_pending.empty());
      // Copy the FelschDigraph from that into *this
      this->copy_felsch_graph(that);

      // Unzip that._pending into _pending and that._pending, this seems to
      // give better performance in the search than splitting that._pending
      // into [begin, begin + size / 2) and [begin + size / 2, end)
      for (size_t i = 0; i < that._pending.size(); i += 2) {
        this->_pending.push_back(std::move(that._pending[i]));
        that._pending[i / 2] = std::move(that._pending[i + 1]);
      }
      that._pending.erase(that._pending.cbegin() + that._pending.size() / 2,
                          that._pending.cend());
    }

    bool try_steal(thread_iterator &q) {
      std::lock_guard<std::mutex> lock(this->_mtx);
      if (this->_pending.empty()) {
        return false;
      }
      // Copy the FelschDigraph and half pending from *this into q
      q.steal_from(*this);  // Must call steal_from on q, so that q is locked
      return true;
    }
  };

  ////////////////////////////////////////////////////////////////////////
  // Den
  ////////////////////////////////////////////////////////////////////////

  template <typename T>
  class Sims1<T>::Den {
   private:
    std::atomic_bool                              _done;
    std::vector<std::unique_ptr<thread_iterator>> _theives;
    std::vector<std::thread>                      _threads;
    std::vector<uint64_t>                         _total_pending;
    size_type                                     _num_threads;
    digraph_type                                  _result;
    std::mutex                                    _mtx;

    void worker_thread(unsigned                                  my_index,
                       std::function<bool(digraph_type const &)> hook) {
      using Lock = std::lock_guard<std::mutex>;
      PendingDef pd;
      for (auto i = 0; i < 128; ++i) {
        while ((pop_from_local_queue(pd, my_index)
                || pop_from_other_thread_queue(pd, my_index))
               && !_done) {
          if (_theives[my_index]->template try_define<Lock>(pd)) {
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
        // It's possible to reach here before all of the work is done,
        // because by coincidence there's nothing in the local queue and
        // nothing in any other queue either, this sometimes leads to
        // threads shutting down earlier than desirable. On the other hand,
        // maybe this is a desirable.
      }
    }

    bool pop_from_local_queue(PendingDef &pd, unsigned my_index) {
      using Lock = std::lock_guard<std::mutex>;
      return _theives[my_index]->template try_pop<Lock>(pd);
    }

    bool pop_from_other_thread_queue(PendingDef &pd, unsigned my_index) {
      for (size_t i = 0; i < _theives.size() - 1; ++i) {
        unsigned const index = (my_index + i + 1) % _theives.size();
        // Could always do something different here, like find
        // the largest queue and steal from that? I tried this and it didn't
        // seem to be faster.
        if (_theives[index]->try_steal(*_theives[my_index])) {
          return pop_from_local_queue(pd, my_index);
        }
      }
      return false;
    }

   public:
    Den(Presentation<word_type> const &p,
        Presentation<word_type> const &e,
        Presentation<word_type> const &f,
        size_type                      n,
        size_type                      num_threads)
        : _done(false),
          _theives(),
          _threads(),
          _total_pending(num_threads, 0),
          _num_threads(num_threads),
          _result(),
          _mtx() {
      for (size_t i = 0; i < _num_threads; ++i) {
        _theives.push_back(std::make_unique<thread_iterator>(p, e, f, n));
      }
      _theives.front()->init(n);
    }

    ~Den() = default;

    digraph_type const &digraph() const {
      REPORT_DEFAULT(
          "total number of nodes in search tree was %s\n",
          detail::group_digits(std::accumulate(_total_pending.cbegin(),
                                               _total_pending.cend(),
                                               uint64_t(0)))
              .c_str());
      return _result;
    }

    void run(std::function<bool(digraph_type const &)> hook) {
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

  ////////////////////////////////////////////////////////////////////////
  // RepOrc helper class
  ////////////////////////////////////////////////////////////////////////

  template <typename T>
  ActionDigraph<T> RepOrc::digraph() const {
    using digraph_type = typename Sims1<T>::digraph_type;
    using node_type    = typename digraph_type::node_type;

    auto hook = [&](digraph_type const &x) {
      if (x.number_of_active_nodes() >= _min) {
        auto first = (_presentation.contains_empty_word() ? 0 : 1);
        auto S     = make<FroidurePin<Transf<0, node_type>>>(
            x, first, x.number_of_active_nodes());
        if (_presentation.contains_empty_word()) {
          auto one = S.generator(0).identity();
          if (!S.contains(one)) {
            S.add_generator(one);
          }
        }
        LIBSEMIGROUPS_ASSERT(S.size() <= _size);
        if (S.size() == _size) {
          return true;
        }
      }
      return false;
    };

    auto result = Sims1<T>(congruence_kind::right, _presentation, *this)
                      .find_if(_max, hook);
    if (result.number_of_active_nodes() == 0) {
      result.restrict(0);
    } else {
      if (_presentation.contains_empty_word()) {
        result.restrict(result.number_of_active_nodes());
      } else {
        result.induced_subdigraph(1, result.number_of_active_nodes());
        std::for_each(result.begin(), result.end(), [](auto &val) { --val; });
        result.number_of_active_nodes(result.number_of_active_nodes() - 1);
      }
    }
    return result;
  }

  ////////////////////////////////////////////////////////////////////////
  // MinimalRepOrc helper class
  ////////////////////////////////////////////////////////////////////////

  template <typename T>
  ActionDigraph<T> MinimalRepOrc::digraph() {
    auto cr = RepOrc(_presentation, *this);

    size_t hi = (_presentation.contains_empty_word() ? _size : _size + 1);
    REPORT_DEFAULT("trying to find faithful rep. o.r.c. on [1, %llu) points\n",
                   hi + 1);
    auto best = cr.min_nodes(1).max_nodes(hi).target_size(_size).digraph();

    if (best.number_of_nodes() == 0) {
      REPORT_DEFAULT("no faithful rep. o.r.c. on [1, %llu) points found\n",
                     hi + 1);
      // No faithful representation on up to <size> points, or trivial
      return best;
    } else if (best.number_of_nodes() == 1) {
      REPORT_DEFAULT("found a faithful rep. o.r.c. on 1 point\n");
      return best;
    }
    hi = best.number_of_nodes();
    REPORT_DEFAULT("found a faithful rep. o.r.c. on %llu points\n", hi);

    REPORT_DEFAULT("trying to find faithful rep. o.r.c. on [1, %llu) points\n",
                   hi);
    ActionDigraph<T> next = std::move(cr.max_nodes(hi - 1).digraph());
    while (next.number_of_nodes() != 0) {
      hi = next.number_of_nodes();
      REPORT_DEFAULT("found a faithful rep. o.r.c. on %llu points\n", hi);
      best = std::move(next);
      REPORT_DEFAULT(
          "trying to find faithful rep. o.r.c. on [1, %llu) points\n", hi);
      next = std::move(cr.max_nodes(hi - 1).digraph());
    }
    REPORT_DEFAULT("no faithful rep. o.r.c. on [1, %llu) points found\n", hi);
    return best;
  }

}  // namespace libsemigroups
