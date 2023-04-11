//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019 James D. Mitchell
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

// This file contains a class KnuthBendix which implements the Knuth-Bendix
// algorithm for finitely presented monoids.

#ifndef LIBSEMIGROUPS_KNUTH_BENDIX_NEW_HPP_
#define LIBSEMIGROUPS_KNUTH_BENDIX_NEW_HPP_

#include <cstddef>  // for size_t
#include <iosfwd>   // for string, ostream
#include <memory>   // for unique_ptr
#include <set>
#include <stack>
#include <vector>  // for vector

#include "cong-intf.hpp"     // for CongruenceInterface
#include "digraph.hpp"       // for ActionDigraph
#include "froidure-pin.hpp"  // for FroidurePin
#include "paths.hpp"         // for Paths
#include "present.hpp"       // for Presentation
#include "runner.hpp"
#include "to-presentation.hpp"  // for Presentation
#include "types.hpp"            // for word_type
#include "words.hpp"            // for word_to_string

namespace libsemigroups {
  // Forward declarations
  namespace v3::detail {
    class KBE;
  }  // namespace v3::detail

  //! Defined in ``knuth-bendix.hpp``.
  //!
  //! On this page we describe the functionality relating to the Knuth-Bendix
  //! algorithm for semigroups and monoids that is available in
  //! ``libsemigroups``. This page contains a details of the member functions
  //! of the class KnuthBendix.
  //!
  //! This class is used to represent a
  //! [string rewriting system](https://w.wiki/9Re)
  //! defining a finitely presented monoid or semigroup.
  //!
  //! \sa congruence::KnuthBendix.
  //!
  //! \par Example
  //! \code
  //! KnuthBendix kb;
  //! kb.set_alphabet("abc");
  //!
  //! kb.add_rule("aaaa", "a");
  //! kb.add_rule("bbbb", "b");
  //! kb.add_rule("cccc", "c");
  //! kb.add_rule("abab", "aaa");
  //! kb.add_rule("bcbc", "bbb");
  //!
  //! !kb.confluent();       // true
  //! kb.run();
  //! kb.number_of_active_rules();  // 31
  //! kb.confluent();        // true
  //! \endcode
  class KnuthBendix : public Runner {
    friend class ::libsemigroups::v3::detail::KBE;  // defined in kbe.hpp

    ////////////////////////////////////////////////////////////////////////
    // KnuthBendix - typedefs/aliases - private
    ////////////////////////////////////////////////////////////////////////

    using external_string_type = std::string;
    using internal_string_type = std::string;
    using external_char_type   = char;
    using internal_char_type   = char;

    ////////////////////////////////////////////////////////////////////////
    // KnuthBendix - nested subclasses - private
    ////////////////////////////////////////////////////////////////////////

    struct Rule {
      KnuthBendix const*    _kbimpl;
      internal_string_type* _lhs;
      internal_string_type* _rhs;
      int64_t               _id;

      // Construct from KnuthBendix with new but empty internal_string_type's
      Rule(KnuthBendix const* kbimpl, int64_t id);

      Rule& operator=(Rule const& copy) = delete;
      Rule(Rule const& copy)            = delete;
      Rule(Rule&& copy)                 = delete;
      Rule& operator=(Rule&& copy)      = delete;

      // Destructor, deletes pointers used to create the rule.
      ~Rule() {
        delete _lhs;
        delete _rhs;
      }

      // Returns the left hand side of the rule, which is guaranteed to be
      // greater than its right hand side according to the reduction ordering
      // of the KnuthBendix used to construct this.
      internal_string_type* lhs() const noexcept {
        return _lhs;
      }

      // Returns the right hand side of the rule, which is guaranteed to be
      // less than its left hand side according to the reduction ordering of
      // the KnuthBendix used to construct this.
      internal_string_type* rhs() const noexcept {
        return _rhs;
      }

      void rewrite();

      void clear() {
        LIBSEMIGROUPS_ASSERT(_id != 0);
        _lhs->clear();
        _rhs->clear();
      }

      inline bool active() const noexcept {
        LIBSEMIGROUPS_ASSERT(_id != 0);
        return (_id > 0);
      }

      void deactivate() noexcept;

      void activate() noexcept;

      void set_id(int64_t id) noexcept {
        LIBSEMIGROUPS_ASSERT(id > 0);
        LIBSEMIGROUPS_ASSERT(!active());
        _id = -1 * id;
      }

      int64_t id() const noexcept {
        LIBSEMIGROUPS_ASSERT(_id != 0);
        return _id;
      }

    };  // struct Rule

    friend struct Rule;

    class RuleLookup;  // forward decl

    // Overlap measures
    struct OverlapMeasure {
      virtual size_t operator()(Rule const*,
                                Rule const*,
                                internal_string_type::const_iterator const&)
          = 0;
      virtual ~OverlapMeasure() {}
    };

    struct ABC;
    struct AB_BC;
    struct MAX_AB_BC;

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendix - friend declarations - private
    //////////////////////////////////////////////////////////////////////////

   public:
    using rule_type = std::pair<std::string, std::string>;

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendix - types - public
    //////////////////////////////////////////////////////////////////////////

    //! This type contains various enums for specifying certain options to a
    //! KnuthBendix instance.
    struct options {
      //! Values for specifying how to measure the length of an overlap.
      //!
      //! The values in this enum determine how a KnuthBendix instance
      //! measures the length \f$d(AB, BC)\f$ of the overlap of two words
      //! \f$AB\f$ and \f$BC\f$:
      //!
      //! \sa overlap_policy(options::overlap)
      enum class overlap {
        //! \f$d(AB, BC) = |A| + |B| + |C|\f$
        ABC = 0,
        //! \f$d(AB, BC) = |AB| + |BC|\f$
        AB_BC = 1,
        //! \f$d(AB, BC) = max(|AB|, |BC|)\f$
        MAX_AB_BC = 2
      };
    };

   private:
    struct Settings {
      Settings();
      size_t           _check_confluence_interval;
      size_t           _max_overlap;
      size_t           _max_rules;
      options::overlap _overlap_policy;
    } _settings;

    ////////////////////////////////////////////////////////////////////////
    // KnuthBendix - data - private
    ////////////////////////////////////////////////////////////////////////

    ActionDigraph<size_t>            _gilman_digraph;
    std::list<Rule const*>           _active_rules;
    mutable std::atomic<bool>        _confluent;
    mutable std::atomic<bool>        _confluence_known;
    mutable std::list<Rule*>         _inactive_rules;
    bool                             _internal_is_same_as_external;
    size_t                           _min_length_lhs_rule;
    std::list<Rule const*>::iterator _next_rule_it1;
    std::list<Rule const*>::iterator _next_rule_it2;
    OverlapMeasure*                  _overlap_measure;
    Presentation<std::string>        _presentation;
    std::set<RuleLookup>             _set_rules;
    std::stack<Rule*>                _stack;
    mutable size_t                   _total_rules;

#ifdef LIBSEMIGROUPS_VERBOSE
    size_t                                   _max_stack_depth;
    size_t                                   _max_word_length;
    size_t                                   _max_active_word_length;
    size_t                                   _max_active_rules;
    std::unordered_set<internal_string_type> _unique_lhs_rules;
#endif

   public:
    //////////////////////////////////////////////////////////////////////////
    // KnuthBendix - constructors and destructor - public
    //////////////////////////////////////////////////////////////////////////

    //! Default constructor.
    //!
    //! Constructs a KnuthBendix instance with no rules, and the short-lex
    //! reduction ordering.
    //!
    //! \parameters
    //! (None)
    //!
    //! \complexity
    //! Constant.
    KnuthBendix();

    // KnuthBendix& init();

    // TODO init

    //! Copy constructor.
    //!
    //! \param copy the KnuthBendix instance to copy.
    //!
    //! \complexity
    //! \f$O(n)\f$ where \f$n\f$ is the sum of the lengths of the words in
    //! rules of \p copy.
    KnuthBendix(KnuthBendix const& copy);

    //! Deleted.
    // KnuthBendix(KnuthBendix&&);

    //! Deleted. TODO undelete
    KnuthBendix& operator=(KnuthBendix const&) = delete;

    //! Deleted. TODO undelete
    // KnuthBendix& operator=(KnuthBendix&&) = delete;

    ~KnuthBendix();

    // TODO init version
    KnuthBendix(Presentation<std::string> const& p) : KnuthBendix() {
      p.validate();
      _presentation    = p;
      auto const first = _presentation.rules.cbegin();
      auto const last  = _presentation.rules.cend();
      for (auto it = first; it != last; it += 2) {
        add_rule_impl(*it, *(it + 1));
      }
    }

    KnuthBendix(Presentation<std::string>&& p) : KnuthBendix() {
      p.validate();
      _presentation = std::move(p);
      // TODO remove code dupl
      auto const first = _presentation.rules.cbegin();
      auto const last  = _presentation.rules.cend();
      for (auto it = first; it != last; it += 2) {
        add_rule_impl(*it, *(it + 1));
      }
    }

    template <typename Word>
    KnuthBendix(Presentation<Word> const& p)
        : KnuthBendix(to_presentation<std::string>(p)) {}

    template <typename Word>
    KnuthBendix(Presentation<Word>&& p)
        : KnuthBendix(
            to_presentation<std::string>(std::forward<Presentation<Word>>(p))) {
    }

    [[nodiscard]] Presentation<std::string> const&
    presentation() const noexcept {
      return _presentation;
    }

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendix - setters for optional parameters - public
    //////////////////////////////////////////////////////////////////////////

    //! Set the interval at which confluence is checked.
    //!
    //! The function \ref run periodically checks if
    //! the system is already confluent. This function can be used to
    //! set how frequently this happens, it is the number of new overlaps
    //! that should be considered before checking confluence. Setting this
    //! value too low can adversely affect the performance of
    //! \ref run.
    //!
    //! The default value is \c 4096, and should be set to
    //! \ref LIMIT_MAX if \ref run should never
    //! check if the system is already confluent.
    //!
    //! \param val the new value of the interval.
    //!
    //! \returns
    //! A reference to \c *this.
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa \ref run.
    KnuthBendix& check_confluence_interval(size_t val) {
      _settings._check_confluence_interval = val;
      return *this;
    }

    //! Set the maximum length of overlaps to be considered.
    //!
    //! This function can be used to specify the maximum length of the
    //! overlap of two left hand sides of rules that should be considered in
    //! \ref run.
    //!
    //! If this value is less than the longest left hand side of a rule, then
    //! \ref run can terminate without the system being
    //! confluent.
    //!
    //! \param val the new value of the maximum overlap length.
    //!
    //! \returns
    //! A reference to \c *this.
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa \ref run.
    KnuthBendix& max_overlap(size_t val) {
      _settings._max_overlap = val;
      return *this;
    }

    //! Set the maximum number of rules.
    //!
    //! This member function sets the (approximate) maximum number of rules
    //! that the system should contain. If this is number is exceeded in
    //! calls to \ref run or
    //! knuth_bendix_by_overlap_length, then they
    //! will terminate and the system may not be confluent.
    //!
    //! By default this value is \ref POSITIVE_INFINITY.
    //!
    //! \param val the maximum number of rules.
    //!
    //! \returns
    //! A reference to \c *this.
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa \ref run.
    KnuthBendix& max_rules(size_t val) {
      _settings._max_rules = val;
      return *this;
    }

    //! Set the overlap policy.
    //!
    //! This function can be used to determine the way that the length
    //! of an overlap of two words in the system is measured.
    //!
    //! \param val the maximum number of rules.
    //!
    //! \returns
    //! A reference to \c *this.
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa options::overlap.
    KnuthBendix& overlap_policy(options::overlap val);

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendix - member functions for rules and rewriting - public
    //////////////////////////////////////////////////////////////////////////

    //! Returns the current number of active rules in the KnuthBendix
    //! instance.
    //!
    //! \returns
    //! The current number of active rules, a value of type `size_t`.
    //!
    //! \exceptions
    //! \noexcept
    //!
    //! \complexity
    //! Constant.
    //!
    //! \parameters
    //! (None)
    size_t number_of_active_rules() const noexcept;

    //! Returns a copy of the active rules.
    //!
    //! This member function returns a vector consisting of the pairs of
    //! strings which represent the rules of the KnuthBendix instance. The \c
    //! first entry in every such pair is greater than the \c second according
    //! to the reduction ordering of the KnuthBendix instance. The rules are
    //! sorted according to the reduction ordering used by the rewriting
    //! system, on the first entry.
    //!
    //! \returns
    //! A copy of the currently active rules, a value of type
    //! `std::vector<rule_type>`.
    //!
    //! \complexity
    //! \f$O(n)\f$ where \f$n\f$ is the sum of the lengths of the words in
    //! rules of \p copy.
    //!
    //! \parameters
    //! (None)
    // TODO(v3): update the doc, now returns a Range
    auto active_rules() const {
      using namespace rx;
      return iterator_range(_active_rules.cbegin(), _active_rules.cend())
             | transform([this](auto const& rule) {
                 // TODO remove allocation
                 internal_string_type lhs = internal_string_type(*rule->lhs());
                 internal_string_type rhs = internal_string_type(*rule->rhs());
                 internal_to_external_string(lhs);
                 internal_to_external_string(rhs);
                 return std::make_pair(lhs, rhs);
               });
    }

    //! Rewrite a word in-place.
    //!
    //! The word \p w is rewritten in-place according to the current active
    //! rules in the KnuthBendix instance.
    //!
    //! \param w the word to rewrite.
    //!
    //! \returns
    //! The argument \p w after it has been rewritten.
    // TODO(later) change to void rewrite(std::string&);
    std::string* rewrite(std::string* w) const;

    //! Rewrite a word.
    //!
    //! Rewrites a copy of the word \p w rewritten according to the current
    //! rules in the KnuthBendix instance.
    //!
    //! \param w the word to rewrite.
    //!
    //! \returns
    //! A copy of the argument \p w after it has been rewritten.
    std::string rewrite(std::string w) const {
      rewrite(&w);
      return w;
    }

    //////////////////////////////////////////////////////////////////////////
    // KnuthBendix - main member functions - public
    //////////////////////////////////////////////////////////////////////////

    //! Check confluence of the current rules.
    //!
    //! \returns \c true if the KnuthBendix instance is
    //! [confluent](https://w.wiki/9DA) and \c false if it is not.
    //!
    //! \parameters
    //! (None)
    bool confluent() const;
    bool confluent_known() const noexcept;

    //! Run the Knuth-Bendix by considering all overlaps of a given length.
    //!
    //! This function runs the Knuth-Bendix algorithm on the rewriting
    //! system represented by a KnuthBendix instance by considering all
    //! overlaps of a given length \f$n\f$ (according to the \ref
    //! options::overlap) before those overlaps of length \f$n + 1\f$.
    //!
    //! \returns
    //! (None)
    //!
    //! \complexity
    //! See warning.
    //!
    //! \warning This will terminate when the KnuthBendix instance is
    //! confluent, which might be never.
    //!
    //! \sa \ref run.
    //!
    //! \parameters
    //! (None)
    void knuth_bendix_by_overlap_length();

    //! Returns the Gilman digraph.
    //!
    //! \returns A const reference to a \ref ActionDigraph.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \warning This will terminate when the KnuthBendix instance is
    //! reduced and confluent, which might be never.
    //!
    //! \sa \ref number_of_normal_forms,
    //! \ref cbegin_normal_forms, and \ref cend_normal_forms.
    //!
    //! \parameters
    //! (None)
    ActionDigraph<size_t> const& gilman_digraph();

    //////////////////////////////////////////////////////////////////////////
    // TODO - pure virtual member functions - public
    //////////////////////////////////////////////////////////////////////////

    //! \copydoc FpSemigroupInterface::size
    //!
    //! \note If \c this has been run until finished, then this function can
    //! determine the size of the semigroup represented by \c this even if
    //! it is infinite. Moreover, the complexity of this function is at
    //! worst \f$O(mn)\f$ where \f$m\f$ is the number of letters in the
    //! alphabet, and \f$n\f$ is the number of nodes in the \ref
    //! gilman_digraph.
    uint64_t size();

    bool equal_to(std::string const&, std::string const&);

    std::string normal_form(std::string const& w);

   private:
    void add_rule_impl(std::string const& p, std::string const& q);
    void add_rule(Rule* rule);

    void internal_rewrite(internal_string_type* u) const;

    static internal_string_type word_to_internal_string(word_type const& u);
    static size_t               internal_char_to_uint(internal_char_type c);
    static internal_char_type   uint_to_internal_char(size_t a);
    static internal_string_type uint_to_internal_string(size_t i);
    static word_type internal_string_to_word(internal_string_type const& s);

    static internal_string_type*
    word_to_internal_string(word_type const& w, internal_string_type* ww);

    internal_char_type external_to_internal_char(external_char_type c) const;
    external_char_type internal_to_external_char(internal_char_type a) const;
    void external_to_internal_string(external_string_type& w) const;
    void internal_to_external_string(internal_string_type& w) const;

    Rule* new_rule() const;
    Rule* new_rule(internal_string_type* lhs, internal_string_type* rhs) const;
    Rule* new_rule(Rule const* rule1) const;
    Rule* new_rule(internal_string_type::const_iterator begin_lhs,
                   internal_string_type::const_iterator end_lhs,
                   internal_string_type::const_iterator begin_rhs,
                   internal_string_type::const_iterator end_rhs) const;

    void push_stack(Rule* rule);
    void overlap(Rule const* u, Rule const* v);
    void clear_stack();

    std::list<Rule const*>::iterator
    remove_rule(std::list<Rule const*>::iterator it);

#ifdef LIBSEMIGROUPS_VERBOSE
    //////////////////////////////////////////////////////////////////////////
    // ./configure --enable-verbose functions
    //////////////////////////////////////////////////////////////////////////

    size_t max_active_word_length();
#endif

    //////////////////////////////////////////////////////////////////////////
    // Runner - pure virtual member functions - private
    //////////////////////////////////////////////////////////////////////////

    void run_impl();
    bool finished_impl() const;
  };

  //! This friend function allows a KnuthBendix object to be left shifted
  //! into a std::ostream, such as std::cout. The currently active rules
  //! of the system are represented in the output.
  std::ostream& operator<<(std::ostream&, KnuthBendix const&);

  namespace knuth_bendix {

    //! Returns a forward iterator pointing at the first normal form with
    //! length in a given range.
    //!
    //! If incremented, the iterator will point to the next least short-lex
    //! normal form (if it's less than \p max in length).  Iterators of the
    //! type returned by this function should only be compared with other
    //! iterators created from the same KnuthBendix instance.
    //!
    //! \param lphbt the alphabet to use for the normal forms
    //! \param min the minimum length of a normal form
    //! \param max one larger than the maximum length of a normal form.
    //!
    //! \returns
    //! A value of type \ref const_normal_form_iterator.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \warning
    //! Copying iterators of this type is relatively expensive.  As a
    //! consequence, prefix incrementing \c ++it the iterator \c it returned
    //! by \c cbegin_normal_forms is significantly cheaper than postfix
    //! incrementing \c it++.
    //!
    //! \warning
    //! If the finitely presented semigroup represented by \c this is
    //! infinite, then \p max should be chosen with some care.
    //!
    //! \sa
    //! \ref cend_normal_forms.
    // TODO update doc
    inline auto normal_forms(KnuthBendix& kb) {
      using namespace rx;
      Paths paths(kb.gilman_digraph());
      paths.from(0);
      return paths;
    }
  }  // namespace knuth_bendix

  namespace presentation {

    //! Return an iterator pointing at the left hand side of a redundant rule.
    //!
    //! This function is defined in ``knuth-bendix.hpp``.
    //!
    //! Starting with the last rule in the presentation, this function
    //! attempts to run the Knuth-Bendix algorithm on the rules of the
    //! presentation except for the given omitted rule. For every such omitted
    //! rule, Knuth-Bendix is run for the length of time indicated by the
    //! second parameter \p t, and then it is checked if the omitted rule can
    //! be shown to be redundant (rewriting both sides of the omitted rule
    //! using the other rules using the output of the, not necessarily
    //! finished, Knuth-Bendix algorithm).
    //!
    //! If the omitted rule can be shown to be redundant in this way, then an
    //! iterator pointing to its left hand side is returned.
    //!
    //! If no rule can be shown to be redundant in this way, then an iterator
    //! pointing to `p.cend()` is returned.
    //!
    //! \tparam T type of the 2nd parameter (time to try running
    //! Knuth-Bendix). \param p the presentation \param t time to run
    //! KnuthBendix for every omitted rule
    //!
    //! \warning The progress of the Knuth-Bendix algorithm may differ between
    //! different calls to this function even if the parameters are identical.
    //! As such this is non-deterministic, and may produce different results
    //! with the same input.
    template <typename T>
    auto redundant_rule(Presentation<std::string> const& p, T t) {
      // TODO reuse the same KnuthBendix
      p.validate();
      Presentation<std::string> q;
      q.alphabet(p.alphabet());
      for (auto omit = p.rules.crbegin(); omit != p.rules.crend(); omit += 2) {
        q.rules.clear();
        q.rules.insert(q.rules.end(), p.rules.crbegin(), omit);
        q.rules.insert(q.rules.end(), omit + 2, p.rules.crend());
        KnuthBendix kb(q);
        kb.run_for(t);
        if (kb.rewrite(*omit) == kb.rewrite(*(omit + 1))) {
          return (omit + 1).base() - 1;
        }
      }
      return p.rules.cend();
    }

    //! Return an iterator pointing at the left hand side of a redundant rule.
    //!
    //! This function is defined in ``knuth-bendix.hpp``.
    //!
    //! Starting with the last rule in the presentation, this function
    //! attempts to run the Knuth-Bendix algorithm on the rules of the
    //! presentation except for the given omitted rule. For every such omitted
    //! rule, Knuth-Bendix is run for the length of time indicated by the
    //! second parameter \p t, and then it is checked if the omitted rule can
    //! be shown to be redundant (rewriting both sides of the omitted rule
    //! using the other rules using the output of the, not necessarily
    //! finished, Knuth-Bendix algorithm).
    //!
    //! If the omitted rule can be shown to be redundant in this way, then an
    //! iterator pointing to its left hand side is returned.
    //!
    //! If no rule can be shown to be redundant in this way, then an iterator
    //! pointing to `p.cend()` is returned.
    //!
    //! \tparam W type of words in the Presentation
    //! \tparam T type of the 2nd parameter (time to try running
    //! Knuth-Bendix). \param p the presentation \param t time to run
    //! KnuthBendix for every omitted rule
    //!
    //! \warning The progress of the Knuth-Bendix algorithm may differ between
    //! different calls to this function even if the parameters are identical.
    //! As such this is non-deterministic, and may produce different results
    //! with the same input.
    template <typename W, typename T>
    auto redundant_rule(Presentation<W> const& p, T t) {
      auto pp = to_presentation<std::string>(p);
      return p.rules.cbegin()
             + std::distance(pp.rules.cbegin(), redundant_rule(pp, t));
    }
  }  // namespace presentation
}  // namespace libsemigroups
#endif  // LIBSEMIGROUPS_KNUTH_BENDIX_NEW_HPP_
