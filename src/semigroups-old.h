/*
 * Semigroups++
 *
 * This file contains the Froidure-Pin algorithm for arbitrary semigroups.
 *
 */

// TODO
// 0) move the methods to the cc file
// 1) the other functionality of Semigroupe.
// 2) remove templates as far as possible.

#ifndef SEMIGROUPS_H
#define SEMIGROUPS_H 1

//#define NDEBUG
//#define DEBUG

#include "basics.h"
#include "elements.h"

#include <algorithm>
#include <assert.h>
#include <iostream>
#include <unordered_map>
#include <vector>

#include <mutex>
#include <thread>

typedef size_t              Letter;
typedef std::vector<Letter> Word;
typedef std::pair<BucketId, size_t> Position;
typedef RecVec<Position> CayleyGraph;

static std::mutex mtx;
// TODO rename this, when we have namespaces
static Position UNDEFINED_P = make_pair(-1, -1);

static bool comp(std::vector<Element*> vec1, std::vector<Element*> vec2) {
  return vec1.size() < vec2.size();
}

class Semigroup {

  typedef RecVec<unsigned char> Flags;

 public:
  Semigroup& operator=(Semigroup const&) = delete;

  class Bucket {
    friend Semigroup;

   public:
    Bucket()                   = delete;
    Bucket(Bucket const& copy) = delete;

    Bucket(Semigroup* semigroup, size_t bid)
        : _elements(new std::vector<Element*>()),
          _final(),
          _first(),
          _index(),
          _left(new CayleyGraph(semigroup->nrgens(), 0, UNDEFINED_P)),
          _length(),
          _map(),
          _multiplied(),
          _nr(0),
          _nr_shorter(0),
          _pos(0),
          _prefix(),
          _reduced(semigroup->nrgens()),
          _right(new CayleyGraph(semigroup->nrgens(), 0, UNDEFINED_P)),
          _semigroup(semigroup),
          _suffix(),
          _tmp_product(semigroup->gens()->at(0)->identity()),
          _wordlen(0),  // (length of the current word) - 1

          _bucket_id(bid),
          _queue_elements(_semigroup->_nr_threads, std::vector<Element*>()),
          _queue_pos(_semigroup->_nr_threads, std::vector<Position>()),
          _queue_gen(_semigroup->_nr_threads, std::vector<Letter>()),
          _queue_first(_semigroup->_nr_threads, std::vector<Letter>()),
          _queue_suffix(_semigroup->_nr_threads, std::vector<Position>()) {
      _lenindex.push_back(0);
      for (auto queue : _queue_elements) {
        queue.reserve(_semigroup->batch_size());
      }
      for (auto queue : _queue_pos) {
        queue.reserve(_semigroup->batch_size());
      }
      for (auto queue : _queue_gen) {
        queue.reserve(_semigroup->batch_size());
      }
      for (auto queue : _queue_first) {
        queue.reserve(_semigroup->batch_size());
      }
      for (auto queue : _queue_suffix) {
        queue.reserve(_semigroup->batch_size());
      }
#ifdef NDEBUG
      assert(false);
#endif
    }

    ~Bucket() {
      _tmp_product->really_delete();
      delete _tmp_product;

      delete _left;
      delete _right;

      for (Element* x : *_elements) {
        x->really_delete();
        delete x;
      }
      delete _elements;
    }

    BucketId bucket_id() const {
      return _bucket_id;
    }

    size_t nr_products() const {
      return _nr_products;
    }

    bool is_done() const {
      return (_pos >= _nr);
    }

    size_t max_queue_length() const {
      return (std::max_element(
                  _queue_elements.begin(), _queue_elements.end(), comp))
          ->size();
    }

    void apply_generators(size_t limit) {

      bool   stop               = false;
      size_t total_queue_length = 0;
      while (_pos < _lenindex.at(_wordlen + 1)
             && _queue_elements[0].size() < _semigroup->_batch_size) {
        size_t   i        = _index.at(_pos);
        size_t   b        = _first.at(i);
        Position s        = _suffix.at(i);
        _multiplied.at(i) = true;
        for (size_t j = 0; j < _semigroup->_nrgens; j++) {
          Position r;
          // reduced_get is OK here since s is shorter.
          if (_wordlen > 0 && !reduced_get(s, j)) {
            r = right_get(s, j);
            if (_semigroup->_found_one && r == _semigroup->_pos_one) {
              _right->set(i, j, _semigroup->_genslookup.at(b));
              continue;
              //} else if (prefix_get(r) != UNDEFINED) {
            } else if (length_get(r) > 1) {
              Position w = left_get(prefix_get(r), b);
              if (w.first == _bucket_id
                  && _right->get(w.second, final_get(r)) != UNDEFINED_P) {
                _right->set(i, j, _right->get(w.second, final_get(r)));
                continue;
              } else if (length_get(w) < _wordlen + 1) {
                _right->set(i, j, right_get(w, final_get(r)));
                continue;
              }
            } else {
              _right->set(
                  i, j, right_get(_semigroup->_genslookup.at(b), final_get(r)));
              continue;
            }
          }
          _nr_products++;
          _tmp_product->redefine(_elements->at(i), _semigroup->_gens->at(j));
          // the bucket which should contain _tmp_product
          size_t bid = _tmp_product->hash_value() % _semigroup->_nr_threads;

          auto it = _semigroup->_buckets[bid]->_map.find(_tmp_product);

          if (it != _semigroup->_buckets[bid]->_map.end()) {
            _right->set(i, j, make_pair(bid, it->second));
            //_semigroup->_nrrules++;
          } else {
            Position pair = make_pair(_bucket_id, i);
            _queue_elements[bid].push_back(_tmp_product->really_copy());
            _queue_pos[bid].push_back(pair);
            _queue_gen[bid].push_back(j);
            _queue_first[bid].push_back(_first.at(i));

            if (_wordlen > 0) {  // _elements[i] is not a generator
              _queue_suffix[bid].push_back(right_get(s, j));
            } else {
              _queue_suffix[bid].push_back(_semigroup->_genslookup.at(j));
            }
          }
        }  // finished applying gens to <_elements->at(pos)>
        _pos++;
      }  // finished words of length <wordlen> + 1
      // stop = (_nr >= limit);
    }

    void process_queue() {

      for (auto bucket : _semigroup->_buckets) {
        for (size_t k = 0; k < bucket->_queue_elements[_bucket_id].size();
             k++) {
          Element* x = bucket->_queue_elements[_bucket_id].at(k);
          Position i = bucket->_queue_pos[_bucket_id].at(k);
          Letter   j = bucket->_queue_gen[_bucket_id].at(k);

          auto it = _map.find(x);

          if (it != _map.end()) {
            right_set(i, j, make_pair(_bucket_id, it->second));
            //_semigroup->_nrrules++;
          } else {

            Position pair = make_pair(_bucket_id, _nr);
            _semigroup->is_one(x, pair);

            // things maybe in different bucket - NOT OK to write to directly
            // we can't use _buckets[whatever]._first(i) etc since another
            // thread might be writing to it.
            _first.push_back(bucket->_queue_first[_bucket_id].at(k));
            _suffix.push_back(bucket->_queue_suffix[_bucket_id].at(k));

            // things maybe in different bucket - OK to write to directly
            // no reallocation can take place since <i> represents a
            // shorter word/element and no other thread can be writing to
            // the same position.
            reduced_set(i, j, 1);
            right_set(i, j, pair);

            // things in this bucket
            _elements->push_back(x);
            _final.push_back(j);
            _index.push_back(_nr);
            _length.push_back(_wordlen + 2);
            _map.insert(std::make_pair(_elements->back(), _nr));
            _prefix.push_back(i);
            _nr++;
          }
        }
        bucket->_queue_elements[_bucket_id].clear();
        bucket->_queue_pos[_bucket_id].clear();
        bucket->_queue_gen[_bucket_id].clear();
        bucket->_queue_first[_bucket_id].clear();
        bucket->_queue_suffix[_bucket_id].clear();
      }
    }

    // have to process left_cayley_graph separately since it relies on
    // the right Cayley graph being fully known for words up to (and
    // including) the current length.

    void process_left_cayley_graph() {
      // fill in left Cayley table entries
      // if (_pos > _nr || _pos == _lenindex.at(_wordlen + 1)) {
      // TODO reintroduce this if-condition
      if (_wordlen > 0) {
        for (size_t i = _lenindex.at(_wordlen); i < _pos; i++) {
          Position p = _prefix.at(_index.at(i));
          Letter   b = _final.at(_index.at(i));
          for (size_t j = 0; j < _semigroup->_nrgens; j++) {
            _left->set(_index.at(i), j, right_get(left_get(p, j), b));
          }
        }
      } else {
        for (size_t i = 0; i < _pos; i++) {
          Letter b = _final.at(_index.at(i));
          for (size_t j = 0; j < _semigroup->_nrgens; j++) {
            _left->set(
                _index.at(i), j, right_get(_semigroup->_genslookup.at(j), b));
          }
        }
      }
    }

    // only use this if really sure x is not already in this bucket
    void insert_gen(Letter i) {
      Position pos = make_pair(_bucket_id, _nr);
      _semigroup->is_one(_semigroup->_gens->at(i), pos);
      _semigroup->_genslookup.push_back(pos);

      _elements->push_back(_semigroup->_gens->at(i));
      _first.push_back(i);
      _final.push_back(i);
      _length.push_back(1);
      _map.insert(std::make_pair(_elements->back(), _nr));
      _prefix.push_back(UNDEFINED_P);
      _suffix.push_back(UNDEFINED_P);
      _index.push_back(_nr);
      _nr++;
    }

    void inline expand(bool increase_wordlen = true) {
      if (increase_wordlen) {
        _wordlen++;
      }
      _left->add_rows(_nr - _nr_shorter);
      _reduced.add_rows(_nr - _nr_shorter);
      _right->add_rows(_nr - _nr_shorter);
      _multiplied.resize(_multiplied.size() + _nr - _nr_shorter, false);
      _lenindex.push_back(_index.size());
      _nr_shorter = _nr;
    }

   private:
    std::vector<Element*>* _elements;
    std::vector<size_t>    _final;
    std::vector<size_t>    _first;
    std::vector<size_t>    _index;
    CayleyGraph*           _left;
    std::vector<size_t>    _length;
    std::unordered_map<const Element*, size_t, hash<const Element*>, myequal>
                        _map;
    std::vector<size_t> _lenindex;
    std::vector<bool>   _multiplied;
    size_t              _nr;
    size_t              _nr_shorter;
    size_t              _pos;
    std::vector<std::pair<size_t, size_t>> _prefix;
    Flags        _reduced;
    CayleyGraph* _right;
    std::vector<std::pair<size_t, size_t>> _suffix;
    Element* _tmp_product;
    size_t   _wordlen;

    Semigroup* _semigroup;
    size_t     _bucket_id;

    std::vector<std::vector<Element*>> _queue_elements;
    std::vector<std::vector<Position>> _queue_pos;
    std::vector<std::vector<Letter>>   _queue_gen;
    std::vector<std::vector<Letter>>   _queue_first;
    std::vector<std::vector<Position>> _queue_suffix;

    size_t _nr_products;

    inline bool reduced_get(Position const& pair, size_t gen) {
      return _semigroup->_buckets[pair.first]->_reduced.get(pair.second, gen);
    }

    inline void reduced_set(Position const& pair, size_t j, size_t k) {
      // mtx.lock();
      _semigroup->_buckets[pair.first]->_reduced.set(pair.second, j, k);
      // mtx.unlock();
    }

    inline size_t final_get(Position const& pair) {
      return _semigroup->_buckets[pair.first]->_final[pair.second];
    }

    inline Position left_get(Position const& pair, size_t gen) {
      return _semigroup->_buckets[pair.first]->_left->get(pair.second, gen);
    }

    inline Position right_get(Position const& pair, size_t gen) {
      return _semigroup->_buckets[pair.first]->_right->get(pair.second, gen);
    }

    inline void right_set(Position const& i, size_t j, Position const& k) {

      _semigroup->_buckets[i.first]->_right->set(i.second, j, k);
    }

    inline Position prefix_get(Position const& pair) {
      return _semigroup->_buckets[pair.first]->_prefix.at(pair.second);
    }

    inline size_t length_get(Position const& pair) {
      return _semigroup->_buckets[pair.first]->_length[pair.second];
    }

    inline Position suffix_get(Position const& pair) {
      return _semigroup->_buckets[pair.first]->_suffix.at(pair.second);
    }
  };

 public:
  /*******************************************************************************
  ********************************************************************************
   * Temporary . . .
  ********************************************************************************
  *******************************************************************************/

  inline bool find(BucketId bid, Element* x) const {
    // size_t bid = x->hash_value() % _nr_threads;
    return _buckets[bid]->_map.find(x) != _buckets[bid]->_map.end();
  }

  /*inline void insert (Element* x) {
    size_t bid = x->hash_value() % _nr_threads;
    _buckets[bid]._map->insert(make_pair(x, make_pair(bid, bucket[bid]._nr)));

  }*/

  /*******************************************************************************
  ********************************************************************************
   * Constructors & destructors. . .
  ********************************************************************************
  *******************************************************************************/

  /*******************************************************************************
   * Construct from generators . . .
  *******************************************************************************/

  Semigroup(std::vector<Element*>* gens, size_t degree, size_t nr_threads)
      : _batch_size(8192),
        _degree(degree),
        _duplicate_gens(),
        _found_one(false),
        _gens(new std::vector<Element*>()),
        _genslookup(),
        _nrgens(gens->size()),
        _nr_idempotents(0),
        _nrrules(0),
        _nr_threads(nr_threads),
        _pos_one(UNDEFINED_P)
  //_relation_pos  (-1),
  //_relation_gen  (0),
  {
    assert(_nrgens != 0);

    for (Element* x : *gens) {
      _gens->push_back(x->really_copy());
    }
    _id = _gens->at(0)->identity();

    for (size_t i = 0; i < _nr_threads; i++) {
      _buckets.push_back(new Bucket(this, i));
    }

    //_lenindex.push_back(0);

    // add the generators
    for (size_t i = 0; i < _nrgens; i++) {
      size_t bid = _gens->at(i)->hash_value() % _nr_threads;
      auto   it  = _buckets[bid]->_map.find(_gens->at(i));
      if (it != _buckets[bid]->_map.end()) {  // duplicate generator
        _genslookup.push_back(make_pair(bid, it->second));
        _nrrules++;
        _duplicate_gens.push_back(make_pair(i, make_pair(bid, it->second)));
      } else {
        _buckets[bid]->insert_gen(i);
      }
    }
    expand_buckets(false);
  }

  void expand_buckets(bool increase_wordlen = true) {
    for (size_t bid = 0; bid < _buckets.size(); bid++) {
      _buckets[bid]->expand(increase_wordlen);
    }
  }

  size_t current_size() {
    size_t size = 0;
    for (size_t i = 0; i < _buckets.size(); i++) {
      size += _buckets[i]->_nr;
    }
    return size;
  }

  size_t current_word_length() {
    size_t wordlen;
    for (size_t bid = 0; bid < _buckets.size(); bid++) {
      if (_buckets[bid]->_wordlen > wordlen) {
        wordlen = _buckets[bid]->_wordlen;
      }
    }
    return wordlen;
  }

  bool is_done() {
    size_t wordlen;
    for (auto bucket : _buckets) {
      if (!bucket->is_done()) {
        return false;
      }
    }
    return true;
  }

  /*******************************************************************************
   *
  *******************************************************************************/

  inline void apply_generators(size_t limit, size_t i) {
    _buckets[i]->apply_generators(limit);
  }

  inline void process_queue(size_t i) {
    _buckets[i]->process_queue();
  }

  inline void process_left_cayley_graph(size_t i) {
    _buckets[i]->process_left_cayley_graph();
  }

  inline void expand_bucket(size_t i) {
    _buckets[i]->expand();
  }

  size_t nr_products() {
    size_t nr = 0;
    for (auto bucket : _buckets) {
      nr += bucket->nr_products();
    }
    return nr;
  }

  void enumerate(size_t limit, bool report) {
    // if (_pos >= _nr || limit <= _nr) return;
    // limit = std::max(limit, _nr + _batch_size);

    if (report) {
      std::cout << "semigroups++: enumerate" << std::endl;
      std::cout << "limit      = " << limit << std::endl;
      std::cout << "batch_size = " << _batch_size << std::endl;
      std::cout << "nr_threads = " << _nr_threads + 1 << std::endl;
      unsigned int n = std::thread::hardware_concurrency();
      std::cout << "hardware supports " << n << " concurrent threads!!!"
                << std::endl
                << std::endl;
    }

    // multiply the words of length > 1 by every generator
    // bool stop = (_nr >= limit);

    std::thread* threads = new std::thread[_nr_threads];

    while (!is_done()) {
      for (size_t i = 0; i < _nr_threads; i++) {
        threads[i] = std::thread(&Semigroup::apply_generators, this, limit, i);
      }

      for (size_t i = 0; i < _nr_threads; i++) {
        threads[i].join();
      }

      if (report) {
        for (size_t i = 0; i < _nr_threads; i++) {
          std::cout << "bucket " << i << " contains " << _buckets[i]->_nr
                    << " elements\n";
          for (size_t j = 0; j < _nr_threads; j++) {
            std::cout << "bucket " << i << " queue for bucket " << j << " has "
                      << _buckets[i]->_queue_elements[j].size()
                      << " elements\n";
          }
          std::cout << "\n";
        }
      }

      for (size_t i = 0; i < _nr_threads; i++) {
        threads[i] = std::thread(&Semigroup::process_queue, this, i);
      }

      for (size_t i = 0; i < _nr_threads; i++) {
        threads[i].join();
      }

      bool move_on = true;

      for (auto bucket : _buckets) {
        if (bucket->_pos != bucket->_lenindex.at(bucket->_wordlen + 1)) {
          move_on = false;
          break;
        }
      }
      if (move_on) {
        for (size_t i = 0; i < _nr_threads; i++) {
          threads[i]
              = std::thread(&Semigroup::process_left_cayley_graph, this, i);
        }

        for (size_t i = 0; i < _nr_threads; i++) {
          threads[i].join();
        }

        for (size_t i = 0; i < _nr_threads; i++) {
          threads[i] = std::thread(&Semigroup::expand_bucket, this, i);
        }

        for (size_t i = 0; i < _nr_threads; i++) {
          threads[i].join();
        }

        if (report) {
          std::cout << "found " << current_size() << " elements, ";
          std::cout << _nrrules << " rules, ";
          // std::cout << "max word length " << current_max_word_length();
          if (!is_done()) {
            std::cout << ", so far" << std::endl << std::endl << std::endl;
          } else {
            std::cout << ", finished!" << std::endl;
          }
        }
      }
    }
    if (report) {
      std::cout << "total number of products = " << nr_products() << std::endl;
    }
  }

  /*******************************************************************************
   * Copy . . .
  *******************************************************************************/

  /*Semigroup (const Semigroup& copy)
    : _batch_size    (copy._batch_size),
      _degree        (copy._degree),
      _duplicate_gens(copy._duplicate_gens),
      _elements      (new std::vector<Element*>()),
      _final         (copy._final),
      _first         (copy._first),
      _found_one     (copy._found_one),
      _genslookup    (copy._genslookup),
      _id            (copy._id->really_copy()),
      _index         (copy._index),
      _left          (copy._left),
      _lenindex      (copy._lenindex),
      _length        (copy._length),
      _multiplied    (copy._multiplied),
      _nr            (copy._nr),
      _nrgens        (copy._nrgens),
      _nr_idempotents(copy._nr_idempotents),
      _nrrules       (copy._nrrules),
      _pos           (copy._pos),
      _pos_one       (copy._pos_one),
      _prefix        (copy._prefix),
      _reduced       (copy._reduced),
      _relation_pos  (copy._relation_pos),
      _relation_gen  (copy._relation_gen),
      _right         (copy._right),
      _suffix        (copy._suffix),
      _wordlen       (copy._wordlen)
  {
    _elements->reserve(_nr);
    _map.reserve(_nr);
    _tmp_product = copy._id->really_copy();

    for (Element* x: *_gens) {
      _gens->push_back(x->really_copy());
    }

    for (size_t i = 0; i < copy._elements->size(); i++) {
      _elements->push_back(copy._elements->at(i)->really_copy());
      _map.insert(std::make_pair(_elements->back(), i));
    }
  }*/

  /*******************************************************************************
   * Construct from semigroup and additional generators . . .
  *******************************************************************************/
  // TODO change to Semigroup*
  /*Semigroup (const Semigroup& copy, std::vector<Element*>* coll, bool report)
    : _batch_size     (copy._batch_size),
      _degree         (copy._degree),    // copy for comparison in
  add_generators
      _duplicate_gens (copy._duplicate_gens),
      _elements       (new std::vector<Element*>()),
      _found_one      (copy._found_one), // copy in case degree doesn't change
  in add_generators
      _gens           (new std::vector<Element*>()),
      _genslookup     (copy._genslookup),
      _left           (new CayleyGraph(copy._left)),
      _multiplied     (copy._multiplied),
      _nr             (copy._nr),
      _nrgens         (copy._nrgens),
      _nr_idempotents (0),
      _nrrules        (0),
      _pos            (copy._pos),
      _pos_one        (copy._pos_one),   // copy in case degree doesn't change
  in add_generators
      _relation_pos   (-1),
      _relation_gen   (0),
      _reduced        (copy._reduced),
      _right          (new CayleyGraph(copy._right)),
      _wordlen        (0)
  {
    assert(!coll->empty());

    _elements->reserve(copy._nr);
    _map.reserve(copy._nr);

    // the following are required for assignment to specific positions in
    // add_generators
    _final.resize(copy._nr, 0);
    _first.resize(copy._nr, 0);
    _length.resize(copy._nr, 0);
    _prefix.resize(copy._nr, 0);
    _suffix.resize(copy._nr, 0);

    std::unordered_set<Element*> new_gens;

    // remove duplicate generators
    for (Element* x: *coll) {
      assert(x->degree() == coll->at(0)->degree());
      new_gens.insert(x->really_copy());
      // copy here so that after add_generators, the semigroup is responsible
      // for the destruction of gens.
    }

    assert((*new_gens.begin())->degree() >= copy.degree());

    size_t deg_plus = (*new_gens.begin())->degree() - copy.degree();

    if (deg_plus != 0) {
      _degree += deg_plus;
      _found_one = false;
      _pos_one = UNDEFINED;
    }

    _lenindex.push_back(0);
    _lenindex.push_back(copy._lenindex.at(1));
    _index.reserve(copy._nr);

    // add the distinct old generators to new _index
    for (size_t i = 0; i < copy._lenindex.at(1); i++) {
      _index.push_back(copy._index.at(i));
      _final.at(_index.at(i)) = i;
      _first.at(_index.at(i)) = i;
      _prefix.at(_index.at(i)) = -1;
      _suffix.at(_index.at(i)) = -1;
      _length.at(_index.at(i)) = 1;
    }

    for (size_t i = 0; i < copy.nrgens(); i++) {
      _gens->push_back(copy._gens->at(i)->really_copy(deg_plus));
    }

    _id          = copy._id->really_copy(deg_plus);
    _tmp_product = copy._id->really_copy(deg_plus);

    for (size_t i = 0; i < copy._elements->size(); i++) {
      _elements->push_back(copy._elements->at(i)->really_copy(deg_plus));
      _map.insert(std::make_pair(_elements->back(), i));
      is_one(_elements->back(), i);
    }

    add_generators(new_gens, report);
  }*/

  /*******************************************************************************
   * Destructor . . .
  *******************************************************************************/

  ~Semigroup() {
    for (auto bucket : _buckets) {
      delete bucket;
    }
    _id->really_delete();
    delete _id;
  }

  /*******************************************************************************
  ********************************************************************************
   * Const methods . . .
  ********************************************************************************
  *******************************************************************************/

  /*******************************************************************************
   * current_max_word_length: get the maximum length of a current word!
  *******************************************************************************/

  /*size_t current_max_word_length () const {
    if (is_done()) {
      return _lenindex.size() - 2;
    } else if (_nr > _lenindex.back()) {
      return _lenindex.size();
    } else {
      return _lenindex.size() - 1;
    }
  }*/

  /*******************************************************************************
   * degree: get the degree of the elements in the semigroup
  *******************************************************************************/

  size_t degree() const {
    return _degree;
  }

  /*******************************************************************************
   * nrgens: get the number of generators of the semigroup
  *******************************************************************************/

  size_t nrgens() const {
    return _gens->size();
  }

  /*******************************************************************************
   * gens: get the generators of the semigroup
  *******************************************************************************/

  std::vector<Element*>* gens() const {
    return _gens;
  }

  /*******************************************************************************
   * is_done: returns true if the semigroup is fully enumerated and false if not
  *******************************************************************************/

  /*bool is_done () const {
    return (_pos >= _nr);
  }*/

  /*******************************************************************************
   * is_begun: returns true if no elements (other than the generators) have
   * been enumerated
  *******************************************************************************/

  /*bool is_begun () const {
    assert(_lenindex.size() > 1);
    return (_pos >= _lenindex.at(1));
  }*/

  /*******************************************************************************
   * current_size: the number of elements enumerated so far
  *******************************************************************************/

  /*size_t current_size () const {
    return _elements->size();
  }*/

  /*******************************************************************************
   * current_nrrules:
  *******************************************************************************/

  size_t current_nrrules() const {
    return _nrrules;
  }

  /*******************************************************************************
   * prefix:
  *******************************************************************************/

  /*size_t prefix (size_t element_nr) const {
    assert(element_nr < _nr);
    return _prefix.at(element_nr);
  }*/

  /*******************************************************************************
   * suffix:
  *******************************************************************************/

  /*size_t suffix (size_t element_nr) const {
    assert(element_nr < _nr);
    return _suffix.at(element_nr);
  }*/

  /*******************************************************************************
   * first_letter:
  *******************************************************************************/

  /*size_t first_letter (size_t element_nr) const {
    assert(element_nr < _nr);
    return _first.at(element_nr);
  }*/

  /*******************************************************************************
   * final_letter:
  *******************************************************************************/

  /*size_t final_letter (size_t element_nr) const {
    assert(element_nr < _nr);
    return _final.at(element_nr);
  }*/

  /*******************************************************************************
   * batch_size:
  *******************************************************************************/

  size_t batch_size() const {
    return _batch_size;
  }

  /*******************************************************************************
   * length: the length of the _elements.at(pos)
  *******************************************************************************/

  /*size_t length (size_t pos) const {
    assert(pos < _nr);
    return _length.at(pos);
  }*/

  /*******************************************************************************
   * product_by_reduction: take the product of _elements->at(i) and
   * _elements->at(j) by tracing the Cayley graph. Assumes i, j are less than
  *_nr.
  *******************************************************************************/

  /*size_t product_by_reduction (size_t i, size_t j) const {
    assert(i < _nr && j < _nr);
    if (length(i) <= length(j)) {
        while (i != (size_t) -1) {
          j = _left->get(j, _final.at(i));
          i = _prefix.at(i);
        }
        return j;
    } else {
      while (j != (size_t) -1) {
        i = _right->get(i, _first.at(j));
        j = _suffix.at(j);
      }
      return i;
    }
  }*/

  /*******************************************************************************
   * fast_product: take the product of _elements->at(i) and
   * _elements->at(j) by tracing the Cayley graph or actually multiplying,
   * whichever is faster. Assumes i, j are less than _nr.
  *******************************************************************************/

  /*size_t fast_product (size_t i, size_t j) const {
    assert(i < _nr && j < _nr);
    if (length(i) < 2 * _tmp_product->complexity() || length(j) < 2 *
  _tmp_product->complexity()) {
      return product_by_reduction(i, j);
    } else {
      _tmp_product->redefine(_elements->at(i), _elements->at(j));
      return _map.find(_tmp_product)->second;
    }
  }*/

  /*******************************************************************************
  ********************************************************************************
   * Non-const methods . . .
  ********************************************************************************
  *******************************************************************************/

  /*******************************************************************************
   * nr_idempotents: get the total number of idempotents
  *******************************************************************************/

  /*size_t nr_idempotents (bool report) {
    if (_nr_idempotents == 0) {
      enumerate(-1, report);

      size_t sum_word_lengths = 0;
      for (size_t i = 1; i < _lenindex.size(); i++) {
        sum_word_lengths += i * (_lenindex.at(i) - _lenindex.at(i - 1));
      }

      if (_nr * _tmp_product->complexity() < sum_word_lengths) {
        for (size_t i = 0; i < _nr; i++) {
          _tmp_product->redefine(_elements->at(i), _elements->at(i));
          if (*_tmp_product == *_elements->at(i)) {
            _nr_idempotents++;
          }
        }
      } else {
        for (size_t i = 0; i < _nr; i++) {
          if (product_by_reduction(i, i) == i) {
            _nr_idempotents++;
          }
        }
      }
    }
    return _nr_idempotents;
  }*/

  /*******************************************************************************
   *
  *******************************************************************************/

  /*size_t nrrules (bool report) {
    enumerate(-1, report);
    return _nrrules;
  }*/

  /*******************************************************************************
   *
  *******************************************************************************/

  void set_batch_size(size_t batch_size) {
    _batch_size = batch_size;
  }

  /*******************************************************************************
   *
  *******************************************************************************/

  size_t size(bool report) {
    enumerate(-1, report);
    return current_size();
  }

  /*******************************************************************************
   * test_membership: check if the element x belongs to the semigroup
  *******************************************************************************/

  /*size_t test_membership (Element* x, bool report) {
    return (position(x, report) != (size_t) -1);
  }*/

  /*******************************************************************************
   *
  *******************************************************************************/

  /*size_t position (Element* x, bool report) {
    if (x->degree() != _degree) {
      return -1;
    }

    while (true) {
      auto it = _map.find(x);
      if (it != _map.end()) {
        return it->second;
      }
      if (is_done()) {
        return -1;
      }
      enumerate(_nr + 1, report);
      // the _nr means we enumerate _batch_size more elements
    }
  }*/

  /*******************************************************************************
   *
  *******************************************************************************/

  /*std::vector<Element*>* elements (size_t limit, bool report) {
    enumerate(limit, report);
    return _elements;
  }*/

  /*******************************************************************************
   *
  *******************************************************************************/

  /*CayleyGraph* right_cayley_graph (bool report) {
    enumerate(-1, report);
    return _right;//FIXME will have to do some work here!
  }*/

  /*******************************************************************************
   *
  *******************************************************************************/

  /*CayleyGraph* left_cayley_graph (bool report) {
    enumerate(-1, report);
    return _left;
  }*/

  /*******************************************************************************
   * factorization: returns the minimum word equal to _elements.at(pos).
  *******************************************************************************/

  /*Word* factorisation (size_t pos, bool report) {

    Word* word = new Word();
    if (pos > _nr && !is_done()) {
      enumerate(pos, report);
    }

    if (pos < _nr) {
      while (pos != (size_t) -1) {
        word->push_back(_first.at(pos));
        pos = _suffix.at(pos);
      }
    }
    return word;
  }*/

  /*******************************************************************************
   *
  *******************************************************************************/

  /*void reset_next_relation () {
    _relation_pos = -1;
    _relation_gen = 0;
  }*/

  /*******************************************************************************
   *
   * Modifies <relation> in place so that
   *
   * _elements[relation.at(0)] * _gens[relation.at(1)] =
   * _elements[relation.at(2)]
   *
   * <relation> is empty if there are no more relations, and it has length 2
   * in the special case of duplicate generators.
  *******************************************************************************/

  /*void next_relation (std::vector<size_t>& relation, bool report) {
    if (!is_done()) {
      enumerate(-1, report);
    }

    relation.clear();

    if (_relation_pos == _nr) { //no more relations
      return;
    }

    if (_relation_pos != (size_t) -1) {
      while (_relation_pos < _nr) {
        while (_relation_gen < _nrgens) {
          if (!_reduced.get(_index.at(_relation_pos), _relation_gen)
              && (_relation_pos < _lenindex.at(1) ||
                  _reduced.get(_suffix.at(_index.at(_relation_pos)),
                                          _relation_gen))) {
            relation.push_back(_index.at(_relation_pos));
            relation.push_back(_relation_gen);
            relation.push_back(_right->get(_index.at(_relation_pos),
  _relation_gen));
            break;
          }
          _relation_gen++;
        }
        if (relation.empty()) {
          _relation_gen = 0;
          _relation_pos++;
        } else {
          break;
        }
      }
      if (_relation_gen == _nrgens) {
        _relation_gen = 0;
        _relation_pos++;
      } else {
        _relation_gen++;
      }
    } else {
      //duplicate generators
      if (_relation_gen < _duplicate_gens.size()) {
        relation.push_back(_duplicate_gens.at(_relation_gen).first);
        relation.push_back(_duplicate_gens.at(_relation_gen).second);
        _relation_gen++;
      } else {
        _relation_gen = 0;
        _relation_pos++;
        next_relation(relation, report);
      }
    }
  }*/

  /*******************************************************************************
   * add_generators: add new generators.
   *
   * A generator is only added if it is does not belong in the existing data
   * structure (it may belong to the semigroup but just not be known to
   * belong).
   *
   * The semigroup is returned in a state where all of the old elements which
   * had been multiplied by all the old generators, have now been multiplied
   * by the new generators. This means that the new semigroup might contain
   * many more elements than the old one did (whether either was finished
   * enumerating or not).
  *******************************************************************************/

  /* void add_generators (const std::unordered_set <Element*>& coll,
                        bool                           report) {
     if (report) {
       std::cout << "semigroups++: add_generators" << std::endl;
     }

     if (coll.empty()) {
       return;
     }

     assert(degree() == (*coll.begin())->degree());

     // get some parameters from the old semigroup
     size_t old_nrgens  = _nrgens;
     size_t old_nr      = _nr;
     size_t nr_old_left = _pos;

     bool there_are_new_gens = false;
     std::vector<bool> old_new; // have we seen _elements->at(i) yet in new?

     // add the new generators to new _gens, _elements, and _index
     for (Element* x: coll) {
       if (_map.find(x) == _map.end()) {
         if (!there_are_new_gens) {

           // erase the old index
           _index.erase(_index.begin() + _lenindex.at(1), _index.end());

           // set up old_new
           old_new.resize(old_nr, false);
           for (size_t i = 0; i < _genslookup.size(); i++) {
             old_new.at(_genslookup.at(i)) = true;
           }
           there_are_new_gens = true;
         }

         _first.push_back(_gens->size());
         _final.push_back(_gens->size());

         _gens->push_back(x);
         _elements->push_back(x);
         _genslookup.push_back(_nr);
         _index.push_back(_nr);

         is_one(x, _nr);
         _map.insert(std::make_pair(x, _nr));
         _multiplied.push_back(false);
         _prefix.push_back(-1);
         _suffix.push_back(-1);
         _length.push_back(1);

         _nr++;
       }
     }

     if (!there_are_new_gens) { // everything in coll was already in the
   semigroup
       return;
     }

     // reset the data structure
     _nrrules = _duplicate_gens.size();
     _pos     = 0;
     _wordlen = 0;
     _nrgens = _gens->size();
     _lenindex.clear();
     _lenindex.push_back(0);
     _lenindex.push_back(_nrgens - _duplicate_gens.size());

     // add columns for new generators
     _reduced = Flags(_nrgens, _reduced.nr_rows() + _nrgens - old_nrgens);
     _left->add_cols(_nrgens - _left->nr_cols());
     _right->add_cols(_nrgens - _right->nr_cols());

     // add rows in for newly added generators
     _left->add_rows(_nrgens - old_nrgens);
     _right->add_rows(_nrgens - old_nrgens);

     size_t nr_shorter_elements;

     // repeat until we have multiplied all of the elements of <old> up to the
     // old value of _pos by all of the (new and old) generators

     while (nr_old_left > 0) {
       nr_shorter_elements = _nr;
       while (_pos < _lenindex.at(_wordlen + 1) && nr_old_left > 0) {
         size_t i = _index.at(_pos); // position in _elements
         size_t b = _first.at(i);
         size_t s = _suffix.at(i);
         if (_multiplied.at(i)) {
           nr_old_left--;
           // _elements.at(i) is in old semigroup, and its descendants are known
           for (size_t j = 0; j < old_nrgens; j++) {
             size_t k = _right->get(i, j);
             if (!old_new.at(k)) { // it's new!
               is_one(_elements->at(k), k);
               _first.at(k) = _first.at(i);
               _final.at(k) = j;
               _length.at(k) = _wordlen + 2;
               _prefix.at(k) = i;
               _reduced.set(i, j, true);
               if (_wordlen == 0) {
                 _suffix.at(k) = _genslookup.at(j);
               } else {
                 _suffix.at(k) = _right->get(s, j);
               }
               _index.push_back(k);
               old_new.at(k) = true;
             } else if (s == (size_t) -1 || _reduced.get(s, j)) {
               // this clause could be removed if _nrrules wasn't necessary
               _nrrules++;
             }
           }
           for (size_t j = old_nrgens; j < _nrgens; j++) {
             closure_update(i, j, b, s, old_new, old_nr);
           }

         } else {
           // _elements.at(i) is not in old
           _multiplied.at(i) = true;
           for (size_t j = 0; j < _nrgens; j++) {
             closure_update(i, j, b, s, old_new, old_nr);
           }
         }
         _pos++;
       } // finished words of length <wordlen> + 1

       expand(_nr - nr_shorter_elements);
       if (_pos > _nr || _pos == _lenindex.at(_wordlen + 1)) {
         if (_wordlen == 0) {
           for (size_t i = 0; i < _pos; i++) {
             size_t b = _final.at(_index.at(i));
             for (size_t j = 0; j < _nrgens; j++) { // TODO reuse old info here!
               _left->set(_index.at(i), j, _right->get(_genslookup.at(j), b));
             }
           }
         } else {
           for (size_t i = _lenindex.at(_wordlen); i < _pos; i++) {
             size_t p = _prefix.at(_index.at(i));
             size_t b = _final.at(_index.at(i));
             for (size_t j = 0; j < _nrgens; j++) {// TODO reuse old info here!
               _left->set(_index.at(i), j, _right->get(_left->get(p, j), b));
             }
           }
         }
         _lenindex.push_back(_index.size());
         _wordlen++;
       }
       if (report) {
         std::cout << "found " << _index.size() << " elements, ";
         std::cout << _nrrules << " rules, ";
         std::cout << "max word length " << current_max_word_length();
         if (!is_done()) {
           std::cout << ", so far" << std::endl;
         } else {
           std::cout << ", finished!" << std::endl;
         }
       }
     }
   }*/

  /*********************************************************************************
  **********************************************************************************
   * Private methods
  **********************************************************************************
  *********************************************************************************/

 private:
  /*******************************************************************************
   *
  *******************************************************************************/

  /*void inline expand (size_t nr) {
    _left->add_rows(nr);
    _reduced.add_rows(nr);
    _right->add_rows(nr);
    _multiplied.resize(_multiplied.size() + nr, false);
  }*/

  /*******************************************************************************
   *
  *******************************************************************************/

  void inline is_one(Element const* x, Position pos) {
    if (!_found_one && *x == *_id) {
      _pos_one   = pos;
      _found_one = true;
    }
  }

  /*******************************************************************************
   *
  *******************************************************************************/

  /*void inline closure_update (size_t i,
                              size_t j,
                              size_t b,
                              size_t s,
                              std::vector<bool>& old_new,
                              size_t old_nr) {
    if (_wordlen != 0 && !_reduced.get(s, j)) {
      size_t r = _right->get(s, j);
      if (_found_one && r == _pos_one) {
        _right->set(i, j, _genslookup.at(b));
      } else if (_prefix.at(r) != (size_t) -1) {
        _right->set(i, j, _right->get(_left->get(_prefix.at(r), b),
                                      _final.at(r)));
      } else {
        _right->set(i, j, _right->get(_genslookup.at(b), _final.at(r)));
      }
    } else {
      _tmp_product->redefine(_elements->at(i), _gens->at(j));
      auto it = _map.find(_tmp_product);
      if (it == _map.end()) { //it's new!
        is_one(_tmp_product, _nr);
        _elements->push_back(_tmp_product->really_copy());
        _first.push_back(b);
        _final.push_back(j);
        _length.push_back(_wordlen + 2);
        _map.insert(std::make_pair(_elements->back(), _nr));
        _prefix.push_back(i);
        _reduced.set(i, j, true);
        _right->set(i, j, _nr);
        if (_wordlen == 0) {
          _suffix.push_back(_genslookup.at(j));
        } else {
          _suffix.push_back(_right->get(s, j));
        }
        _index.push_back(_nr);
        _nr++;
      } else if (it->second < old_nr && !old_new.at(it->second)) {
        // we didn't process it yet!
        is_one(_tmp_product, it->second);
        _first.at(it->second) = b;
        _final.at(it->second) = j;
        _length.at(it->second) = _wordlen + 2;
        _prefix.at(it->second) = i;
        _reduced.set(i, j, true);
        _right->set(i, j, it->second);
        if (_wordlen == 0) {
          _suffix.at(it->second) = _genslookup.at(j);
        } else {
          _suffix.at(it->second) = _right->get(s, j);
        }
        _index.push_back(it->second);
        old_new.at(it->second) = true;
      } else { // it->second >= old->_nr || old_new.at(it->second)
        // it's old
        _right->set(i, j, it->second);
        _nrrules++;
      }
    }
  }*/

  /*********************************************************************************
  **********************************************************************************
   * Private data
  **********************************************************************************
  *********************************************************************************/

  size_t               _batch_size;
  std::vector<Bucket*> _buckets;
  size_t               _degree;
  std::vector<std::pair<size_t, Position>> _duplicate_gens;
  bool                   _found_one;
  std::vector<Element*>* _gens;
  std::vector<Position>  _genslookup;
  Element*               _id;
  size_t                 _nrgens;
  size_t                 _nr_idempotents;
  size_t                 _nr_threads;
  size_t                 _nrrules;
  Position               _pos_one;
  // size_t                                   _relation_pos;
  // size_t                                   _relation_gen;
  size_t _wordlen;
};

#endif
