#ifndef CHECK_UTILS_H__
#define CHECK_UTILS_H__
#include <limits.h>
#include <cstdlib>
#include <cassert>
#include <set>

typedef std::set<int> iset;

typedef int lbool;
#define l_True 1
#define l_False (-1)
#define l_Undef 0

enum AtKind { Gt = 0, Le = 1, Neq = 2, Eq = 3 };
struct atom {
  int var;
  AtKind kind;
  int val;

  atom operator~(void) const {
    return atom { var, (AtKind) (kind^1), val };
  }
};

//inline unsigned int var(atom a) { return a.info>>2; }
//inline unsigned int kind(atom a) { return a.info&3; }
//inline int val(atom a) { return a.val; }
inline unsigned int var(atom a) { return a.var; }
inline unsigned int kind(atom a) { return a.kind; }
inline int val(atom a) { return a.val; }

static atom at_Undef = { INT_MAX, Le, INT_MIN };

class domain {
public: 
  domain(void)
    : lb(INT_MIN), ub(INT_MAX)
  { }

  domain(int _lb, int _ub, iset& _holes)
    : lb(_lb), ub(_ub), holes(_holes)
  { }

  lbool value(unsigned int op, int k)
  {
    lbool res = l_Undef;
    if(op&2)
    {
      // Equality
      if(!indomain(k))
        res = l_False;
      else if(lb == ub)
        res = l_True;
    } else {
      // Leq 
      if(k < lb)
        res = l_False;
      else if(ub <= k)
        res = l_False;
    }
  
    return (op&1) ? res : ((-1)*res);
  }

  bool apply(unsigned int op, int k)
  {
    switch(op)
    {
      case Le:
        return set_ub(k); 
      case Gt:
        return set_lb(k+1);
      case Eq:
        return set_lb(k) && set_ub(k);
      case Neq:
        return rem(k);

      default:
        assert (0 && "Not reachable.");
    }
    return false;
  }

  bool indomain(int k)
  {
    if(k < lb || ub < k)
      return false;
    auto it = holes.find(k);
    if(it != holes.end())
      return false;
    return true;   
  }

  bool rem(int k)
  {
    if(lb == k)
      return set_lb(k+1);
    else if(k == ub)
      return set_ub(k-1);

    holes.insert(k);
    return true;
  }

  void finesse_lb(void) {
    auto it = holes.begin();
    // Trim the domain.
    while(it != holes.end() && (*it) < lb)
    {
      auto t = it;
      ++it;
      holes.erase(t);
    }
    while(it != holes.end() && (*it) == lb)
    {
      auto t = it;
      ++it;
      holes.erase(t);
      lb++;
    }
  }

  bool set_lb(int k) {
    if(lb < k)
    {
      lb = k;
      finesse_lb();
      return lb <= ub;
    }
    return true;
  }

  void finesse_ub(void) {
    auto it = holes.rbegin();
    // Trim the domain. Urgh -- complexity here is log(n).
    while(it != holes.rend() && ub < (*it))
    {
      auto t = it;
      ++it;
      holes.erase(--t.base());
    }

    while(it != holes.rend() && (*it) == ub)
    {
      auto t = it;
      ++it;
      holes.erase(--t.base());
      ub--;
    }
  }

  bool set_ub(int k) {
    if(k < ub)
    {
      ub = k;
      finesse_ub();
      return lb <= ub;
    }
    return true;
  }

  void clear(void) { lb = INT_MIN; ub = INT_MAX; holes.clear(); }

  int lb, ub;
  iset holes; 
};

template <class T>
class vec {
public:
  static int default_sz() { return 100; }

  typedef T* iterator;
  typedef vec<T> vec_t;
  
  vec(void)
    : sz(0), maxsz(default_sz()), data((T*) malloc(sizeof(T)*maxsz))
  {
    assert(data);
  }

  vec(int _maxsz)
    : sz(0), maxsz(_maxsz), data((T*) malloc(sizeof(T)*maxsz))
  {
    assert(data);
  }

  vec(int _sz, T elt)
    : sz(_sz), maxsz(_sz), data((T*) malloc(sizeof(T)*maxsz)) {
    for(int ii = 0; ii < sz; ii++)
      new (&data[ii]) T(elt);
  }

  template<class V>
  vec(V& elts)
    : sz(elts.size()), maxsz(std::max(2, sz)), data((T*) malloc(sizeof(T)*maxsz))
  {
    int ii = 0;  
    for(T& e : elts)
      data[ii++] = e;
  }

  T* begin(void) { return data; }
  T* end(void) { return data+sz; }
  int size(void) const { return sz; }

  T& last(void) { return data[sz-1]; }

  void push(void) {
    if(sz >= maxsz)
      growTo(sz+1);
    new (&(data[sz++])) T();
  }
  void _push(const T& elt) { data[sz++] = elt; }
  void push(const T& elt) {
    if(sz >= maxsz)
      growTo(sz+1); 
    _push(elt);
  }
  void pop(void) { data[--sz].~T(); }

  T& operator[](int ii) { return data[ii]; }
  const T& operator[](int ii) const { return data[ii]; }

  ~vec(void) {
    clear();
    free(data);
  }
  
  void growTo(int new_max) {
    if(maxsz >= new_max) return;
    assert(maxsz >= 1);
    while(maxsz < new_max) {
      maxsz *= 2;
    }
    data = (T*) realloc(data, sizeof(T)*maxsz);
    assert(data);
  }

  void dropTo(int _sz)
  {
    while(_sz < sz)
      pop();
  }
  void _dropTo(int _sz) {
    if(_sz < sz)
      sz = _sz;
  }

//  void clear(void) { sz = 0; }
  void clear(void) { dropTo(0); }
  void _clear(void) { sz = 0; }
protected:
  int sz;
  int maxsz;

  T* data;
};

class Clause {
public:
  typedef atom* iterator;

  template<class V>
  Clause(V& cl)
    : used(false), count(0), sz(cl.size())
  {
    int ii = 0;
    for(atom l : cl)
      data[ii++] = l;
  }

  template<class V>
  Clause(V& cl, int _sz)
    : sz(_sz)
  {
    for(int ii = 0; ii < sz; ii++)
      data[ii] = cl[ii];
  }

  atom* begin() { return data; }
  atom* end() { return data + sz; }

  atom& operator[](int i) { return data[i]; }
  
  int size(void) const { return sz; }

  bool used;
  int count;
protected:
  int sz;
  atom data[0];
};

template<class V>
Clause* Clause_new(V& cl) {
  int mem_size = sizeof(Clause) + cl.size()*sizeof(atom); 
  void* mem = malloc(mem_size);
  return new (mem) Clause(cl);
}

template<class V>
Clause* Clause_new(V& cl, int _sz) {
  int sz = std::min(_sz, (int) cl.size());
  int mem_size = sizeof(Clause) + sz*sizeof(atom); 
  void* mem = malloc(mem_size);
  return new (mem) Clause(cl, sz);
}

#endif
