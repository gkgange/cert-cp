#ifndef CHECK_UTILS_H__
#define CHECK_UTILS_H__
#include <cstdlib>

typedef int lit;

typedef int lbool;
#define l_True 1
#define l_False (-1)
#define l_Undef 0

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
  int& _size(void) { return sz; }

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
  typedef lit* iterator;

  template<class V>
  Clause(V& cl)
    : used(false), count(0), sz(cl.size())
  {
    int ii = 0;
    for(lit l : cl)
      data[ii++] = l;
  }

  template<class V>
  Clause(V& cl, int _sz)
    : sz(_sz)
  {
    for(int ii = 0; ii < sz; ii++)
      data[ii] = cl[ii];
  }

  lit* begin() { return data; }
  lit* end() { return data + sz; }

  lit& operator[](int i) { return data[i]; }
  
  int size(void) const { return sz; }

  bool used;
  int count;
protected:
  int sz;
  lit data[0];
};

template<class V>
Clause* Clause_new(V& cl)
{
  int mem_size = sizeof(Clause) + cl.size()*sizeof(lit); 
  void* mem = malloc(mem_size);
  return new (mem) Clause(cl);
}

template<class V>
Clause* Clause_new(V& cl, int _sz)
{
  int sz = std::min(_sz, (int) cl.size());
  int mem_size = sizeof(Clause) + sz*sizeof(lit); 
  void* mem = malloc(mem_size);
  return new (mem) Clause(cl, sz);
}

#endif
