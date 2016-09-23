#ifndef DIFFSOLVE_BOOLSET_H
#define DIFFSOLVE_BOOLSET_H
#include "fdres-types.h"

class boolset {
public:  
  boolset(int sz)
    : is_touched(sz, false) { }

  boolset(void) { }

  bool elem(int idx) const { assert(idx < (int) is_touched.size()); return is_touched[idx]; }
  void insert(int idx) {
    assert(idx < (int) is_touched.size());
    if(!is_touched[idx]) {
      is_touched[idx] = true;
      touched.push(idx);
    }
  }
  void clear(void) {
    for(int idx : touched)
      is_touched[idx] = false;
    touched.clear();
  }

  void grow(void) { is_touched.push(false); }
  void growTo(int newsz) {
    while(size() < newsz)
      grow();
  }

  int limit(void) const { return is_touched.size(); }
  int size(void) const { return touched.size(); }

  int* begin(void) { return touched.begin(); }
  int* end(void) { return touched.end(); }

  vec<bool> is_touched;
  vec<int> touched;
};
#endif
