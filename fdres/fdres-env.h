#ifndef FDRES_ENV_H
#define FDRES_ENV_H

#include <unordered_map>
#include "fdres-types.h"
#include "boolset.h"

struct fdres_env {
  fdres_env(void) { }

  fdres_env(int sz)
    : dom(sz, domain()), dom_0(sz, domain()), changes(sz) {

  }

  void growTo(int sz) {
    dom.careful_growTo(sz);     
    dom_0.careful_growTo(sz);
    while(dom.size() < sz) {
      dom.push();
      dom_0.push();
    }
    changes.growTo(sz);
  }

  void set(int ii, const domain& d) {
    changes.insert(ii);
    dom[ii] = d;
  }

  bool post(atom at) {
    growTo(var(at)+1);
    changes.insert(var(at));
    return dom[var(at)].apply(kind(at), val(at));
  }

  // Evaluate an atom under a domain 
  lbool value(atom at) {
    return dom[var(at)].value(kind(at), val(at)); 
  }

  const domain& operator[](int xi) const {
    return dom[xi];
  }

  void clear(void) {
    for(int ii : changes)  
      dom[ii] = dom_0[ii];
    changes.clear();
  }

  void commit(void) {
    for(int ii : changes)
      dom_0[ii] = dom[ii];
    changes.clear();
  }

  vec<domain> dom;  
  vec<domain> dom_0;

  boolset changes;
};

#endif
