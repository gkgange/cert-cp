#ifndef __IDRUP_STATE_H__
#define __IDRUP_STATE_H__
#include <unordered_set>
#include "idrup-types.h"

class Marks {
public:
  Marks(void)
    : time(0), idx(0)
  { } 

  void tick(void) {
    if(marks.size() > 0)
    {
      marks[idx] = time;
      idx = (idx+1)%marks.size();
    }
    time++;
  }

  void mark(Clause* cl)
  {
    tick();
    for(lit l : *cl)
    {
      while(marks.size() <= l)
        marks.push(time-1);
      marks[l] = time;
    }
  }

  bool is_marked(Clause* cl)
  {
    for(lit l : *cl)
    {
      while(marks.size() <= l)
        marks.push(time-1);

      if(marks[l] != time)
        return false;
    }
    return true;
  }

protected:
  unsigned int time;
  unsigned int idx;
  vec<unsigned int> marks;
};

class Hash_clause {
public:
  Hash_clause(Marks& _m) : m(_m) {}

  unsigned int operator()(Clause* cl) const
  {
    m.mark(cl);
    
    // Hash function taken from DRUP-trim, because
    // it needs to be order-invariant.
    unsigned int sum  = 0, prod = 1, xorr  = 0;
    for (int i = 0; i < cl->size(); ++i) {
      prod *= (*cl)[i];
      sum  += (*cl)[i];
      xorr  ^= (*cl)[i];
    }
    return ((1023 * sum + prod) ^ (31 * xorr));
  }

  Marks& m;
};

class Eq_clause {
public:
  Eq_clause(Marks& _m) : m(_m) {}

  bool operator()(Clause* cl_x, Clause* cl_y) const
  {
    // Assumption: hash has most recently been called on
    // one of cl_x, cl_y
    return (cl_x->size() == cl_y->size()
        && m.is_marked(cl_x)
        && m.is_marked(cl_y));
  }
  Marks& m;
};

typedef std::unordered_set<Clause*, Hash_clause, Eq_clause> ClauseTable;
typedef std::unordered_set<int> UnitTable;

class IDrup {
public:
  IDrup(void)
    : has_empty(false), attached(0), marks(), table(1000, Hash_clause(marks), Eq_clause(marks))
  { }

  bool check_redundant(vec<lit>& cl);
  void add_clause(vec<lit>& cl);
  void remove_clause(vec<lit>& cl);
  Clause* pop_clause(vec<lit>& cl);

  void free_clause(Clause* cl);
  bool is_used(Clause* cl);
protected:
  void attachClause(Clause* c);
  void detachWatch(lit l, Clause* c);
  void detachClause(Clause* c);

  lbool value(lit l);
  bool enqueue(lit l, Clause* r);

  bool queue_units(Clause*& confl);

  bool propagate(Clause*& confl);
  void mark_conflict(Clause* cl);

  void grow_to(int nvars);
  void grow_to(vec<lit>& ps);

  void undo_until(int trail_sz);
  void clear_trail(void);

  bool has_empty;

  int attached;

   
  vec<lbool> assigns;
  vec<bool> used_lit;
  vec<Clause*> reason;

  vec<lit> trail;

  vec< vec<Clause*> > marked_watches;
  vec< vec<Clause*> > watches;

  Marks marks;
  ClauseTable table;

  UnitTable unit_table;
};
#endif
