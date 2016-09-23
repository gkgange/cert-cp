#ifndef __FDRES_STATE_H__
#define __FDRES_STATE_H__
#include <unordered_map>
#include "fdres-types.h"

typedef std::unordered_map<int, Clause*> ClauseTable;

class FDres {
public:
  FDres(void)
  { }

  // Check a clause is implied by its antecedents
  bool check_clause(vec<atom>& cl, vec<int>& ants);
  // Add a clause
  void add_clause(int cl_id, vec<atom>& cl);
  void remove_clause(int cl_id);
  Clause* pop_clause(int cl_id);

  void free_clause(Clause* cl);
  bool is_used(Clause* cl);

protected:
//  void attachClause(Clause* c);
//  void detachWatch(lit l, Clause* c);
//  void detachClause(Clause* c);
  Clause* find_clause(int cl_id);
  void clear_state();

  lbool value(atom l);
  bool enqueue(atom l);

//  bool queue_units(Clause*& confl);

//  bool propagate(Clause*& confl);
//  void mark_conflict(Clause* cl);

  void grow_to(int nvars);
  void grow_to(vec<atom>& ps);

//  void undo_until(int trail_sz);
//  void clear_trail(void);

  vec<domain> domains;

  vec<atom> trail;

  vec<unsigned int> touched;
  vec<bool> is_touched; 

  vec< vec<Clause*> > watches;

  ClauseTable table;
  vec<atom> units;
};
#endif
