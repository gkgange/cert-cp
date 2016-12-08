#ifndef __FDRES_STATE_H__
#define __FDRES_STATE_H__
#include <unordered_map>
#include "fdres-types.h"
#include "fdres-env.h"

typedef std::unordered_map<int, Clause*> ClauseTable;

class FDres {
public:
  FDres(void) : env(0) { }

  FDres(int sz)
    : env(sz)
  { }

  // Check a clause is implied by its antecedents
  bool check_clause(vec<atom>& cl, vec<int>& ants);
  bool check_clause_linear(vec<atom>& cl, vec<int>& ant_ids);
#ifdef VAR_WATCH
  bool check_clause_watch(vec<atom>& cl, vec<int>& ant_ids);
#endif
  // Add a clause
  bool add_clause(int cl_id, vec<atom>& cl);
  void remove_clause(int cl_id);

  void free_clause(Clause* cl);
  bool is_used(Clause* cl);

protected:
  Clause* pop_clause(int cl_id);
//  void attachClause(Clause* c);
//  void detachWatch(lit l, Clause* c);
//  void detachClause(Clause* c);
  Clause* find_clause(int cl_id);
  void clear_state();

  lbool value(atom l);
  bool enqueue(atom l);

  void grow_to(int nvars);
  void grow_to(vec<atom>& ps);

#ifdef VAR_WATCH
public:
#endif
  fdres_env env;

#ifdef VAR_WATCH
  struct watch { atom at; Clause* cl; };
  vec< vec<watch> > watches;
  vec<bool> var_is_queued;
  vec<int> var_queue;

  boolset touched_vars;
#endif

  ClauseTable table;
};
#endif
