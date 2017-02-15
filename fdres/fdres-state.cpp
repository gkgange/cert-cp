#include <cassert>
#include <sstream>
#include "fdres-state.h"

// #define CHECK_VERBOSE

static vec<atom> empty;

void FDres::free_clause(Clause* cl)
{
  free(cl);
}

bool FDres::is_used(Clause* cl)
{
  if(!cl)
    return true;

  return cl->used;
}

lbool FDres::value(atom l)
{
  return env.value(l);
}

std::string atom_str(atom at) {
  std::stringstream ss; 
  ss << "x" << at.var; 
  switch(at.kind) {
    case Gt:
      ss << " > ";
      break;
    case Le:
      ss << " <= ";
      break;
    case Neq:
      ss << " != ";
      break;
    case Eq:
      ss << " == ";
      break;
  }
  ss << at.val;
  return ss.str();
}

bool FDres::add_clause(int cl_id, vec<atom>& ps) {
  grow_to(ps);

  Clause* cl = NULL;
  if(ps.size() == 1) {
#ifdef CHECK_VERBOSE
    fprintf(stderr, "%s <- [%d]\n", atom_str(ps[0]).c_str(), cl_id);
#endif
    if(!env.post(ps[0]))
      return false;
    env.commit();
  } else {
    cl = Clause_new(ps);
#ifdef CHECK_VERBOSE
    cl->ident = cl_id;
#endif
    table.insert(std::make_pair(cl_id, cl));
  }
  return true;
}

// Does a single linear scan; assumes clauses are propagated in order
bool FDres::check_clause_linear(vec<atom>& cl, vec<int>& ant_ids) {
  for(atom at : cl) {
    if(!env.post(~at)) {
      env.clear();
      return true;
    }
  }

  for(int cl_id : ant_ids) {
    Clause* cl = find_clause(cl_id);
    if(cl) {
      // Find 'watches'
      atom* w = cl->begin();
      atom* end = cl->end();
      // Find the first watch
      for(; w != end; ++w) {
        if(env.value(*w) == l_True)
          goto clause_done;
        if(env.value(*w) == l_Undef) {
          break;
        }
      }
      if(w == end) {
        // Already unsat.
        env.clear();
        return true;
      }
     
      // Check that the clause is unit
      atom* at = w;
      for(++at; at != end; ++at) {
        if(env.value(*at) != l_False) {
          fprintf(stderr, "WARNING: Clause not %d yet unit.\n", cl_id);
          goto clause_done;
        }
      }

      // Clause is unit; first watch is true
      if(!env.post((*cl)[0])) {
        env.clear();
        return true;
      }
    }

clause_done:
    continue;
  }
  return false;
}

// Returns l_False on inconsistent; l_True on propagation
lbool trim_and_apply(fdres_env& e, vec<atom>& cl) {
  while(cl.size() > 0) {
    switch(e.value(cl[0])) {
      case l_False:
        cl[0] = cl.last();
        cl.pop();
        continue;
      case l_True:
        cl._dropTo(1);
        return l_Undef;
      case l_Undef:
        goto watch_found;
    }
  }
  return l_False; 

watch_found: 
  while(cl.size() > 1) {
    switch(e.value(cl[1])) {
      case l_True:
        cl[0] = cl[1];
        cl._dropTo(1);
        return l_Undef;
      case l_False: 
        cl[1] = cl.last();
        cl.pop();
        continue;
      case l_Undef:
        // Found two unfixed atoms
        return l_Undef;
    }
  }
  if(!e.post(cl[0])) {
#ifdef CHECK_VERBOSE
    fprintf(stderr, "_|_ <~ [?]\n");
#endif
    return l_False;
  }
#ifdef CHECK_VERBOSE
  fprintf(stderr, "%s <- [?]\n", atom_str(cl[0]).c_str());
#endif
  return l_True;   
}

// Does a linear scan first, _then_ collects remaining occurrences.
bool FDres::check_clause(vec<atom>& cl, vec<int>& ant_ids) {
  for(atom at : cl) {
#ifdef CHECK_VERBOSE
    fprintf(stderr, "%s <~\n", atom_str(~at).c_str());
#endif
    if(!env.post(~at)) {
      env.clear();
      return true;
    }
  }

  vec<Clause*> pending_clauses;

  for(int cl_id : ant_ids) {
    Clause* cl = find_clause(cl_id);
    if(cl) {
      // Find 'watches'
      atom* w = cl->begin();
      atom* end = cl->end();
      // Find the first watch
      for(; w != end; ++w) {
        if(env.value(*w) == l_True)
          goto clause_done;
        if(env.value(*w) == l_Undef) {
          break;
        }
      }
      if(w == end) {
        // Already unsat.
#ifdef CHECK_VERBOSE
        fprintf(stderr, "_|_ <- [%d]\n", cl_id);
#endif
        env.clear();
        return true;
      }
     
      // Check that the clause is unit
      atom* at = w;
      for(++at; at != end; ++at) {
        if(env.value(*at) != l_False) {
          pending_clauses.push(cl);
          goto clause_done;
        }
      }

      // Clause is unit; first watch is true
      if(!env.post(*w)) {
#ifdef CHECK_VERBOSE
        fprintf(stderr, "_|_ <- [%d]\n", cl->ident);
#endif
        env.clear();
        return true;
      }
#ifdef CHECK_VERBOSE
      fprintf(stderr, "%s <- [%d]\n", atom_str(*w).c_str(), cl->ident);
#endif
    }

clause_done:
    continue;
  }

  // Failed on a linear scan; now do it (semi-)properly
  // FIXME: Use occurrence lists
  vec< vec<atom> > pending;
  vec<int> remaining;
  for(Clause* cl : pending_clauses) {
    pending.push();
    vec<atom>& p_curr(pending.last());

    for(atom at : *cl) {
      switch(env.value(at)) {
        case l_False:
          continue;
        case l_True:
          pending.pop();
          goto pend_skip;
        case l_Undef:
          p_curr.push(at);
      }
    }
    if(p_curr.size() == 0) {
      env.clear();
#ifdef CHECK_VERBOSE
      fprintf(stderr, "_|_ <- [%d]\n", cl->ident);
#endif
      return true;
    }
    if(p_curr.size() == 1) {
      if(!env.post(p_curr[0])) {
        // Should be unreachable
#ifdef CHECK_VERBOSE
        fprintf(stderr, "_|_ <- [%d] <UNREACH?> \n", cl->ident);
#endif
        env.clear();
        return true;
      }
#ifdef CHECK_VERBOSE
      fprintf(stderr, "%s <- [%d]\n", atom_str(p_curr[0]).c_str(), cl->ident);
#endif
      pending.pop();
    } else {
      remaining.push(pending.size()-1);
    }
pend_skip:
    continue;
  }

  while(true) {
    int jj = 0;
    for(int pi : remaining) {
      switch(trim_and_apply(env, pending[pi])) {
        case l_True:
          continue;
        case l_False:
          env.clear();
          return true;
        case l_Undef:
          remaining[jj++] = pi;
      }
    }
    if(jj == remaining.size())
      return false;
    remaining._dropTo(jj);
  }

  return false;
}

#ifdef VAR_WATCH
inline void enqueue_var(FDres* r, int var) {
  if(r->var_is_queued[var])
    return;
  r->var_is_queued[var] = true;
  r->var_queue.push(var);
}

inline int dequeue_var(FDres* r) {
  int v = r->var_queue.last();
  r->var_queue.pop();
  r->var_is_queued[v] = false;
  return v;
}

inline void add_watch(FDres* r, atom at, Clause* cl) {
  r->touched_vars.insert(at.var);
  r->watches[at.var].push(FDres::watch { at, cl });
}

inline void cleanup(FDres* r) {
  for(int var : r->var_queue) {
    r->var_is_queued[var] = false;
  }
  r->var_queue.clear();
  
  for(int var : r->touched_vars) {
    r->watches[var].clear();     
  }
  r->touched_vars.clear();
  r->env.clear();
}

bool FDres::check_clause_watch(vec<atom>& cl, vec<int>& ant_ids) {
  for(atom at : cl) {
#ifdef CHECK_VERBOSE
    fprintf(stderr, "%s <~\n", atom_str(~at).c_str());
#endif
    if(!env.post(~at)) {
      env.clear();
      return true;
    }
  }

//  for(int vi = 0; vi < var_is_queued.size(); vi++)
//    assert(!var_is_queued[vi]);
  for(int cl_id : ant_ids) {
    Clause* cl_ptr = find_clause(cl_id);
    if(cl_ptr) {
      Clause& cl(*cl_ptr);
      // Find the first indeterminate atom
      atom* w = cl.begin();
      atom* end = cl.end();
      // Find the first watch
      for(; w != end; ++w) {
        if(env.value(*w) == l_True)
          goto clause_prep_done;
        if(env.value(*w) == l_Undef) {
          break;
        }
      }
      if(w == end) {
        // Already unsat.
#ifdef CHECK_VERBOSE
        fprintf(stderr, "_|_ <- [%d]\n", cl_id);
#endif
        cleanup(this);
        return true;
      }
      // Move first watch to cl[0]
      atom fst = *w;
      *w = cl[0];
      cl[0] = fst;
     
      // Check that the clause is unit
      atom* at = w;
      for(++at; at != end; ++at) {
        if(env.value(*at) == l_True)
          goto clause_prep_done;

        if(env.value(*at) == l_Undef) {
          /* Not unit; set up watches. */
          atom snd = *at;
          *at = cl[1];
          cl[1] = snd;

          add_watch(this, fst, cl_ptr);
          add_watch(this, snd, cl_ptr);
          goto clause_prep_done;
        }
      }

      // Clause is unit; first watch is true
      if(!env.post(fst)) {
#ifdef CHECK_VERBOSE
        fprintf(stderr, "_|_ <- [%d]\n", cl.ident);
#endif
        cleanup(this);
        return true;
      }
#ifdef CHECK_VERBOSE
      fprintf(stderr, "%s <- [%d]\n", atom_str(fst).c_str(), cl.ident);
#endif
      enqueue_var(this, fst.var);
    }

clause_prep_done:
    continue;
  }
  
  while(var_queue.size() > 0) {
    int var = dequeue_var(this);
//    assert(!var_is_queued[var]);
    
    int wj = 0;
    vec<watch>& ws(watches[var]);
    for(watch w : ws) {
      // If the watch is still indeterminate, save it.
      if(env.value(w.at) == l_True)
        continue;
      if(env.value(w.at) == l_Undef) {
        ws[wj++] = w;
        continue;
      }
      // Make sure the watch is cl[0].
      Clause& cl(*(w.cl));
      if(cl[1] != w.at) {
//        assert(w.at == cl[0]);
        cl[0] = cl[1];
        cl[1] = w.at;
      }
//      assert(w.at == cl[1]);
      atom fst = cl[0];
      if(env.value(fst) == l_True) {
        // Clause is satisfied
        continue;
      }
      for(int ii = 2; ii < cl.size(); ii++) {
        atom at(cl[ii]);
        if(env.value(at) == l_True)
          goto clause_watch_done;
        if(env.value(at) == l_Undef) {
          // Watch found
          // If the watch is on the current var,
          // add_watch may invalidate the iterator.
          if(at.var == var) {
            ws[wj++] = { at, &cl };
          } else {
            add_watch(this, at, &cl);
          }
          cl[1] = at;
          cl[ii] = w.at;
          goto clause_watch_done;
        }
      }
      // If we reach here, clause is unit
      if(!env.post(fst)) {
#ifdef CHECK_VERBOSE
        fprintf(stderr, "_|_ <- [%d]\n", cl.ident);
#endif
        cleanup(this);
        return true;
      }
#ifdef CHECK_VERBOSE
      fprintf(stderr, "%s <- [%d]\n", atom_str(fst).c_str(), cl.ident);
#endif
      enqueue_var(this, fst.var);
        
clause_watch_done:
      continue;
    }
    ws.dropTo(wj);
  }

  // Reached fixpoint without concluding unsat
  cleanup(this);
  return false;
}
#endif

void FDres::clear_state()
{
  env.clear();
}

bool FDres::enqueue(atom l)
{
  return env.post(l);
}

Clause* FDres::find_clause(int cl_id)
{
  auto it = table.find(cl_id);
  if(it == table.end())
    return nullptr;

  return (*it).second;
}

void FDres::remove_clause(int cl_id)
{
  Clause* cl = pop_clause(cl_id);
  if(cl)
    free(cl); 
}

Clause* FDres::pop_clause(int cl_id)
{
  auto it = table.find(cl_id);
  if(it != table.end())
  {
    Clause* cl((*it).second);
    table.erase(it);
    return cl;
  }
//  fprintf(stderr, "Clause not found: %d\n", cl_id);
//  assert(0);
  return NULL;
}

void FDres::grow_to(int nvars)
{
#ifdef VAR_WATCH
  while(watches.size() < nvars) {
    watches.push();
    var_is_queued.push(false);        
  }
  touched_vars.growTo(nvars);
#endif
  env.growTo(nvars);
}

void FDres::grow_to(vec<atom>& cl)
{
  int v = 0;
  for(atom l : cl)
    v = std::max(v, l.var);
  grow_to(v);
}
