#include <cassert>
#include "fdres-state.h"

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

bool FDres::add_clause(int cl_id, vec<atom>& ps) {
  grow_to(ps);

  Clause* cl = NULL;
  if(ps.size() == 1) {
    if(!env.post(ps[0]))
      return false;;
    env.commit();
  } else {
    cl = Clause_new(ps);
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
        if(env.value(*at) != l_False)
          goto clause_done;
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

bool FDres::check_clause(vec<atom>& cl, vec<int>& ant_ids)
{
  /*
  for(atom at : cl) {
    if(!env.post(~at))
      return true;
  }

  vec<Clause*> ants;
  for(int cl_id : ant_ids)
  {
    Clause* cl = find_clause(cl_id);
    if(cl) {
      // Find 'watches'
      atom* at = cl->begin();
      atom* end = cl->end();
      // Find the first watch
      atom* w = cl->begin();
      for(; at != end; ++at) {
        if(env.value(*at) == l_True)
          goto clause_done;
        if(env.value(*at) == l_Undef) {
          std::swap(*at, *w); ++w;
          break;
        }
      }
      if(at == end) {
        // Already unsat.
        env.clear();
        return true;
      }

      // Now the second watch
      for(; at != end; ++at) {
        if(env.value(*at) == l_True)
          goto clause_done; 
        if(env.value(*at) == l_Undef) {
          std::swap(*at, *w); ++w;
          break;
        }
      }
      if(at == end) {
        // Clause is unit; first watch is true
        if(!env.post((*cl)[0])) {
          env.clear();
          return true;
        }
      } else {
        watches[(*cl)[0]].push(cl);
        watches[(*cl)[1]].push(cl);
      }
    }

clause_done:
    continue;
  }
  */
  //FIXME
  return false;
}

void FDres::clear_state()
{
  env.clear();
  touched.clear();
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
  assert(0 && "Clause not found.\n");
  return NULL;
}

void FDres::grow_to(int nvars)
{
  while(watches.size() < nvars) {
    watches.push();
  }
  env.growTo(nvars);
  touched.growTo(nvars);
}

void FDres::grow_to(vec<atom>& cl)
{
  int v = 0;
  for(atom l : cl)
    v = std::max(v, l.var);
  grow_to(v);
}
