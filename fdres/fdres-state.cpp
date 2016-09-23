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
  return domains[var(l)].value(kind(l), val(l));
}

void FDres::add_clause(int cl_id, vec<atom>& ps)
{
  grow_to(ps);

  Clause* cl = NULL;
  if(ps.size() == 1)
  {
    cl = (Clause*) (units.size()<<1|1);
    units.push(ps[0]);
  } else {
    cl = Clause_new(ps);
  }

  table.insert(std::make_pair(cl_id, cl));
}

bool FDres::check_clause(vec<atom>& cl, vec<int>& ant_ids)
{
  /*
  vec<Clause*> ants;
  for(int cl_id : ant_ids)
  {
    Clause* cl = find_clause(cl_id);
    ants.push(cl);
    
    if(((uintptr_t) cl)&1)
    {
      atom l = units[((uintptr_t) cl)>>1];
      if(!enqueue(l))
      {
        clear_state();
        return true;
      }
    } else {
      assert(cl->size() > 1);
      cl->count = cl->size();
      for(atom l : (*cl))
      {
        if(!is_touched[l^1])
        {
          is_touched[l^1] = true;
          touched.push(l^1);
        }
        watches[l^1].push(cl);
      }
    }
  }
  for(atom l : cl)
  {
    if(!enqueue(~l))
    {
      clear_state();
      return true;
    }
  }

  int qhead = 0;
  for(; qhead < trail.size(); qhead++)
  {
    atom l = trail[qhead];
    vec<Clause*>& ws(watches[l]);

    for(Clause* c : ws)
    {
      c->count--;
      if(!c->count)
      {
        // Conflict
        clear_state();
        return true;
      } else if(c->count == 1) {
        // Unit
        for(atom m : (*c))
        {
          if(value(m) != l_False)
          {
            bool okay = enqueue(m);
            assert(okay);
            break;
          }
        }
      }
    }
  }
  // Failed to detect a conflict; clear state
  clear_state();
  return false;
  */
  //FIXME
  return false;
}

void FDres::clear_state()
{
  for(unsigned int v : touched)
  {
    is_touched[v] = false;
    domains[v].clear();       
  }
  trail.clear();
  touched.clear();
}

bool FDres::enqueue(atom l)
{
  /*
  unsigned int v(var(l));
  unsigned int k(kind(l));
  int x(val(l));

  lbool lval = domains[v].value(k, x);
  if(lval == l_False)
    return false;
  if(lval == l_Undef)
  {
    if(!is_touched(v))
    {
      touched.push(v);
      is_touched[v] = true;
    }

    domains[v].apply(k, x);
    trail.push(l);
  }
  return true;
  */
  assert(0 && "Implement");
  return false;
}

Clause* FDres::find_clause(int cl_id)
{
  auto it = table.find(cl_id);
  if(it == table.end())
    assert(0 && "Clause not found.");

  return (*it).second;
}

void FDres::remove_clause(int cl_id)
{
  Clause* cl = pop_clause(cl_id);
  assert(cl);
  if(!(((uintptr_t) cl)&1))
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
  /*
  while(domains.size() <= nvars)
  {
    domains.push(l_Undef);
    is_touched.push(false);
  }
  */
  assert(0 && "Implement me.");
}

void FDres::grow_to(vec<atom>& cl)
{
  /*
  int v = 0;
  for(atom l : cl)
    v = std::max(v, var(l));
  grow_to(v);
  */
  assert(0 && "Implement me");
}
