#include <cassert>
#include "idres-state.h"

static vec<lit> empty;

void IDres::free_clause(Clause* cl)
{
  free(cl);
}

bool IDres::is_used(Clause* cl)
{
  if(!cl)
    return true;

  return cl->used;
}

lbool IDres::value(lit l)
{
  lbool asg = assigns[l>>1]; 

  return (l&1) ? asg : ((-1)*asg);
}

void IDres::add_clause(int cl_id, vec<lit>& ps)
{
  grow_to(ps);

//  Clause* cl = Clause_new(ps);
  Clause* cl = NULL;
  if(ps.size() == 1)
  {
    cl = (Clause*) (ps[0]<<1|1);
  } else {
    cl = Clause_new(ps);
  }

  table.insert(std::make_pair(cl_id, cl));
}

bool IDres::check_clause(vec<lit>& cl, vec<int>& ant_ids)
{
  vec<Clause*> ants;
  for(int cl_id : ant_ids)
  {
    Clause* cl = find_clause(cl_id);
    ants.push(cl);
    
//    if(cl->size() == 1)
    if(((uintptr_t) cl)&1)
    {
//      lit l = (*cl)[0];
      lit l = ((uintptr_t) cl)>>1;
      if(!enqueue(l))
      {
        clear_state();
        return true;
      }
    } else {
      assert(cl->size() > 1);
      cl->count = cl->size();
      for(lit l : (*cl))
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
  for(lit l : cl)
  {
    if(!enqueue(l^1))
    {
      clear_state();
      return true;
    }
  }

  int qhead = 0;
  for(; qhead < trail.size(); qhead++)
  {
    lit l = trail[qhead];
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
        for(lit m : (*c))
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
}

void IDres::clear_state()
{
  for(lit l : trail)
    assigns[l>>1] = l_Undef;
  for(lit l : touched)
  {
    is_touched[l] = false;
    watches[l].clear();
  }
  trail.clear();
  touched.clear();
}

bool IDres::enqueue(lit l)
{
  lbool lval = value(l);
  if(lval == l_False)
    return false;
  if(lval == l_Undef)
  {
    assigns[l>>1] = (l&1) ? l_True : l_False;
    trail.push(l);
  }
  return true;
}

Clause* IDres::find_clause(int cl_id)
{
  auto it = table.find(cl_id);
  if(it == table.end())
    assert(0 && "Clause not found.");

  return (*it).second;
}

void IDres::remove_clause(int cl_id)
{
  Clause* cl = pop_clause(cl_id);
  assert(cl);
  if(!(((uintptr_t) cl)&1))
    free(cl); 
}

Clause* IDres::pop_clause(int cl_id)
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

void IDres::grow_to(int nvars)
{
  while(assigns.size() <= nvars)
  {
    assigns.push(l_Undef);
    watches.push();
    watches.push();    
    is_touched.push(false);
    is_touched.push(false);
  }
}

void IDres::grow_to(vec<lit>& cl)
{
  int v = 0;
  for(lit l : cl)
    v = std::max(v, l>>1);
  grow_to(v);
}
