#include <cassert>
#include "idrup-state.h"

static vec<lit> empty;
static Clause* REASON_ASSUMP = Clause_new(empty);

Clause* unit_clause(lit l)
{
  return (Clause*) (l<<1|1);
}

void IDrup::free_clause(Clause* cl)
{
  if(((uintptr_t) cl)&1)
    return;
//   delete cl;
  free(cl);
}

bool IDrup::is_used(Clause* cl)
{
  if(!cl)
    return true;

  if(((uintptr_t) cl)&1)
  {
    return used_lit[((uintptr_t) cl)>>1];
  } else {
    return cl->used;
  }
}

void IDrup::undo_until(int trail_sz)
{
  while(trail_sz < trail.size())
  {
    assigns[trail.last()>>1] = l_Undef;
    trail.pop();
  }
}

void IDrup::clear_trail(void)
{
  for(lit l : trail)
    assigns[l>>1] = l_Undef;
  trail.clear();
}

bool IDrup::check_redundant(vec<lit>& cl)
{
  if(has_empty)
    return true;

  grow_to(cl);

  // Enqueue unit clauses
  Clause* confl;

  if(!queue_units(confl))
  {
    mark_conflict(confl);
    clear_trail();
    return true;
  }

  for(lit l : cl)
  {
    
    if(!enqueue(l^1, REASON_ASSUMP))
    {
      used_lit[l] = true;
      clear_trail();
      return true;
    }
  }

  if(propagate(confl))
  {
    clear_trail();
    return false;
  }

  mark_conflict(confl);
  clear_trail();
  return true;
}

void IDrup::mark_conflict(Clause* confl)
{
  if(confl == REASON_ASSUMP)
    return;

  if(((uintptr_t) confl)&1)
  {
    // Unit clause
    lit l = (lit) (((uintptr_t) confl)>>1);
    used_lit[l] = true;
    if(reason[l>>1])
      mark_conflict(reason[l>>1]);
    else
      used_lit[l^1] = true;
    return;
  }
  
  if(!confl->used)
  {
    detachClause(confl);
    confl->used = true; 
    attachClause(confl);
  }

  for(int li = 1; li < confl->size(); li++)
  {
    lit l = (*confl)[li];
    Clause* r(reason[l>>1]);
    if(r == NULL)
    {
      used_lit[l] = true;
    } else {
      mark_conflict(r);
    }
  }
}

bool IDrup::queue_units(Clause*& confl)
{
  for(lit l : unit_table)
  {
    if(!enqueue(l, NULL))
    {
      confl = unit_clause(l);
      return false;
    }
  }
  return true;
}

bool IDrup::propagate(Clause*& confl)
{
  int mark_qhead = 0;
  int qhead = 0;

  while(mark_qhead < trail.size() || qhead < trail.size())
  {
    for(; mark_qhead < trail.size(); mark_qhead++)
    {
      lit l = trail[mark_qhead];

      vec<Clause*>& ws(marked_watches[l]);
      
      int wj = 0;
      for(int wi = 0; wi < ws.size(); wi++)
      {
        // Clause watched
        Clause& cl(*(ws[wi]));
        
        // Ensure ~l is cl[1]
        if(cl[1] != (l^1))
        {
          cl[0] = cl[1];
          cl[1] = (l^1);
        }

        if(value(cl[0]) == l_True)
        {
          // Clause already true.
          ws[wj++] = &cl;
          continue;
        }

        for(int li = 2; li < cl.size(); li++)
        {
          lit lp = cl[li];
          if(value(lp) != l_False)
          {
            cl[1] = lp;
            cl[li] = l^1;
            marked_watches[lp^1].push(&cl);
            goto marked_watch_found;
          }
        }
        // Watch failed.
        if(value(cl[0]) == l_False)
        {
          // Conflict. Copy the remaining watches,
          // and record the conflicting clause.
          while(wi < ws.size())
            ws[wj++] = ws[wi++];
          ws.dropTo(wj);

          confl = &cl;
          return false;
        } else {
          enqueue(cl[0], &cl);
          ws[wj++] = &cl;
        }
  marked_watch_found:
        continue;
      }
      ws.dropTo(wj);
    }

    for(; qhead < trail.size(); qhead++)
    {
      lit l = trail[qhead];

      vec<Clause*>& ws(watches[l]);
      
      int wj = 0;
      for(int wi = 0; wi < ws.size(); wi++)
      {
        // Clause watched
        Clause& cl(*(ws[wi]));
        
        // Ensure ~l is cl[1]
        if(cl[1] != (l^1))
        {
          cl[0] = cl[1];
          cl[1] = (l^1);
        }

        if(value(cl[0]) == l_True)
        {
          // Clause already true.
          ws[wj++] = &cl;
          continue;
        }

        for(int li = 2; li < cl.size(); li++)
        {
          lit lp = cl[li];
          if(value(lp) != l_False)
          {
            cl[1] = lp;
            cl[li] = l^1;
            watches[lp^1].push(&cl);
            goto watch_found;
          }
        }
        // Watch failed.
        if(value(cl[0]) == l_False)
        {
          // Conflict. Copy the remaining watches,
          // and record the conflicting clause.
          while(wi < ws.size())
            ws[wj++] = ws[wi++];
          ws.dropTo(wj);

          confl = &cl;
          return false;
        } else {
          enqueue(cl[0], &cl);

          // Copy remaining watches, and jump out
          while(wi < ws.size())
            ws[wj++] = ws[wi++];
          ws.dropTo(wj);
          goto unmarked_unitprop;
        }
  watch_found:
        continue;
      }
      ws.dropTo(wj);
    }
  unmarked_unitprop:
    continue;
  }
  return true;
}

void IDrup::detachWatch(lit l, Clause* cl)
{
  vec<Clause*>& ws(cl->used ? marked_watches[l] : watches[l]);
  for(int wi = 0; wi < ws.size(); wi++)
  {
    if(ws[wi] == cl)
    {
      ws[wi] = ws.last();
      ws.pop();
      return;
    }
  }
}

void IDrup::detachClause(Clause* cl)
{
//  assert(cl->size() > 1);
  detachWatch((*cl)[0]^1, cl);
  detachWatch((*cl)[1]^1, cl);

  attached--;
}

void IDrup::attachClause(Clause* cl)
{
//  assert(cl->size() > 1);
  lit l0((*cl)[0]^1);
  lit l1((*cl)[1]^1);

  // We'll deal with this by running from the beginning.
//  assert(assigns[l0>>1] == l_Undef);
//  assert(assigns[l1>>1] == l_Undef);
  
  if(cl->used)
  {
    marked_watches[l0].push(cl);
    marked_watches[l1].push(cl);
  } else {
    watches[l0].push(cl);
    watches[l1].push(cl);
  }

  attached++;
}

lbool IDrup::value(lit l)
{
  lbool asg = assigns[l>>1]; 

  return (l&1) ? asg : ((-1)*asg);
}

bool IDrup::enqueue(lit l, Clause* r)
{
  lbool lval = value(l);
  if(lval == l_False)
    return false;
  if(lval == l_Undef)
  {
    assigns[l>>1] = (l&1) ? l_True : l_False;
    reason[l>>1] = r;
    trail.push(l);
  }
  return true;
}

void IDrup::add_clause(vec<lit>& ps)
{
  grow_to(ps);

  if(ps.size() == 0)
  {
    has_empty = true;
  } else if(ps.size() == 1) {
    unit_table.insert(ps[0]);
  } else {
    Clause* cl = Clause_new(ps);
    attachClause(cl);
    table.insert(cl);
  }
}

void IDrup::remove_clause(vec<lit>& cl)
{
  if(cl.size() == 0) {
    has_empty = false;
  } else if(cl.size() == 1) {
    unit_table.erase(cl[0]);
  } else {
    Clause* cl_exist = pop_clause(cl);
    assert(cl_exist);
    free(cl_exist); 
  }
}

Clause* IDrup::pop_clause(vec<lit>& cl)
{
  if(cl.size() == 0)
  {
    has_empty = false;
    return NULL;
  }
  if(cl.size() == 1)
  {
    unit_table.erase(cl[0]);
    return NULL;
  } else {
    // Ugly.
    Clause* cl_ptr = Clause_new(cl);
    
    auto it = table.find(cl_ptr);
//    assert(it != table.end());
    if(it != table.end())
    {
      Clause* cl_exist(*it);
      detachClause(cl_exist);
      table.erase(it);
      free(cl_ptr);

      return cl_exist;
    }
    assert(0 && "Clause not found.\n");
    return NULL;
  }
}

void IDrup::grow_to(int nvars)
{
//  printf("::%d\n", nvars);
  while(assigns.size() <= nvars)
  {
    assigns.push(l_Undef);
    used_lit.push(false);
    used_lit.push(false);
    reason.push(NULL);
    watches.push();
    watches.push();    
    marked_watches.push();
    marked_watches.push();    
  }
}

void IDrup::grow_to(vec<lit>& cl)
{
  int v = 0;
  for(lit l : cl)
    v = std::max(v, l>>1);
  grow_to(v);
}
