#include "fdres-types.h"
#include "fdres-state.h"
#include "log-parser.h"

template<class P>
bool verify_unsat(P& gen, int verbosity)
{
  FDres res;

  StepT next;
  while((next = gen.next()) != S_None)
  {
    switch(next)
    {
      case S_Intro:
        res.add_clause(gen.id, gen.clause);
        break;

      case S_Del:
        res.remove_clause(gen.id);
        break;
      
      case S_Infer:
        if(!res.check_clause(gen.clause, gen.ants))
        {
          if(verbosity > 0)
            fprintf("Error: derivation of clause %d failed.\n", gen.id);
          return false;

        }
        // Empty clause derived
        if(gen.clause.size() == 0)
          return true;

        res.add_clause(gen.id, gen.clause);
        break;
      default:
        assert (0 && "Unreachable.");
    }
  }
  if(verbosity > 0)
    fprintf(stderr, "Error: proof terminated without empty clause.\n");

  return false;
}

int main(int argc, char** argv)
{
  // Construct the     
   

}
