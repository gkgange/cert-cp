#include <iostream>
#include <cassert>
#include <algorithm>
#include <zlib.h>
#include "ParseUtils.h"
#include "idrup-types.h"
#include "idres-state.h"
// Quick implementation of modified DRUP
// proof checker, permitting unjustified clauses.
//
//#define DEBUG_REMOVE

using namespace Parse;

template<class In>
void readClause(In& in, vec<lit>& cl)
{
  cl.clear();

  int l;
  while((l = Parse::parseInt(in)) != 0)
  {
    if(l < 0)
      cl.push((-l)<<1);
    else
      cl.push(l<<1|1);
  }
}

template<class In>
void readInts(In& in, vec<int>& ps)
{
  ps.clear();

  int l;
  while((l = Parse::parseInt(in)) != 0)
  {
    ps.push(l);
  }
}


int main(int argc, char** argv)
{
  // Load the proof file. 
  gzFile in_file = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
  StreamBuffer in(in_file);

  IDres idtrace;
  vec<lit> cl; // Temporary clause storage
  vec<int> ants;

  int root = -1;
  
  int init = 0;
  int derived = 0;

  Parse::skipWhitespace(in);
  while(!isEof(in))
  {
    char c = *in;

    if(c == 'c')
    {
      // Comment (or hint) line
      skipLine(in);
    } else if (c == 'd') {
      // Deletion line.
      ++in;
      int cl_id = Parse::parseInt(in);
      idtrace.remove_clause(cl_id);
    } else {
      // Either introduction or 
      int cl_id = Parse::parseInt(in);
      readClause(in, cl);
      Parse::skipWhitespace(in);
      if(*in == '0')
      {
        // Axiom
        ++in;
        init++;
      } else {
        readInts(in, ants);
        if(!idtrace.check_clause(cl, ants))
        {
          printf("c invalid clause: [");
          for(lit l : cl)
          {
            printf(" %s%d", l&1 ? "" : "-", l>>1);
          }
          printf(" ]\n");
          printf("s INVALID\n");

          gzclose(in_file);
          return 1;
        }
        derived++;
        if(cl.size() == 0)
          root = cl_id;
      }
      idtrace.add_clause(cl_id, cl);
    }
    Parse::skipWhitespace(in);
  }

  if(root == -1)
    fprintf(stdout, "s INCOMPLETE\n");
  else
    fprintf(stdout, "s VERIFIED\n");

  gzclose(in_file);
  return 0;
}
