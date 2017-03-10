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
#define BIN_TRACE

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

int check_bintrace(FILE* infile, IDres& idtrace) {
  vec<lit> cl; // Temporary clause storage
  vec<int> ants;

  int root = -1;
  
  int init = 0;
  int derived = 0;

  unsigned int header[2];

  while(2 == fread(header, sizeof(unsigned int), 2, infile)) {
    if(header[0] == INT_MAX-1) {
      // Deletion
      idtrace.remove_clause(header[1]);
      continue;
    } else if(header[0] == INT_MAX) {
      continue;
    }
    unsigned int cl_id = header[0];
    unsigned int sz = header[1];

    // Read the literals
    cl.growTo(sz);  
    int r_sz;
    if(sz != (r_sz = fread(cl.begin(), sizeof(lit), sz, infile))) {
      fprintf(stderr, "Expected %d, got %d\n", sz, r_sz);
      assert(0);
    }
    cl._size() = sz;

    // And the antecedents
    if(1 != fread(&sz, sizeof(unsigned int), 1, infile))
      assert(0);
    ants.growTo(sz);
    if(sz != fread(ants.begin(), sizeof(int), sz, infile))
      assert(0);
    ants._size() = sz;

    if(ants.size() == 0) {
      // Axiom
      init++;
    } else {
      if(!idtrace.check_clause(cl, ants))
      {
        printf("c invalid clause: [");
        for(lit l : cl)
        {
          printf(" %s%d", l&1 ? "" : "-", l>>1);
        }
        printf(" ]\n");
        printf("s INVALID\n");

        fclose(infile);
        exit(1);
        return 1;
      }
      derived++;
      if(cl.size() == 0)
        root = cl_id;
    }
    idtrace.add_clause(cl_id, cl);
  }
  return root;
}

int main(int argc, char** argv)
{
  // Load the proof file. 
#ifndef BIN_TRACE
  gzFile in_file = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
  StreamBuffer in(in_file);
#else
  FILE* infile = stdin;
  if(argc != 1) {
    infile = fopen(argv[1], "rb");
    if(!infile) {
      fprintf(stderr, "Failed to open file %s\n", argv[1]);
      exit(1);
    }
  }
#endif

#ifdef BIN_TRACE
  IDres idtrace;
  int root = check_bintrace(infile, idtrace);
 #else 
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
#endif

  if(root == -1)
    fprintf(stdout, "s INCOMPLETE\n");
  else
    fprintf(stdout, "s VERIFIED\n");

#ifndef BIN_TRACE
  gzclose(in_file);
#endif
  return 0;
}
