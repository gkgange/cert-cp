#include <cstring>
#include "fdres-types.h"
#include "fdres-state.h"
#include "log-parser.h"

struct opts {
  enum in_t { I_Bool, I_Sem };

  opts(void)
    : infile(nullptr), outfile(nullptr),
      verbosity(1),
      in_mode(I_Sem), drop_unit(false) {
  }
  const char* infile;
  const char* outfile; 
  int verbosity;
  in_t in_mode;
  bool drop_unit;
};

int parse_options(opts& o, int argc, char** argv) {
  int jj = 1;
  for(int ii = 1; ii < argc; ++ii) {
    if(strcmp(argv[ii], "-drop-unit") == 0) {
      fprintf(stderr, "WARNING: -drop-unit not yet implemented\n");
      o.drop_unit = true;
    } else if(strcmp(argv[ii], "-bool") == 0) {
      o.in_mode = opts::I_Bool;
    } else if(strcmp(argv[ii], "-q") == 0) {
      o.verbosity = 0;
    } else if (strcmp(argv[ii], "-verbosity") == 0) {
      ++ii;
      o.verbosity = atoi(argv[ii]);
    } else if(strcmp(argv[ii], "-sem") == 0) {
      o.in_mode = opts::I_Sem;
    } else {
      argv[jj++] = argv[ii];
    }
  }
  return jj;
}

#define BUF_SZ 1024
char buf[BUF_SZ];

#define HINT_TAG INT_MAX
#define DEL_TAG (INT_MAX-1)

template<class T>
void vec_fill(FILE* f, unsigned int sz, vec<T>& elts) {
  elts.growTo(sz);
  unsigned int count = fread(elts.begin(), sizeof(T), sz, f);
  assert(sz == count);
  elts._size() = count;
}

template<class T>
void vec_fill(FILE* f, vec<T>& elts) {
  unsigned int sz;
  int ok = fread(&sz, sizeof(unsigned int), 1, f);
  assert(ok);
  vec_fill(f, sz, elts);
}

vec<char> sbuf;

bool verify_unsat(FILE* infile, int verbosity) {
  FDres res;

  // setvbuf(infile, buf, _IOFBUF, BUF_SZ);
  unsigned int hdr[2];
  vec<atom> atoms;
  vec<int> ants;

  // Skip the prelude
  int ok = fread(hdr, sizeof(unsigned int), 2, infile);
  assert(ok == 2);
  for(int ii = 0; ii < hdr[1]; ii++) {
    vec_fill(infile, sbuf);
  }

  while(2 == fread(hdr, sizeof(unsigned int), 2, infile)) {
//    fprintf(stderr, "[%d, %d] | %ld\n", hdr[0], hdr[1], ftell(infile));
    switch(hdr[0]) {
      case HINT_TAG:
        continue;
      case DEL_TAG:
        res.remove_clause(hdr[1]);
        continue;
      default:
        // Intro or infer
        vec_fill(infile, hdr[1], atoms);
        vec_fill(infile, ants);
         
        if(ants.size() == 0) {
          // Intro
          if(verbosity > 2)
            fprintf(stderr, "intro|> %d\n", hdr[0]);
           
          if(!res.add_clause(hdr[0], atoms))
            return true;
        } else {
          // Infer
          if(verbosity > 2) 
            fprintf(stderr, "> clause %d\n", hdr[0]);

#ifdef VAR_WATCH
          if(!res.check_clause_watch(atoms, ants))
#else
          if(!res.check_clause(atoms, ants))
#endif
          {
            if(verbosity > 1)
              fprintf(stderr, "Error: derivation of clause %d failed.\n", hdr[0]);
            return false;
          }
          // Empty clause derived
          if(atoms.size() == 0)
            return true;

          if(!res.add_clause(hdr[0], atoms))
            return true;
        }
    }
  }

  if(verbosity > 0)
    fprintf(stderr, "Error: proof terminated without empty clause.\n");

  return false;
}


int main(int argc, char** argv)
{
  opts o;
  argc = parse_options(o, argc, argv);

  FILE* trace = fopen(argv[1], "rb");
  if(!trace) {
    fprintf(stderr, "Failed to open trace file: %s\n", argv[1]);
    return 2;
  }
  if(verify_unsat(trace, o.verbosity)) {
     if(o.verbosity > 0)
      printf("s VERIFIED\n");
    return 0;
  }
  if(o.verbosity > 0)
    printf("s INCOMPLETE\n");
  return 1;
}
