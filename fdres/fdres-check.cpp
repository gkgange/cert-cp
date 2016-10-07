#include <cstring>
#include "fdres-types.h"
#include "fdres-state.h"
#include "log-parser.h"

struct opts {
  enum in_t { I_Bool, I_Sem };

  opts(void)
    : infile(nullptr), outfile(nullptr),
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


template<class P>
bool verify_unsat(P& gen, int verbosity) {
  FDres res;

  // StepT next;
  // while((next = gen.next()) != S_None)
  while(!gen.isEof()) {
    switch(gen.next()) {
      case S_Comm:
        // Ignore coments in resolution checking
        break;
      case S_Intro:
        if(verbosity > 2)
          fprintf(stderr, "intro|> %d\n", gen.id);
        // Any unit clauses will be permanently added.
        if(!res.add_clause(gen.id, gen.atoms))
          return true;
        break;

      case S_Del:
        res.remove_clause(gen.id);
        break;
      
      case S_Infer:
//        if(!res.check_clause(gen.atoms, gen.ants)) {
        if(verbosity > 2) 
          fprintf(stderr, "> clause %d\n", gen.id);

//        if(!res.check_clause_linear(gen.atoms, gen.ants))
        if(!res.check_clause(gen.atoms, gen.ants))
        {
          if(verbosity > 1)
            fprintf(stderr, "Error: derivation of clause %d failed.\n", gen.id);
          return false;
        }
        // Empty clause derived
        if(gen.atoms.size() == 0)
          return true;

        if(!res.add_clause(gen.id, gen.atoms))
          return true;
//        res.add_clause(gen.id, gen.atoms);
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
  opts o;
  argc = parse_options(o, argc, argv);

  if(o.in_mode == opts::I_Bool) {
    // In the bool case, we need to parse
    // the atom table.
    gzFile lit_file = gzopen(argv[1], "rb");
    Parse::StreamBuffer lit_stream(lit_file);

    // Read in the atom semantics
    AtomTable atable;
    read_atoms(lit_stream, atable);

    gzclose(lit_file);

    // Now, read the proof directives
    gzFile proof_file = gzopen(argv[2], "rb");
    Parse::StreamBuffer proof_stream(proof_file);
    LogParser<Parse::StreamBuffer> parser(proof_stream, atable);
    if(verify_unsat(parser, o.verbosity)) {
      if(o.verbosity > 0)
        printf("s VERIFIED\n");
      return 0;
    }
    if(o.verbosity > 0)
      printf("s INCOMPLETE\n");
    return 1;
  } else {
    // In the sem case, we skip directly to reading the proof
    // directives
    gzFile proof_file = gzopen(argv[1], "rb");
    Parse::StreamBuffer proof_stream(proof_file);
    SemParser<Parse::StreamBuffer> parser(proof_stream);
    if(verify_unsat(parser, o.verbosity)) {
      if(o.verbosity > 0)
        printf("s VERIFIED\n");
      return 0;
    }
    if(o.verbosity > 0)
      printf("s INCOMPLETE\n");
    return 1;

    return 1;
  }

}
