#include <cassert>
#include <unordered_set>
#include "ParseUtils.h"
#include "fdres-types.h"
#include "fdres-state.h"
#include "log-parser.h"
#include "fdres-env.h"

#define ERROR assert(0 && "FAILURE")

// Inline literal semantics and discard any tautologies.
// i.e. x < 3 => x < 4.

struct opts {
  enum out_t { O_Bool, O_Sem };

  opts(void)
    : infile(nullptr), outfile(nullptr),
      out_mode(O_Sem), drop_unit(false) {
  }
  const char* infile;
  const char* outfile; 
  out_t out_mode;
  bool drop_unit;
};

bool is_tauto(fdres_env& env, vec<atom>& lemma) {
  for(atom at : lemma) {
    if(!env.post(~at)) {
      env.clear();
      return true;
    }
  }
  env.clear();
  return false;
}

const char* op_str[] = { ">", "<=", "!=", "=" };
void print_atom(atom at) {
  fprintf(stdout, " v%d%s%d", at.var, op_str[at.kind], at.val);
}
void print_intro(int id, vec<atom>& lemma) {
  fprintf(stdout, "%d", id);
  for(atom at : lemma)
    print_atom(at);
  fprintf(stdout, " 0 0\n");
}

void print_del(int id) {
  fprintf(stdout, "d %d\n", id);
}

void print_infer(int id, vec<atom>& lemma, vec<int>& ants) {
  fprintf(stdout, "%d", id);
  for(atom at : lemma)
    print_atom(at);
  fprintf(stdout, " 0");

  for(int ant : ants)
    fprintf(stdout, " %d", ant);
  fprintf(stdout, " 0\n");
}

void print_comment(std::string& comment) {
  fprintf(stdout, "c %s\n", comment.c_str());
}

struct clause_info_t { int id ; int count; };

int parse_options(opts& o, int argc, char** argv) {
  int jj = 1;
  for(int ii = 1; ii < argc; ++ii) {
    if(strcmp(argv[ii], "-drop-unit") == 0) {
      fprintf(stderr, "WARNING: -drop-unit not yet implemented\n");
      o.drop_unit = true;
    } else if(strcmp(argv[ii], "-bool") == 0) {
      o.out_mode = opts::O_Bool;
    } else {
      argv[jj++] = argv[ii];
    }
  }
  return jj;
}

int main(int argc, char** argv) {
  // Load the proof file. 
  opts o;
  argc = parse_options(o, argc, argv);

  // gzFile in_file = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
  gzFile lit_file = gzopen(argv[1], "rb");
  Parse::StreamBuffer lit_stream(lit_file);

  // Read in the atom semantics
  AtomTable atable;
  read_atoms(lit_stream, atable);

  gzclose(lit_file);

  // Allocate the environment
  fdres_env env(atable.nvars());

  // Now, read the proof directives
  gzFile proof_file = gzopen(argv[2], "rb");
  Parse::StreamBuffer proof_stream(proof_file);
  LogParser<Parse::StreamBuffer> parser(proof_stream, atable);

  std::unordered_map<int, int> live_clauses;
  vec<clause_info_t> clause_info;
  clause_info.push(clause_info_t { 0, 0 });

  vec<int> live_ants;

  while(!parser.isEof()) {
    StepT step = parser.next();
    
    switch(step) {
      case S_Comm:
        print_comment(parser.comment);
        break;
      case S_Intro:
        // Dump tautologies
        if(!is_tauto(env, parser.atoms)) {
          int id = clause_info.size();
          clause_info.push(clause_info_t { id, 1 });
          print_intro(id, parser.atoms);
          live_clauses.insert(std::make_pair(parser.id, id));
        }
        break; 
      case S_Del:
        {
          auto it = live_clauses.find(parser.id);
          if(it != live_clauses.end()) {
            int id = (*it).second;
            if(clause_info[id].count == 1) {
              print_del(id);
            }
            clause_info[id].count--;
            live_clauses.erase(it);
          }
        }
        break;
      case S_Infer:
        {
          live_ants.clear();
          for(int ant : parser.ants) {
            auto it = live_clauses.find(ant);
            if(it != live_clauses.end())
              live_ants.push((*it).second);
          }
          if(live_ants.size() > 0) {
            if(live_ants.size() == 1) {
              // Alias
              clause_info[live_ants[0]].count++;
              live_clauses.insert(std::make_pair(parser.id, live_ants[0]));
            } else {
              // Actually a derivation
              int id = clause_info.size();
              clause_info.push(clause_info_t { id, 1 });
              print_infer(id, parser.atoms, live_ants);
              live_clauses.insert(std::make_pair(parser.id, id));
            }
          } else {
            // Resolving tautologies _should_ still be a tautology
            if(!is_tauto(env, parser.atoms))
              ERROR;
          }
        }
        break;
    }
  }
  gzclose(proof_file);

  return 0;
}
