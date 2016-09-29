#include <cassert>
#include <cstring>
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
      out_mode(O_Sem), drop_unit(false), keep_alias(false) {
  }
  const char* infile;
  const char* outfile; 
  out_t out_mode;
  bool drop_unit;
  bool keep_alias;
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

void extract_dom(fdres_env& env, int var, vec<atom>& lemmas) {
  const domain& d(env[var]);
  if(d.lb > INT_MIN)
    lemmas.push(atom { var, Gt, d.lb-1 });
  if(d.ub < INT_MAX)
    lemmas.push(atom { var, Le, d.ub });
  for(int k : d.holes)
    lemmas.push(atom { var, Neq, k });
}

void simplify(fdres_env& env, vec<atom>& lemma) {
  for(atom at : lemma) {
    if(!env.post(~at)) {
      fprintf(stderr, "WARNING: Attempted to simplify tautology.\n");
      env.clear();
      return;
    }
  }
  // Now extract the entailed domains of changed variables,
  // and negate them
  vec<atom> dom_atoms;
  for(int v : env.changes) {
    extract_dom(env, v, dom_atoms);
  }

  lemma.clear();
  for(atom at : dom_atoms)
    lemma.push(~at);
  env.clear();
}

const char* op_str[] = { ">", "<=", "!=", "=" };
void print_atom(atom at) {
  fprintf(stdout, " v%d %s %d", at.var, op_str[at.kind], at.val);
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

struct clause_info_t { int id ; int count; bool seen; bool used; };

/*
class clause_set {
public:
  clause_set(void) : count(0), next_id(1) { }

  struct info_t { int id; int pos; int count; bool seen; bool uses };
  struct ref_t { int idx; };

  ref_t add(vec<atom>& cl_atoms, vec<ref_t>& cl_ants) {
    if(count == dense.size()) {
      dense.push(count);
      info.push();
      _atoms.push();
      _ants.push();
    }
    int idx = dense[count];
    info[idx] = { next_id++, count, 1, false, false };
      
    for(atom at : cl_atoms)
      _atoms[idx].push(at);
    for(ref_t ant : cl_ants) {
      _ants[idx].push(ant.idx);
      info[ant.idx].uses++;
    }

    return ref_t { idx };
  };

  void remove(ref_t r) {
    info[r.idx].count--;
    if(info[r.idx].count > 0)
      return;
      
    int rep = dense[--count];
    int r_pos = info[r.idx].pos;

    // Maintain the cross-references and
    // de-facto free-list 
    info[rep].pos = r_pos;
    dense[r_pos] = rep;
    info[r.idx].pos = count;
    dense[count] = r.idx;

    _atoms[r.idx].clear();
    _ants[r.idx].clear();
  }

  info_t& operator[](ref_t r) { return _info[r.idx]; }
  vec<atom>& ants(ref_t r) { return _ants[r.idx]; } 
  vec<int>& atoms(ref_t r) { return _atoms[r.idx]; } 

protected:
  vec<info_t> _info;
  vec< vec<atom> > _atoms;
  vec< vec<int> > _ants;

  vec<int> dense;
  int count;

  int next_id;
};
*/


int parse_options(opts& o, int argc, char** argv) {
  int jj = 1;
  for(int ii = 1; ii < argc; ++ii) {
    if(strcmp(argv[ii], "-drop-unit") == 0) {
      fprintf(stderr, "WARNING: -drop-unit not yet implemented\n");
      o.drop_unit = true;
    } else if(strcmp(argv[ii], "-bool") == 0) {
      o.out_mode = opts::O_Bool;
    } else if(strcmp(argv[ii], "-keep-alias") == 0) {
      o.keep_alias = true;
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
  clause_info.push(clause_info_t { 0, 0, false, false });

  vec<int> live_ants;

  int unused_clauses = 0;

  while(!parser.isEof()) {
    StepT step = parser.next();
    
    switch(step) {
      case S_Comm:
        print_comment(parser.comment);
        break;
      case S_Intro:
        // Dump tautologies
        if(!is_tauto(env, parser.atoms)) {
          simplify(env, parser.atoms);
          int id = clause_info.size();
          clause_info.push(clause_info_t { id, 1, false, false });
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
              if(!clause_info[id].used)
                unused_clauses++;

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
            if(it != live_clauses.end()) {
              int id = (*it).second;
              if(!clause_info[id].seen)
                live_ants.push((*it).second);
              clause_info[id].seen = true;
            }
          }
          for(int c_id : live_ants)
            clause_info[c_id].seen = false;

          if(live_ants.size() > 0) {
            if(!o.keep_alias && live_ants.size() == 1) {
              // Alias
              clause_info[live_ants[0]].count++;
              live_clauses.insert(std::make_pair(parser.id, live_ants[0]));
            } else {
              // Actually a derivation
              simplify(env, parser.atoms);
              for(int ant : live_ants)
                clause_info[ant].used = true;

              int id = clause_info.size();
              clause_info.push(clause_info_t { id, 1, false, false });
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
    
  fprintf(stderr, "Unused: %d clauses\n", unused_clauses);

  return 0;
}
