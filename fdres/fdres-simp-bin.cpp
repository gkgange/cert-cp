#include <cassert>
#include <cstring>
#include <unordered_set>
#include "ParseUtils.h"
#include "fdres-types.h"
#include "fdres-state.h"
#include "log-parser.h"
#include "fdres-env.h"

#define ERROR assert(0 && "FAILURE")

// #define DOMAIN_COMMIT

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
  // Cheap check -- tautologies usually only talk about one variable
  if(lemma.size() == 0)
    return false;

  unsigned int v = var(lemma[0]);
  for(int ii = 1; ii < lemma.size(); ii++) {
    if(var(lemma[ii]) != v)
      return false;
  }

  for(atom at : lemma) {
    if(!env.post(~at)) {
      env.clear();
      return true;
    }
  }
  env.clear();
  return false;
}

// Only emit those atoms which aren't entailed by the root domain.
void extract_dom(fdres_env& env, unsigned int var, vec<atom>& lemmas) {
#ifndef DOMAIN_COMMIT
  const domain& d(env[var]);
  if(d.lb == d.ub) {
    lemmas.push(atom { var<<2|Eq, d.lb });
    return;
  }
  if(d.lb > INT_MIN)
    lemmas.push(atom { var<<2|Gt, d.lb-1 });
  if(d.ub < INT_MAX)
    lemmas.push(atom { var<<2|Le, d.ub });
  for(int k : d.holes)
    lemmas.push(atom { var<<2|Neq, k});
#else
  const domain& d(env[var]);
  const domain& d0(env.dom_0[var]);
  if(d.lb == d.ub) {
    lemmas.push(atom { var<<2|Eq, d.lb });
    return;
  }
  if(d.lb > d0.lb)
    lemmas.push(atom { var<<2|Gt, d.lb-1 });
  if(d.ub < d0.ub)
    lemmas.push(atom { var<<2|Le, d.ub });

  iset::iterator it = d.holes.begin();
  iset::iterator it0 = d0.holes.begin();

  while(it0 != d0.holes.end()) {
    if(*it == *it0) {
      ++it; ++it0;
    } else {
      lemmas.push(atom { var<<2|Neq, *it });
      ++it;
    }
  }
  for(; it != d.holes.end(); ++it)
    lemmas.push(atom { var<<2|Neq, *it});
#endif
}

void simplify(fdres_env& env, vec<atom>& lemma) {
#ifdef DOMAIN_COMMIT
  // Drop any trivially false atoms
  atom* tl = lemma.begin();
  for(atom at : lemma) {
    if(env.value(at) != l_False) {
      *tl = at;
      ++tl;
    }
  }
  lemma.dropTo(tl - lemma.begin());
#endif
  
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

template<class T>
void write_vec(FILE* f, vec<T>& elts) {
  fwrite(&elts._size(), sizeof(unsigned int), 1, f);
  fwrite(elts.begin(), sizeof(T), elts.size(), f);
}

void write_infer(FILE* f, unsigned int id, vec<atom>& atoms, vec<int>& ants) {
  fwrite(&id, sizeof(unsigned int), 1, f);
  write_vec(f, atoms);
  write_vec(f, ants);
}

#define HINT_TAG INT_MAX
#define DEL_TAG (INT_MAX-1)

unsigned int hint_buf[] = { HINT_TAG, 0 };

/*
void write_hint(FILE* f, unsigned int hint) {
  hint_buf[1] = hint;
  write_hint(hint_buf, sizeof(unsigned int), 2, f);
}
*/

/*
void print_del(int id) {
  fprintf(stdout, "d %d\n", id);
}
*/

struct clause_info_t { int id ; int count; bool seen; bool used; };

class clause_set {
public:
  clause_set(void) : count(0), next_id(1),
  active_hint(0) {
    hint_buf[0] = HINT_TAG; hint_buf[1] = 0;
  }

  struct info_t { int id; int pos; int count; bool seen; bool emitted; };
  struct ref_t { int idx; int id; };

  void set_hint(unsigned int s) {
    active_hint = s;
  }
  unsigned int hint(ref_t r) { return _hint[r.idx]; }

  void write_hint(FILE* f, unsigned int s) {
    hint_buf[1] = s;
    fwrite(hint_buf, sizeof(unsigned int), 2, f);
  }

  ref_t add(vec<atom>& cl_atoms) {
    vec<ref_t> ants;
    return add(cl_atoms, ants);
  }
  ref_t add(vec<atom>& cl_atoms, vec<ref_t>& cl_ants) {
    if(count == dense.size()) {
      dense.push(count);
      _info.push();
      _atoms.push();
      _ants.push();
      _uses.push();
      _hint.push();
    }

    int idx = dense[count];
    int id = next_id++;
    _info[idx] = { id, count, 1, false, false };
    count++;

    ref_t r { idx, id };
      
    for(atom at : cl_atoms)
      _atoms[idx].push(at);
    for(ref_t ant : cl_ants) {
      _ants[idx].push(ant);
      _uses[ant.idx].push(r);
    }

    if(cl_ants.size() == 0)
      _hint[idx] = active_hint;

    return r;
  };

  void inc_ref(ref_t r) {
    _info[r.idx].count++;
  }

  // Returns true if no references remain
  bool dec_ref(ref_t r) {
    assert(!is_stale(r));
    assert(count > 0);

    assert(_info[r.idx].count > 0);
    _info[r.idx].count--;
    if(_info[r.idx].count > 0)
      return false;
    /*
    _atoms[r.idx].clear();
    for(int ant_idx : _ants[r.idx]) {
      _uses[ant_idx]--;
    }
    _ants[r.idx].clear();
    */
    pending_deletes.push(r.idx);
    return true;
  }

  info_t& operator[](ref_t r) { return _info[r.idx]; }
  vec<ref_t>& ants(ref_t r) { return _ants[r.idx]; } 
  vec<atom>& atoms(ref_t r) { return _atoms[r.idx]; } 

  bool is_stale(ref_t r) { return r.id != _info[r.idx].id; }

  void flush_deletions(FILE*);
protected:
  void real_delete(int ci) {
    int rep = dense[--count];
    int r_pos = _info[ci].pos;

    // Maintain the cross-references and
    // de-facto free-list 
    _info[rep].pos = r_pos;
    dense[r_pos] = rep;
    _info[ci].pos = count;
    dense[count] = ci;

    _ants[ci].clear();
    _uses[ci].clear();
    _atoms[ci].clear();
  }

  vec<info_t> _info;
  vec< vec<atom> > _atoms;
  vec< vec<ref_t> > _ants;
  vec< vec<ref_t> > _uses;
  vec<unsigned int> _hint;

  vec<int> dense;
  int count;

  int next_id;
  vec<int> pending_deletes;

public:
//  std::string active_hint;
//  std::string last_hint;

  unsigned int active_hint;
  unsigned int hint_buf[2];  
  vec<unsigned int> del_buf;
};


vec<int> empty;
vec<int> ant_ids;
vec<unsigned int> del_buf;

void emit_clause(FILE* f, clause_set& cs, clause_set::ref_t cl) {
  clause_set::info_t& cinfo(cs[cl]);
  // If the clause has already been
  // output, terminate
  if(cinfo.emitted)
    return;
  // Assuming deletion handling is correct, there
  // shouldn't be any stale references
  assert(cinfo.id == cl.id);

  cinfo.emitted = true;
  vec<clause_set::ref_t>& ants(cs.ants(cl));
  for(clause_set::ref_t ant : cs.ants(cl)) {
    emit_clause(f, cs, ant);
  }
  if(ants.size() == 0 && cs.hint_buf[1] != cs.hint(cl)) {
    cs.write_hint(f, cs.hint(cl));
  }
  
  // Dereference ants
  ant_ids.clear();
  for(auto aref : ants)
    ant_ids.push(aref.id);
  
  write_infer(f, cl.id, cs.atoms(cl), ant_ids);
}

void clause_set::flush_deletions(FILE* f) {
  // For each deleted clause, check whether some
  // reference survives
  for(int ci : pending_deletes) {
    assert(_info[ci].pos < count);

    // If so, the subtree rooted at that use
    // must be emitted
    for(ref_t use : _uses[ci]) {
      if(!is_stale(use) && _info[use.idx].count > 0) {
        emit_clause(f, *this, use);
      }
    }
  }
  // Now, emit deletion information for any clause
  // that has been emitted,
  // and clear expired data
  for(int ci : pending_deletes) {
    if(_info[ci].emitted) {
      del_buf.push(DEL_TAG); del_buf.push(_info[ci].id);
    }
    real_delete(ci);
    /*
    _ants[ci].clear();
    _uses[ci].clear();
    _atoms[ci].clear();
    */
  }
  fwrite(del_buf.begin(), sizeof(unsigned int), del_buf.size(), f);

  del_buf.clear();
  pending_deletes.clear();

}

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

// Check that for each atom in inf, ~Ant |- ~at
static bool is_alias(fdres_env& env, vec<atom>& inf, vec<atom>& ant) {
  for(atom at : ant) {
    if(!env.post(~at)) {
      ERROR; // ant is a tautology 
      env.clear();
      return false;
    }
  }
  for(atom at : inf) {
    if(env.value(at) != l_False) {
      env.clear();
      return false;
    }
  }
  env.clear();
  return true;
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
  VarTable vtable;
  read_atoms(lit_stream, atable, vtable);
  gzclose(lit_file);

  // FILE* outfile = fopen(opts.outfile, "wb");
  FILE* outfile = stdout;
//  FILE* outfile = fopen("log.fdres", "wb");
  // Compute the header length.
  int hdr_sz = sizeof(unsigned int);
  for(unsigned int ii = 0; ii < vtable.size(); ii++) {
    hdr_sz += sizeof(unsigned int) + vtable[ii].size();
  }
  // Now output all var identifiers
  fwrite(&hdr_sz, sizeof(unsigned int), 1, outfile);
  unsigned int nvars = vtable.size();
  fwrite(&nvars, sizeof(unsigned int), 1, outfile);
  for(unsigned int ii = 0; ii < vtable.size(); ii++) {
    unsigned int sz = vtable[ii].size();
    fwrite(&sz, sizeof(unsigned int), 1, outfile);
    fwrite(vtable[ii].c_str(), sizeof(char), sz, outfile);
  }
  // assert(sizeof(unsigned int) + hdr_sz == ftell(outfile));

  // Allocate the environment
  fdres_env env(atable.nvars());

  // Now, read the proof directives
  gzFile proof_file = gzopen(argv[2], "rb");
  Parse::StreamBuffer proof_stream(proof_file);
  LogParser<Parse::StreamBuffer> parser(proof_stream, atable);


  std::unordered_map<int, clause_set::ref_t> live_clauses;
  // vec<clause_info_t> clause_info;
  clause_set clause_info;
  // clause_info.push(clause_info_t { 0, 0, false, false });

  vec<clause_set::ref_t> live_ants;

  while(!parser.isEof()) {
    StepT step = parser.next();
    
    switch(step) {
      case S_Comm:
        // print_comment(parser.comment);
        // Works okay, because it strtol returns 0 on non-integer.
        clause_info.set_hint(strtol(parser.comment.c_str()+1, NULL, 10));
        break;
      case S_Intro:
        // Dump tautologies
        clause_info.flush_deletions(outfile);
        if(!is_tauto(env, parser.atoms)) {
          simplify(env, parser.atoms);
          // int id = clause_info.size();
          // clause_info.push(clause_info_t { id, 1, false, false });
          clause_set::ref_t ref(clause_info.add(parser.atoms));
          // print_intro(id, parser.atoms);
          // live_clauses.insert(std::make_pair(parser.id, id));
          live_clauses.insert(std::make_pair(parser.id, ref));
        }
        break; 
      case S_Del:
        {
          auto it = live_clauses.find(parser.id);
          if(it != live_clauses.end()) {
            clause_set::ref_t id = (*it).second;
            // Printing is now handled by
            // flush_deletions
            /*
            if(clause_info[id].count == 1) {
              if(!clause_info[id].used)
                unused_clauses++;
              // print_del(id);
              live_clauses.erase(it);
            }
            clause_info[id].count--;
            */
            if(clause_info.dec_ref(id)) {
              live_clauses.erase(it);
            }
          }
        }
        break;
      case S_Infer:
        {
          clause_info.flush_deletions(outfile);
          
          // Resolve non-tautology antecedents to the
          // corresponding references
          live_ants.clear();
          for(int ant : parser.ants) {
            auto it = live_clauses.find(ant);
            if(it != live_clauses.end()) {
              clause_set::ref_t id = (*it).second;
              // Don't duplicate antecedents
              if(!clause_info[id].seen)
                live_ants.push((*it).second);
              clause_info[id].seen = true;
            }
          }
          for(clause_set::ref_t c_id : live_ants)
            clause_info[c_id].seen = false;

          if(live_ants.size() > 0) {
#if 0
            //=========================
            // GKG: It turns out that, in some cases, it's necessary to have self-resolution.
            // Consider c1: [x < 3] \/ [x > 4], c2: [x = 3 \/ x = 4].
            // By unit propagation we get nothing. But by self-resolution, we can get:
            // c1a: [x != 3], c1b: [x != 4].
            //=========================

            if(!o.keep_alias && live_ants.size() == 1) {
              // Alias
              // clause_info[live_ants[0]].count++;
              clause_info.inc_ref(live_ants[0]);
              live_clauses.insert(std::make_pair(parser.id, live_ants[0]));
            } else {
              // Actually a derivation
              // Perform self-subsumption
              simplify(env, parser.atoms);

              clause_set::ref_t ref(clause_info.add(parser.atoms, live_ants));
              live_clauses.insert(std::make_pair(parser.id, ref));

              if(parser.atoms.size() == 0) {
                emit_clause(outfile, clause_info, ref);
              }
            }
#else
            // Always perform self-subsumption
            simplify(env, parser.atoms);
            if(!o.keep_alias && live_ants.size() == 1 && is_alias(env, parser.atoms, clause_info.atoms(live_ants[0]))) {
              clause_info.inc_ref(live_ants[0]);
              live_clauses.insert(std::make_pair(parser.id, live_ants[0]));
            } else {
              clause_set::ref_t ref(clause_info.add(parser.atoms, live_ants));
              live_clauses.insert(std::make_pair(parser.id, ref));

              if(parser.atoms.size() == 0) {
                emit_clause(outfile, clause_info, ref);
              }
            }
#endif

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
