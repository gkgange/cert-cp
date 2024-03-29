#ifndef LOG_PARSER__H
#define LOG_PARSER__H

#include <cctype>
#include <sstream>
#include <vector>
#include <unordered_map>
#include "ParseUtils.h"
#include "fdres-types.h"

#define VAR_UNDEF (INT_MAX>>2)

class VarTable {
public:
  VarTable(void) { }
  int get(std::string& s) {
    auto it = table.find(s);
    if(it != table.end())
      return (*it).second;
    int idx = names.size();
    names.push_back(s);
    table[s] = idx;
    return idx;    
  }

  unsigned int size(void) {
    return names.size();
  }

  std::string operator[](int idx) const { return names[idx]; }
protected:
  std::vector<std::string> names;
  std::unordered_map<std::string, int> table;
};

// typedef std::unordered_map<std::string, int> VarTable;

// Parse steps
enum StepT { S_Intro, S_Del, S_Infer, S_Comm };

// Assumes atoms are in a
// contiguous range.
class AtomTable {
public:
  AtomTable(void)
    : var_max(0) { }

  void set(int i, atom at) {
    assert(i > 0);
    if(i >= atoms.size()) {
      while(atoms.size() <= i)
        atoms.push(at_Undef);
    }
    atoms[i] = at;
    var_max = std::max(var_max, (int) var(at));
  }

  atom operator[](int i) const {
    assert(i != 0);
    if(i < 0) {
      assert(-i < atoms.size());
      return ~atoms[-i];
    } else {
      assert(i < atoms.size());
      return atoms[i];
    }
  }

  int nvars(void) const { return var_max+1; }
protected:
  int var_max;
  vec<atom> atoms;
};

enum OpT { Op_Lt, Op_Le, Op_Gt, Op_Ge, Op_Eq, Op_Ne };

template<class In>
void chomp(In& in, const char* str) {
  if(!Parse::eagerMatch(in, str)) {
    assert(0 && "Match failed.");
  }
}

template<class In>
void wchomp(In& in, const char* str) {
  Parse::skipWhitespace(in);
  chomp(in, str);
}

template<class In>
OpT read_op(In& in) {
  Parse::skipWhitespace(in);
  char c = *in; ++in;
  switch(c) {
    case '=': 
      return Op_Eq;
    case '!':
      chomp(in, "=");
      return Op_Ne;
    case '<':
      if(*in == '=') {
        ++in; return Op_Le;
      } else {
        return Op_Lt;
      }
    case '>':
      if(*in == '=') {
        ++in; return Op_Ge;
      } else {
        return Op_Gt;
      }
    default:
      assert(0 && "Expected op.");   
      return Op_Eq;
  }
}

template<class In>
atom read_satom(In& in) {
  Parse::skipWhitespace(in);
  wchomp(in, "v");
  int var = Parse::parseInt(in);
  OpT op = read_op(in);
  int val = Parse::parseInt(in);

  switch(op) {
    case Op_Eq:  
      return atom { var, Eq, val };
    case Op_Ne:  
      return atom { var, Neq, val };
      break;
    case Op_Lt:  
      return atom { var, Le, val-1 };
    case Op_Le:  
      return atom { var, Le, val };
    case Op_Gt:  
      return atom { var, Gt, val };
    case Op_Ge:
      return atom { var, Gt, val-1 };
    default:
      assert (0 && "Unreachable");
      return atom { };
  }
}

static inline bool is_id_char(char c) {
  return isalnum(c) || c == '_';
}

template<class In>
std::string read_ident(In& in) {
  Parse::skipWhitespace(in);
  std::stringstream ss;
  while(is_id_char(*in)) {
    ss << ((char) *in);
    ++in;
  }
  return ss.str();
}

/*
static inline int get_vid(VarTable& vtbl, std::string& ident) {
  auto it = vtbl.find(ident);
  if(it != vtbl.end())
    return (*it).second;
  int var = vtbl.size()+1;
  vtbl[ident] = var;
  return var;
}
*/

template<class In>
atom read_satom(In& in, VarTable& vtbl) {
  Parse::skipWhitespace(in);
  std::string ident = read_ident(in);
  unsigned int var = vtbl.get(ident);
  OpT op = read_op(in);
  int val = Parse::parseInt(in);

  switch(op) {
    case Op_Eq:  
      return atom { var<<2|Eq, val };
    case Op_Ne:  
      return atom { var<<2|Neq, val };
      break;
    case Op_Lt:  
      return atom { var<<2|Le, val-1 };
    case Op_Le:  
      return atom { var<<2|Le, val };
    case Op_Gt:  
      return atom { var<<2|Gt, val };
    case Op_Ge:
      return atom { var<<2|Gt, val-1 };
    default:
      assert (0 && "Unreachable");
      return atom { };
  }
}

template<class In>
void read_atomdef(In& in, AtomTable& tbl) {
  int id = Parse::parseInt(in); 
  
  wchomp(in, "[");
  /*
  wchomp(in, "v");
  int var = Parse::parseInt(in);
  OpT op = read_op(in);
  int val = Parse::parseInt(in);
  */
  atom at(read_satom(in));
  wchomp(in, "]");

  // printf("[|x%d op %d|]\n", var, val);
  tbl.set(id, at);
}

template<class In>
void read_atomdef(In& in, AtomTable& tbl, VarTable& vtbl) {
  int id = Parse::parseInt(in); 
  
  wchomp(in, "[");
  /*
  wchomp(in, "v");
  int var = Parse::parseInt(in);
  OpT op = read_op(in);
  int val = Parse::parseInt(in);
  */
  atom at(read_satom(in, vtbl));
  wchomp(in, "]");

  // printf("[|x%d op %d|]\n", var, val);
  tbl.set(id, at);
}


template<class In>
void read_atoms(In& in, AtomTable& tbl) {
  while(!Parse::isEof(in)) {
    read_atomdef(in, tbl);
    if(!Parse::isEof(in))
      Parse::skipWhitespace(in);
  }
}

template<class In>
void read_atoms(In& in, AtomTable& tbl, VarTable& vtbl) {
  while(!Parse::isEof(in)) {
    read_atomdef(in, tbl, vtbl);
    if(!Parse::isEof(in))
      Parse::skipWhitespace(in);
  }
}

// Original log parser; requires dereferencing
// literals.
// WARNING: AtomTable must remain alive in the
// enclosing scope.
template<class In>
class LogParser {
  public:
    LogParser(In& _in, AtomTable& _at) 
      : in(_in), at(_at) { }
           
    StepT next(void);
    bool isEof(void) {
      Parse::skipWhitespace(in);
      return *in == EOF;
    }

    int id;
    vec<atom> atoms;
    vec<int> ants;
    std::string comment;
  protected:    
    void read_clause(void);

    In& in;
    AtomTable& at;
};

/*
template<class In>
void read_atoms(In& in, AtomTable& tbl) {
  while(!Parse::isEof(in)) {
    read_atom(in, tbl);
    if(!Parse::isEof(in))
      Parse::skipWhitespace(in);
  }
}
*/

// Assumes a textual form with atomic
// constraints directly included.
template<class In>
class SemParser {
public:
  SemParser(In& _in)
    : in(_in) { }

  StepT next(void);
  StepT next(VarTable& vtbl);
  bool isEof(void) {
    Parse::skipWhitespace(in);
    return *in == EOF;
  }

  void read_clause(void);
  void read_clause(VarTable& vtbl);

  // Temporary storage for
  // the most recent token.
  int id;
  vec<atom> atoms;
  vec<int> ants;
  std::string comment;

protected:    
  In& in;
};

template<class In>
void LogParser<In>::read_clause(void) {
  atoms.clear();   
  Parse::skipWhitespace(in);
  while(*in != '0') {
    int lid = Parse::parseInt(in);
    if(var(at[lid]) == VAR_UNDEF) {
      fprintf(stderr, "ERROR: unidentified atom %d", lid);
      exit(1);
    }
    atoms.push(at[lid]);
    Parse::skipWhitespace(in);
  }
  ++in;
}

template<class In>
void readInts(In& in, vec<int>& args) {
  args.clear();
  Parse::skipWhitespace(in);
  while(*in != '0') {
    args.push(Parse::parseInt(in));
    Parse::skipWhitespace(in);
  }
  ++in;
}

template<class In>
std::string read_line(In& in) {
  std::stringstream ss; 
  while(*in != '\n') {
    if(isEof(in))
     return ss.str();
    ss << ((char) *in);
    ++in; 
  }
  ++in;
  return ss.str();
}

template<class In>
StepT LogParser<In>::next(void) {
  Parse::skipWhitespace(in);
  char c = *in;
  if(c == 'c')
  {
    // Comment (or hint) line
    // Urgh -- for the simplifier, we need to recover these.
    // skipLine(in);
    ++in;
    Parse::skipWhitespace(in);
    comment = read_line(in);
    return S_Comm;
  } else if (c == 'd') {
    // Deletion line.
    ++in;
    id = Parse::parseInt(in);
    return S_Del;
  } else {
    // Either introduction or derivation
    id = Parse::parseInt(in);
    read_clause();
    Parse::skipWhitespace(in);
    if(*in == '0')
    {
      // Axiom
      ++in;
      return S_Intro;
    } else {
      readInts(in, ants);
      return S_Infer;
    }
  }
  Parse::skipWhitespace(in);
}

template<class In>
void SemParser<In>::read_clause(void) {
  atoms.clear();
  Parse::skipWhitespace(in);
  while(*in != '0') {
    atoms.push(read_satom(in));
    Parse::skipWhitespace(in);
  }
  ++in;
}

template<class In>
void SemParser<In>::read_clause(VarTable& vtbl) {
  atoms.clear();
  Parse::skipWhitespace(in);
  while(*in != '0') {
    atoms.push(read_satom(in, vtbl));
    Parse::skipWhitespace(in);
  }
  ++in;
}


template<class In>
StepT SemParser<In>::next(void) {
  Parse::skipWhitespace(in);
  char c = *in;
  if(c == 'c')
  {
    // Comment (or hint) line
    ++in;
    Parse::skipWhitespace(in);
    comment = read_line(in);
    return S_Comm;
  } else if (c == 'd') {
    // Deletion line.
    ++in;
    id = Parse::parseInt(in);
    return S_Del;
  } else {
    // Either introduction or derivation
    id = Parse::parseInt(in);
    read_clause();
    Parse::skipWhitespace(in);
    if(*in == '0')
    {
      // Axiom
      ++in;
      return S_Intro;
    } else {
      readInts(in, ants);
      return S_Infer;
    }
  }
  Parse::skipWhitespace(in);
}

template<class In>
StepT SemParser<In>::next(VarTable& vtbl) {
  Parse::skipWhitespace(in);
  char c = *in;
  if(c == 'c')
  {
    // Comment (or hint) line
    ++in;
    Parse::skipWhitespace(in);
    comment = read_line(in);
    return S_Comm;
  } else if (c == 'd') {
    // Deletion line.
    ++in;
    id = Parse::parseInt(in);
    return S_Del;
  } else {
    // Either introduction or derivation
    id = Parse::parseInt(in);
    read_clause(vtbl);
    Parse::skipWhitespace(in);
    if(*in == '0')
    {
      // Axiom
      ++in;
      return S_Intro;
    } else {
      readInts(in, ants);
      return S_Infer;
    }
  }
  Parse::skipWhitespace(in);
}


#endif
