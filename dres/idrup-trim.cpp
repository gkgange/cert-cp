#include <boost/iostreams/device/mapped_file.hpp>
#include "ParseUtils.h"
#include "idrup-types.h"
#include "idrup-state.h"
#include <cstdio>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

enum Instr { D_Intro, D_Del, D_Infer, D_Nop };

template<class T>
void parseClause(T& in, vec<lit>& cl)
{
  cl.clear();
  Parse::skipWhitespace(in);
  int l;
  while((l = Parse::parseInt(in)) != 0)
  {
    if(l < 0)
      cl.push((-l)<<1);
    else
      cl.push(l<<1|1);
  }
}

class LineBuf {
  static const int init_sz = 200;
public:
  LineBuf()
    : _is_eof(true), data((char*) malloc(sizeof(char)*init_sz)), sz(init_sz),
      pos(0), _end(0)
  { }
  
  void operator++(void)
  {
    pos++;
  }

  char& operator*(void) { return data[pos]; }

  void push(char c)
  {
    if(_end == sz)
    {
      sz *= 1.5;
      data = (char*) realloc(data, sizeof(char)*sz);
      assert(data);
    }
    data[_end++] = c;  
  }

  void push(char* start, char* end)
  {
    for(; start < end; start++)
      push(*start); 
  }

  bool is_eof(void) { return _is_eof; }
  void make_eof(void) { _is_eof = true; }

  void clear(void) {
    pos = 0;
    _end = 0;
    _is_eof = false;
  }

  char* begin() { return data+pos; }
  char* end() { return data+_end; }

protected:
  bool _is_eof;

  char* data;
  int sz;
  int pos;
  int _end;
};

bool isEof(LineBuf& buf) { return buf.is_eof(); }

class MFile {
public:
  MFile(const char* filename)
    : file(open(filename, O_RDONLY))
  {
    struct stat sb;
    fstat(file, &sb);
    start = (char*) mmap(NULL, sb.st_size, PROT_READ, MAP_SHARED, file, 0); 
    pos = start;
    end = start + sb.st_size;
  }

  ~MFile(void) {
    close(file);
  }

  void next_line(LineBuf& line)
  {
    if(pos == end)
    {
      line.make_eof();
    } else {
      line.clear();
      char* lstart = pos;
      while(pos != end && *pos != '\n')
        pos++;

      line.push(lstart, pos);
      line.push('\0');
      if(pos != end)
        pos++;
    }
  }

  void prev_line(LineBuf& line)
  {
    if(pos == start)
    {
      line.make_eof();
    } else {
      line.clear();
      pos--;
      char* lend = pos;
      
      while(start < pos && *(pos-1) != '\n')
        pos--;
      line.push(pos, lend);
      line.push('\0');
    }
  }

  void operator++(void) { pos++; }
  char operator*(void) { return *pos; }
  
  bool isEof(void) { return pos == end; }
protected:
//  boost::iostreams::mapped_file file;  
  int file;
  char* pos;
  char* start;
  char* end;
};

void print_lits(vec<lit>& ps)
{
  for(lit l : ps)
    printf(" %s%d", l&1 ? "" : "-", l>>1);
}

int main(int argc, char** argv)
{
  // Deal with input arguments

  IDrup idrup;

  MFile file(argv[1]); 
  int init = 0;
  int derived = 0;

  int used_init = 0;
  int used_derived = 0;

  // Scan forward.
  vec<lit> cl;
  LineBuf line;
  file.next_line(line);
  for(; !isEof(line); file.next_line(line))
  {
    // Parse the line
    Parse::skipWhitespace(line);

    if(*line == 'c')
      continue;
    if(*line == 'i')
    {
      // Introduction line
      ++line;
      parseClause(line, cl); 
      idrup.add_clause(cl);
//      printf("i"); print_lits(cl); printf("\n");
      init++;
    } else if(*line == 'd') {
      // Deletion line
      ++line;
      parseClause(line, cl);
      idrup.remove_clause(cl);
      // printf("d"); print_lits(cl); printf("\n");
    } else {
      // Derivation line
      parseClause(line, cl);  
      idrup.add_clause(cl);
      derived++;
      // printf("|-"); print_lits(cl); printf("\n");
    }
  }

  cl.clear();
  bool complete = idrup.check_redundant(cl);
  if(!complete)
  {
    printf("s INCOMPLETE\n");
    return 1;
  }
  
  // Scan backwards.
  file.prev_line(line);
  for(; !line.is_eof(); file.prev_line(line))
  {
    Parse::skipWhitespace(line);
    if(*line == 'c')
      continue; 
    if(*line == 'i')
    {
      // Remove initial clause
      ++line;
      parseClause(line, cl);
      // printf("<- i"); print_lits(cl); printf("\n");
      Clause* ptr = idrup.pop_clause(cl);
      if(idrup.is_used(ptr))
        used_init++;
      idrup.free_clause(ptr);
    } else if(*line == 'd') {
      // Deletion line; clause may be used.
      ++line;
      parseClause(line, cl);
      idrup.add_clause(cl);
      // printf("<- d"); print_lits(cl); printf("\n");
    } else {
      // Derivation line; remove the clause,
      // but check that it's used.
      parseClause(line, cl);
      Clause* ptr = idrup.pop_clause(cl);
      if(!ptr || idrup.is_used(ptr))
      {
        used_derived++;
        if(!idrup.check_redundant(cl))
        {
          printf("c Clause not redundant: [");
          for(lit l : cl)
            printf(" %s%d", l&1 ? "" : "-", l>>1);
          printf(" ]\n");
          printf("s INVALID\n");
          return 1;
        }
      }
      idrup.free_clause(ptr);
      // printf("<- |-"); print_lits(cl); printf("\n");
    }
  }

  printf("c used %d of %d initial clauses, %d of %d derived clauses.\n", used_init, init, used_derived, derived);
  printf("s VERIFIED\n");
  return 0;
}
