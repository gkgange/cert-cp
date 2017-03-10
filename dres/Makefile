CXX = clang++
CXXFLAGS = -O3 -g -I .
#CXXFLAGS = -O2 -g -I .
#CXXFLAGS = -O0 -g -I .
#CXXFLAGS += -pg
CXXFLAGS += -Wall -Wno-unused-function -Wno-deprecated -ffast-math -std=c++11
LFLAGS = -lz

#SRCS = $(wildcard core/*.cpp)
SRCS = 
OBJS = $(addsuffix .o, $(basename $(SRCS)))
DEPS = $(addsuffix .d, $(basename $(SRCS)))


TARGETS = idrup-trim idres-check
TARGETOBJS = $(addsuffix .o, $(TARGETS))
TARGETDEPS = $(addsuffix .d, $(TARGETS))

all : $(TARGETS)

#$(TARGETS) : % : %.o $(OBJS)
#	$(CXX) $(CXXFLAGS) -o $@ $@.o $(OBJS) $(LFLAGS)

CLEAN_OBJS = $(OBJS) idrup-trim.o idrup-state.o idres-check.o idres-state.o

idrup-trim : idrup-trim.o idrup-state.o $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $@.o idrup-state.o $(OBJS) $(LFLAGS)

idres-check : idres-check.o idres-state.o $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $@.o idres-state.o $(OBJS) $(LFLAGS)
clean :
	rm -f $(TARGETS) $(TARGETOBJS) $(CLEAN_OBJS)

-include $(DEPS)
-include $(TARGETDEPS)

%.d: %.c
	@$(CXX) -MM -MT  $(subst .d,.o,$@) -MT $@ $(CXXFLAGS) $< > $@
