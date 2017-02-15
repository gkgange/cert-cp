#CXX = clang++
CXX = g++
#CXXFLAGS = -O2 -g -I .
#CXXFLAGS = -O0 -g -I .
CXX_OPTFLAGS = -O3 -g -I .
CXX_DEBUGFLAGS = -O0 -g -I .
CXXFLAGS = -Wall -Wno-unused-function -Wno-deprecated -ffast-math -std=c++11
LFLAGS = -lz

CXXFLAGS += -DVAR_WATCH

SRCS = fdres-state.cpp log-parser.cpp
OBJS = $(addsuffix .o, $(basename $(SRCS)))
DEBUG_OBJS = $(addsuffix .debug.o, $(basename $(SRCS)))
DEPS = $(addsuffix .d, $(basename $(SRCS)))


TARGETS = fdres-check fdres-simp
TARGETOBJS = $(addsuffix .o, $(TARGETS))
DEBUG_TARGETOBJS = $(addsuffix .debug.o, $(TARGETS))
TARGETDEPS = $(addsuffix .d, $(TARGETS))

DEBUG_TARGETS = $(addsuffix .debug, $(TARGETS))

all : opt debug
opt : $(TARGETS)
debug : $(DEBUG_TARGETS)

ALL_OBJS = $(OBJS) $(TARGETOBJS)
ALL_DEBUG = $(DEBUG_OBJS) $(DEBUG_TARGETOBJS)

## Debug objects
#$(ALL_OBJS) $(ALL_DEBUG) : % : $(DEPS)

$(ALL_OBJS) : %.o : %.cpp
	$(CXX) $(CXXFLAGS) $(CXX_OPTFLAGS) -c -o $@ $<

$(ALL_DEBUG) : %.debug.o : %.cpp
	$(CXX) $(CXXFLAGS) $(CXX_DEBUGFLAGS) -c -o $@ $<

$(TARGETS) : % : %.o $(OBJS)
	@echo Target rule: $@
	$(CXX) $(CXXFLAGS) $(CXX_OPTFLAGS) -o $@ $@.o $(OBJS) $(LFLAGS)

$(DEBUG_TARGETS) : %.debug : %.debug.o $(DEBUG_OBJS)
	@echo Target rule: $@
	$(CXX) $(CXXFLAGS) $(CXX_DEBUGFLAGS) -o $@ $@.o $(DEBUG_OBJS) $(LFLAGS)

clean :
	rm -f $(TARGETS) $(DEBUG_TARGETS) $(ALL_OBJS) $(ALL_DEBUG) 

-include $(DEPS)
-include $(TARGETDEPS)

%.d : %.cpp
	@$(CXX) -MM -MT  $(subst .d,.o,$@) -MT $@ $(CXXFLAGS) $< > $@
