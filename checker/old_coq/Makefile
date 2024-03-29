#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile V8.3pl4     ##
#############################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile bounds.v cumulative.v domain.v element.v linear.v prim.v reif.v zset.v checker.ml main.ml model.ml mTypes.ml cOption.ml registry.ml spec.ml 
#

# 
# This Makefile may take 3 arguments passed as environment variables:
#   - COQBIN to specify the directory where Coq binaries resides;
#   - CAMLBIN and CAMLP4BIN to give the path for the OCaml and Camlp4/5 binaries.
COQLIB:=$(shell $(COQBIN)coqtop -where | sed -e 's/\\/\\\\/g')
CAMLP4:="$(shell $(COQBIN)coqtop -config | awk -F = '/CAMLP4=/{print $$2}')"
ifndef CAMLP4BIN
  CAMLP4BIN:=$(CAMLBIN)
endif

CAMLP4LIB:=$(shell $(CAMLP4BIN)$(CAMLP4) -where)

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

OCAMLLIBS:=-I .
COQSRCLIBS:=-I $(COQLIB)/kernel -I $(COQLIB)/lib \
  -I $(COQLIB)/library -I $(COQLIB)/parsing \
  -I $(COQLIB)/pretyping -I $(COQLIB)/interp \
  -I $(COQLIB)/proofs -I $(COQLIB)/tactics \
  -I $(COQLIB)/toplevel \
  -I $(COQLIB)/plugins/cc \
  -I $(COQLIB)/plugins/dp \
  -I $(COQLIB)/plugins/extraction \
  -I $(COQLIB)/plugins/field \
  -I $(COQLIB)/plugins/firstorder \
  -I $(COQLIB)/plugins/fourier \
  -I $(COQLIB)/plugins/funind \
  -I $(COQLIB)/plugins/micromega \
  -I $(COQLIB)/plugins/nsatz \
  -I $(COQLIB)/plugins/omega \
  -I $(COQLIB)/plugins/quote \
  -I $(COQLIB)/plugins/ring \
  -I $(COQLIB)/plugins/romega \
  -I $(COQLIB)/plugins/rtauto \
  -I $(COQLIB)/plugins/setoid_ring \
  -I $(COQLIB)/plugins/subtac \
  -I $(COQLIB)/plugins/subtac/test \
  -I $(COQLIB)/plugins/syntax \
  -I $(COQLIB)/plugins/xml
COQLIBS:=-I . 
COQDOCLIBS:=

##########################
#                        #
# Variables definitions. #
#                        #
##########################

OCAMLFIND = ocamlfind

ZFLAGS=$(OCAMLLIBS) $(COQSRCLIBS) -I $(CAMLP4LIB)
OPT:=
COQFLAGS:=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
ifdef CAMLBIN
  COQMKTOPFLAGS:=-camlbin $(CAMLBIN) -camlp4bin $(CAMLP4BIN)
endif
COQC:=$(COQBIN)coqc
COQDEP:=$(COQBIN)coqdep -c
GALLINA:=$(COQBIN)gallina
COQDOC:=$(COQBIN)coqdoc
COQMKTOP:=$(COQBIN)coqmktop
CAMLLIB:=$(shell $(CAMLBIN)ocamlc.opt -where)
CAMLC:=$(OCAMLFIND) ocamlc -c -rectypes -g
CAMLOPTC:=$(OCAMLFIND) ocamlopt -g -c -rectypes # -ccopt -pg
CAMLLINK:=$(OCAMLFIND) ocamlc -rectypes -g
CAMLOPTLINK:=$(OCAMLFIND) ocamlopt -rectypes -g # -ccopt -pg
GRAMMARS:=grammar.cma
CAMLP4EXTEND:=pa_extend.cmo pa_macro.cmo q_MLast.cmo
CAMLP4OPTIONS:=
PP:=-pp "$(CAMLP4BIN)$(CAMLP4)o -I $(CAMLLIB) -I . $(COQSRCLIBS) $(CAMLP4EXTEND) $(GRAMMARS) $(CAMLP4OPTIONS) -impl"

REQ_PKG:="dynlink extlib"
PKG_FLAGS:=-package $(REQ_PKG)
LINKPKG_FLAGS:=-package $(REQ_PKG) -linkpkg

###################################
#                                 #
# Definition of the "all" target. #
#                                 #
###################################

MODEL_FILES:=$(wildcard models/*.v)

VFILES:=bounds.v\
	arith_ops.v\
  domain.v\
  zset.v\
	map.v\
	domset.v\
  cumulative.v\
	cumul_dset.v\
  element.v\
	element_dset.v\
  linear.v\
	linear_dset.v\
	sol.v\
  prim.v\
  reif.v\
	arith.v\
	model.v\
	resolution.v\
	log.v\
  checker_impl.v
VOFILES:=$(VFILES:.v=.vo)
VOFILES0:=$(filter-out ,$(VOFILES))
GLOBFILES:=$(VFILES:.v=.glob)
VIFILES:=$(VFILES:.v=.vi)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
AUTO_MLFILES:=checker_impl.ml
MLFILES:=#$(AUTO_MLFILES)

MODEL_VOFILES=$(MODEL_FILES:.v=.vo)

CMOFILES:=$(MLFILES:.ml=.cmo)
CMOFILES0:=$(filter-out ,$(CMOFILES))
CMIFILES:=$(MLFILES:.ml=.cmi)
CMIFILES0:=$(filter-out ,$(CMIFILES))
CMXFILES:=$(MLFILES:.ml=.cmx)
CMXSFILES:=$(MLFILES:.ml=.cmxs)
CMXSFILES0:=$(filter-out ,$(CMXSFILES))
OFILES:=$(MLFILES:.ml=.o)

TARGETS:=
all: $(VOFILES) $(CMOFILES) $(CMXSFILES) $(TARGETS)
spec: $(VIFILES)
models: $(MODEL_VOFILES)

gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all.pdf: $(VFILES)
	$(COQDOC) -toc -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.pdf: $(VFILES)
	$(COQDOC) -toc -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`



####################
#                  #
# Special targets. #
#                  #
####################

.PHONY: all opt byte archclean clean install depend html

%.cmi: %.mli
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $(PKG_FLAGS) $<

%.cmo: %.ml
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $(PP) $(PKG_FLAGS) $<

%.cmx: %.ml
	$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $(PP) $(PKG_FLAGS) $<

%.cmxs: %.ml
	$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -shared -o $@ $(PP) $< $(LINKPKG_FLAGS)

%.cmo: %.ml4
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $(PP) -impl $(PKG_FLAGS) $<

%.cmx: %.ml4
	$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $(PP) -impl $(PKG_FLAGS) $<

%.cmxs: %.ml4
	$(CAMLOPTLINK) $(ZDEBUG) $(ZFLAGS) -shared -o $@ $(PP) -impl $< $(LINKPKG_FLAGS)

%.ml.d: %.ml
	$(CAMLBIN)ocamldep -slash $(OCAMLLIBS) $(PP) "$<" > "$@"

%.vo %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

%.vi: %.v
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

%.g: %.v
	$(GALLINA) $<

%.tex: %.v
	$(COQDOC) -latex $< -o $@

%.html: %.v %.glob
	$(COQDOC) -html $< -o $@

%.g.tex: %.v
	$(COQDOC) -latex -g $< -o $@

%.g.html: %.v %.glob
	$(COQDOC) -html -g $< -o $@

%.v.d: %.v
	$(COQDEP) -slash $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

install:
	mkdir -p $(COQLIB)/user-contrib
	(for i in $(VOFILES0); do \
	 install -d `dirname $(COQLIB)/user-contrib/$(INSTALLDEFAULTROOT)/$$i`; \
	 install $$i $(COQLIB)/user-contrib/$(INSTALLDEFAULTROOT)/$$i; \
	 done)
	(for i in $(CMOFILES0); do \
	 install -d `dirname $(COQLIB)/user-contrib/$(INSTALLDEFAULTROOT)/$$i`; \
	 install $$i $(COQLIB)/user-contrib/$(INSTALLDEFAULTROOT)/$$i; \
	 done)
	(for i in $(CMIFILES0); do \
	 install -d `dirname $(COQLIB)/user-contrib/$(INSTALLDEFAULTROOT)/$$i`; \
	 install $$i $(COQLIB)/user-contrib/$(INSTALLDEFAULTROOT)/$$i; \
	 done)
	(for i in $(CMXSFILES0); do \
	 install -d `dirname $(COQLIB)/user-contrib/$(INSTALLDEFAULTROOT)/$$i`; \
	 install $$i $(COQLIB)/user-contrib/$(INSTALLDEFAULTROOT)/$$i; \
	 done)

clean:
	rm -f $(CMOFILES) $(CMIFILES) $(CMXFILES) $(CMXSFILES) $(OFILES) $(VOFILES) $(VIFILES) $(GFILES) $(MLFILES:.ml=.cmo) $(MLFILES:.ml=.cmx) *~
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(HTMLFILES) $(GHTMLFILES) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) $(VFILES:.v=.v.d)
	rm -f $(CMOFILES) $(MLFILES:.ml=.cmi) $(MLFILES:.ml=.ml.d) $(MLFILES:.ml=.cmx) $(MLFILES:.ml=.o)
	rm -f $(AUTO_MLFILES) $(AUTO_MLFILES:.ml=.mli)
	rm -f $(MODEL_FILES:.v=.glob) $(MODEL_FILES:.v=.v.d) $(MODEL_FILES:.v=.vo)
	- rm -rf html

archclean:
	rm -f *.cmx *.o


printenv: 
	@echo CAMLC =	$(CAMLC)
	@echo CAMLOPTC =	$(CAMLOPTC)
	@echo CAMLP4LIB =	$(CAMLP4LIB)

-include $(VFILES:.v=.v.d)
.SECONDARY: $(VFILES:.v=.v.d)

-include $(MLFILES:.ml=.ml.d)
.SECONDARY: $(MLFILES:.ml=.ml.d)

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

