SRCDIR = $(shell pwd)
OCAMLC = ocamlc
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
#
# Installation directory
#
PKG-NAME = fzn2cmod

MLMODULES=\
   dynArray \
	 opts \
   util dom token problem \
   lexer parser

OCAMLINC=-I .

OCAMLFLAGS+=$(OCAMLINC)
OCAMLOPTFLAGS+=$(OCAMLINC)

PROF = -ccopt "-pg"
#PROF =

#---------------------------------------
# Rules
#---------------------------------------

# Global rules
TARGETS=fzn2cmod

all: opt

opt: $(TARGETS)

$(TARGETS) : % : $(MLMODULES:%=%.cmx) %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(PROF) $@.mli $^

clobber: clean
	/bin/rm -f Makefile.depend TAGS
	/bin/rm -f $(TARGETS) $(TARGETS_BYTE) $(TARGETS_PROF) $(TARGETS_DEBUG)

clean:
	/bin/rm -f *.cm[ioxat] *.cmti *.o *.cmxa *.annot *.html *.ps *.pdf *.dvi *.out
	/bin/rm -f lexer.ml
	/bin/rm -f *.aux *.bbl *.blg *.dvi *.pdf *.log *.toc *.idx *.ilg *.ind ocamldoc*.tex ocamldoc.sty

wc: $(SRC)
	wc $^

#--------------------------------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#--------------------------------------------------------------

.SUFFIXES: .ml .mli .cmi .cmo .cmx

#-----------------------------------
# CAML
#-----------------------------------

%.ml: %.mll
	$(OCAMLLEX) $^

%.ml %.mli: %.mly
	$(OCAMLYACC) $^

%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

%.p.cmx: %.ml
	$(OCAMLOPT) -p $(OCAMLOPTFLAGS) -c -o $@ $<

.PHONY: tags TAGS
tags: TAGS
TAGS: $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml)
#	ocamltags $^
	otags $^

.PHONY: depend cpp
depend:
	$(OCAMLDEP) $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml) >Makefile.depend

Makefile.depend:
	$(OCAMLDEP) $(MLMODULES:%=%.mli) $(MLMODULES:%=%.ml) >Makefile.depend

-include Makefile.depend
