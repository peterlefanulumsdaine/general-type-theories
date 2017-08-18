# Based on example given by Adam Chlipala, in “Theorem Proving in the Large”,
# section “Build Patterns”. http://adam.chlipala.net/cpdt/html/Large.html

# Usage examples:
#     make
#     make all
#     make html
#     make all TIMED=yes
#     make clean

# Modules to be included in the main build:
MODULES := \
	Family \
	Coproduct \
	DeductiveClosure \
	RawSyntax \
	StandardRawRules \
	ShapeSystems \
	ShapeSystemExamples \
	WellFoundedRelations \

VS      := $(MODULES:%=%.v)

# The HoTT coq binaries (“hoqc” etc.) are used by default.  These can
# be overridden by explicitly passing a different value of COQC, e.g.
#     make COQC=coqc
# COQDEP and COQDOC are set automatically based on COQC, but we are not
# very clever about this, so if it doesn’t work, these can be explicitly
# specified too.
#
# NOTE: currently, the “timed” options are hardwired to use “hoqc” etc.

COQC ?= hoqc

ifeq ($(COQC),hoqc)
	COQDEP ?= hoqdep
else
	COQDEP ?= coqdep
endif

COQDOC ?= coqdoc

export COQC COQDEP COQDOC

.PHONY: coq all install clean html

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R . "" $(VS) -o Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile*.coq
	rm -f html

html: all
	mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -utf8 -html $(COQDOCLIBS) -d html $(VS)
