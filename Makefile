# Based on example given by Adam Chlipala, in “Theorem Proving in the Large”,
# section “Build Patterns”. http://adam.chlipala.net/cpdt/html/Large.html

# Usage examples:
#     make
#     make all
#     make html
#     make clean

# Modules to be included in the main build:
MODULES := \
	Auxiliary/General \
	Auxiliary/WellFounded \
	Auxiliary/Family \
	Auxiliary/Coproduct \
	Auxiliary/Closure \
	Syntax/ScopeSystem \
	Syntax/SyntacticClass \
	Syntax/Arity \
	Syntax/Signature \
	Syntax/Expression \
	Syntax/Substitution \
	Syntax/Metavariable \
	Syntax/All \
	Typing/Context \
	Typing/Judgement \
	Typing/Presuppositions \
	Typing/RawRule \
	Typing/StructuralRule \
	Typing/RawTypeTheory \
	Typing/StructuralRulePresuppositions \
	Typing/All \
	Presented/ContextVariants \
	Presented/AlgebraicExtension \
	Presented/PresentedRawRule \
	Presented/CongruenceRule \
	Presented/PresentedRawTypeTheory \
	Presented/TypedRule \
	Presented/TypeTheory \
	Metatheorem/Presuppositions \
	Metatheorem/Elimination \
	Metatheorem/UniqueTyping \
	Metatheorem/Acceptability \
	Example/ScopeSystemExamples \
	Example/MartinLofTypeTheory

VS      := $(MODULES:%=%.v)

# For older versions of the HoTT library, use the dedicate “hoqc”:
#     make COQC=hoqc


COQC ?= coqc

ifeq ($(COQC),hoqc)
	COQDEP ?= hoqdep
else
	COQDEP ?= coqdep
endif

COQDOC ?= coqdoc

export COQC COQDEP COQDOC

# coq_makefile hack:
# Some versions of coq_makefile (in coq trunk) don’t play nicely with
# the HoTT binaries; but the HoTT library doesn’t (yet) provide an installed
# hook to its own coq_makefile binary.  So we allow the user to pass this in
# by an explicit environment variable $HOQBIN or $COQBIN.  The latter takes
# precedence if both are specified.
# To avoid passing this by hand every time, add
#     export HOQBIN=~/Path/To/HoTT/coq-HoTT/bin/
# to your shell profile file.

HOQBIN ?=

COQBIN ?= $(HOQBIN)

COQMAKEFILE = $(COQBIN)coq_makefile

# TODO: clean up treatment of binaries/environment variables

.PHONY: coq all install clean html

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQMAKEFILE) -f _CoqProject COQC = "$(COQC)" COQDEP = "$(COQDEP)" $(VS) -o Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile*.coq
	rm -f html

cleaner:
	rm -f **/*.glob **/*.vo **/*.v.d **/*~ **/.*.aux

html:: Makefile.coq
	$(MAKE) -f Makefile.coq html
