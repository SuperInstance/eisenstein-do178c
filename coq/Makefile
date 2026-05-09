# Makefile for Eisenstein DO-178C Coq Proofs
# Requires: Coq 8.18+ with ZArith standard library

COQC   := coqc
COQDEP := coqdep
COQFLAGS :=

# Source files in dependency order
VFILES := eisenstein-safety.v \
          int8-soundness.v \
          differential-zero.v \
          galois-xor.v

VOFILES := $(VFILES:.v=.vo)
GLOBFILES := $(VFILES:.v=.glob)
VOKFILES := $(VFILES:.v=.vok)

.PHONY: all clean check proofs

all: proofs

proofs: $(VOFILES)

check: $(VOKFILES)

# Each file is self-contained (definitions replicated for standalone compilation)
# If modular compilation is desired, use _CoqProject with -Q flags
%.vo: %.v
	$(COQC) $(COQFLAGS) $<

%.vok: %.v
	$(COQC) $(COQFLAGS) $<

%.glob: %.v %.vo
	$(COQC) $(COQFLAGS) $<

clean:
	rm -f *.vo *.glob *.vok *.aux *.d

deps:
	$(COQDEP) $(VFILES) > .depend

-include .depend
