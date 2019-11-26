default: all

all: Makefile.coq
	$(info Coq: Compiling source files using coqc ...)
	@+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	$(info Coq: Cleaning up ...)
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(info Coq: Invoking coq_makefile ...)
	@$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject Makefile: ;

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: default all clean
