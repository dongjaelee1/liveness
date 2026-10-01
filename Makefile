# Forward most targets to Rocq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all
.PHONY: all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	find lantana lantana_heap_lang \( -name "*.d" -o -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.coq Makefile.coq.conf .lia.cache
.PHONY: clean

# Create Rocq Makefile.
Makefile.coq: _CoqProject Makefile
	"$(COQBIN)rocq" makefile -f _CoqProject -o Makefile.coq

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;

# Phony wildcard targets
phony: ;
.PHONY: phony
