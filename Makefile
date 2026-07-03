COQMAKEFILE := CoqMakefile

all:
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)
	make -f $(COQMAKEFILE)

clean:
	rm -f *.glob *.vo *.vos *.vok *.aux
	rm -f theories/*.glob theories/*.vo theories/*.vos theories/*.vok
	rm -f $(COQMAKEFILE)