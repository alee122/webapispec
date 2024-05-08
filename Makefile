KNOWNTARGETS := CoqMakefile

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

clean:
	rm *.vo *.vos *.glob *.vok
