# Partial Audit Classification
#
# Verified toolchain: Coq 8.18.0 (coqc, coqchk), OCaml 4.14.1, dune 3.x.

.PHONY: all rocq ocaml check coqchk demo verify clean

all: rocq ocaml

# The formal development, including extraction to rocq/audit_kernel.ml.
# rocq/Makefile is a generated build artifact (see .gitignore) and is not
# tracked in git, so it is (re)generated here before every build.
rocq:
	cd rocq && coq_makefile -f _CoqProject -o Makefile
	$(MAKE) -C rocq

# The OCaml CLI. Copies the freshly extracted kernel into ocaml/ so the
# dune build always reflects the current Coq proofs, then builds it.
ocaml: rocq
	cp rocq/audit_kernel.ml rocq/audit_kernel.mli ocaml/
	dune build

# Independent re-verification of every .vo with coqchk: no Admitted, no
# Axiom, every module closed under the global context.
coqchk: rocq
	cd rocq && coqchk -R . PAC PAC.Base PAC.Boundary PAC.Admissibility PAC.Residual PAC.SelfAdmission PAC.Cases PAC.Extraction

check: coqchk
	python3 tools/fixture_check.py

demo: ocaml
	dune exec ocaml/cli/main.exe

# Every required gate, in order. This is the command that decides
# whether the repository is in a shippable state.
verify: all check
	@echo
	@echo "ALL GATES PASSED"

clean:
	-$(MAKE) -C rocq clean
	rm -rf _build ocaml/audit_kernel.ml ocaml/audit_kernel.mli rocq/Makefile rocq/Makefile.conf rocq/.Makefile.d
