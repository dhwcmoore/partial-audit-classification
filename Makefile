# Partial Audit Classification
#
# Verified toolchain: Coq 8.18.0 (coqc, coqchk), OCaml 4.14.1, dune 3.x.

.PHONY: all rocq ocaml check coqchk assumptions admitted-check demo verify clean

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
# Axiom, every module closed under the global context. The module list
# is derived from _CoqProject rather than hardcoded, after that
# hardcoding once let Pipeline.v compile and link for a full commit
# without ever being coqchk-verified (see the commit history): a
# hardcoded second copy of the file list is exactly the kind of drift
# this repository's whole project argues against.
coqchk: rocq
	cd rocq && coqchk -R . PAC $$(grep '\.v$$' _CoqProject | sed -e 's/\.v$$//' -e 's/^/PAC./' | tr '\n' ' ')

# Print Assumptions on every publication-facing theorem
# (PrintAssumptions.v), then fail if any theorem's proof depends on an
# axiom: a theorem with no axiom dependencies prints exactly "Closed
# under the global context"; one with a dependency prints an "Axioms:"
# block instead. This is complementary to coqchk, not redundant with
# it: coqchk verifies compiled .vo files are internally consistent,
# this verifies the *specific theorems this repository publishes*
# don't quietly rest on an admitted lemma or declared Axiom introduced
# elsewhere in the dependency graph.
assumptions: rocq
	cd rocq && coqc -R . PAC PrintAssumptions.v > /tmp/pac-assumptions.log 2>&1; \
	cat /tmp/pac-assumptions.log; \
	if grep -q '^Axioms:' /tmp/pac-assumptions.log; then \
	  echo "assumptions: FAILED -- an axiom dependency was found above"; exit 1; \
	else \
	  echo "assumptions: every listed theorem is closed under the global context"; \
	fi

# A source-level check for the specific proof shortcuts this
# repository's own claims depend on never being used: Admitted proofs,
# the admit tactic, and Axiom declarations. Best-effort text search,
# not a substitute for coqchk/assumptions above, but it catches the
# problem at the point someone introduces it rather than only at
# publication time.
admitted-check:
	@if grep -rnE 'Admitted\.|(^|;)[[:space:]]*admit\.|^[[:space:]]*Axiom[[:space:]]' rocq/*.v; then \
	  echo "admitted-check: FAILED -- Admitted/admit/Axiom found above"; exit 1; \
	else \
	  echo "admitted-check: no Admitted, admit, or Axiom in rocq/*.v"; \
	fi

check: coqchk admitted-check assumptions
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