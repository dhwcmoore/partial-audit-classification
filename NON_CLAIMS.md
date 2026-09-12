# What this repository does not establish

Read this before reading any proof or CLI output as an assurance. It governs
both accompanying manuscripts, "A Discipline of Partial Audit Classification"
(submitted, STTT) and "Boundary Discipline for Accounting Information
Systems" (submitted, IJDAR).

## v0.2 scope (frozen before implementation)

This section states the target claim for v0.2 before any proof in this
repository was changed to reach it, so that the implementation is built to
a fixed specification rather than the specification being written to match
whatever the implementation ended up proving.

> The kernel computes classifications from declared boundaries, requires a
> distinct admission certificate before a verified classification may
> support an unqualified opinion, automatically records every material
> result that is not both verified and validly admitted, and prevents the
> extracted decision procedure from returning an unqualified opinion when
> any required certificate is absent.

This is stronger than the v0.1 claim below because it concerns a
computational decision procedure (`decide_opinion` / `run_pipeline`), not
only a declarative predicate (`OpinionAdmissible`) defined to contain the
desired property by construction.

v0.2 continues to not claim:

- that supplied evidence is genuine;
- that supplied materiality judgements are correct;
- that different process identifiers guarantee organisational independence;
- that collusion is prevented;
- that the classifier performs an audit;
- that the Wirecard fixture reconstructs EY's working papers;
- that OCaml extraction and compilation are inside the Rocq trusted proof
  boundary.

The rest of this document describes what v0.1 already established (still
true) and, as later sections are added, what v0.2 adds on top of it.

## What is proved

`rocq/Admissibility.v`, `rocq/Residual.v`, and `rocq/SelfAdmission.v` prove
three theorems, generally, over abstract `Fact`, `Assertion`, and `Process`
types:

- **Default-Free Admissibility** (`default_free_admissibility`,
  `contrapositive_inadmissible`): an opinion is admissible as unqualified
  only if every material dependency is an admitted `Verified` classification.
  This holds for *any* boundary specification and evidence context you
  supply to `boundary_state`, not only for the three worked cases.
- **Residual Preservation** (`residual_preservation`,
  `residual_preservation_chain`): the residual register only grows.
- **No Self-Admission** (`no_self_admission`, `role_separation`): a process
  in the Proposer role cannot simultaneously occupy the Verifier role for
  the same assertion.

`rocq/Cases.v` then exercises these on three finite instances matching the
papers' own examples (Wirecard, a ten-transaction continuous-auditing queue,
and a SQL-Unknown rendering collapse). `coqchk` confirms every module is
closed under the global context with no `Admitted` and no `Axiom`.

## What is not proved, and what running the CLI does not show

- **This is a classification kernel, not an audit.** The theorems say
  nothing about whether a bank confirmation is genuine, a transaction is
  fraudulent, or a risk model is well-calibrated. `material`,
  `independently_admitted`, and the contents of any `BoundarySpec` are
  supplied by the caller; the kernel enforces the *composition* rule over
  whatever those supplied predicates say, and no more.
- **The three worked cases are illustrative traces, not empirical
  findings.** `Cases.v`'s Wirecard module encodes the narrative in the
  papers' Section 6/7 as a boundary specification with five preconditions;
  it is not a reconstruction of Ernst & Young's actual working papers, and
  the CLI's "counterfactual with full evidence" is a demonstration that the
  boundary specification is not vacuous, not a claim about what would have
  happened.
- **Only the mechanical Verified/Undefined branch is modelled.** Boundary
  evaluation in this development produces exactly those two outcomes.
  `Refuted`, `PresumptivelyVerified`, `PresumptivelyRefuted`, and
  `EscalationRequired` are declared in `Base.v` and used in the residual
  register and the case studies, but no generic, provably-correct procedure
  for *assigning* them is formalised here; the papers describe them
  qualitatively (Section 3) and this repository does not yet close that
  gap.
- **No revocation.** The boundary machinery is monotone in the evidence
  context (`has_fact_monotone`): nothing in this development retracts a
  fact or downgrades a `Verified` classification once evidence is added.
  Real audits sometimes need to un-verify something; that is out of scope
  for v0.1, exactly as `RegisterLog`'s append-only `step` relation does not
  model deletion.
- **`independently_admitted` and `proposes`/`admits` are abstract.** This
  repository proves that a Proposer cannot also be a Verifier by
  construction of the `Role` type. It does not model *how* an organisation
  assigns roles, staffs an independent review function, or prevents
  collusion between two distinct processes that are each honestly
  single-role.
- **Extraction is trusted, not verified.** As with any Coq development that
  extracts to OCaml, the extraction mechanism itself, the OCaml compiler,
  and this repository's hand-written CLI wiring around the extracted kernel
  are not machine-checked. `tools/fixture_check.py` is a regression test
  against the CLI's current output, i.e. observed agreement between the
  extracted executable and the case-study Examples in `Cases.v` — that is
  testing, not proof.
- **No claim about real-world adoption, cost, or legal effect.** Section 8
  of the AIS paper and Section 8 (Implications) of the STTT paper discuss
  what a standard or inspection protocol *could* require; nothing in this
  repository constitutes such a standard, and no auditing body has adopted
  any part of it.

## Relationship to the "machine-checked sketch" remark

The STTT manuscript's Remark on "machine-checked sketch" (end of Section 9)
says the admissibility, residual-preservation, and no-self-admission
theorems "are proved for the finite instances exercised there." This
repository in fact proves them generally (quantified over abstract types),
with the finite instances in `Cases.v` as worked examples rather than the
full extent of what is proved. If you are citing this repository from either
manuscript, cite the general theorems in `Admissibility.v`, `Residual.v`,
and `SelfAdmission.v`, and treat `Cases.v` as illustration.
