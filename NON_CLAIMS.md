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

Every theorem below is generic (quantified over abstract `Fact`,
`Assertion`, and `Process` types, or over the finite fact/assertion types
each fixture declares), holds for *any* boundary specification, evidence
context, process registry, and dependency set you supply, and is
`coqchk`-clean: no `Admitted`, no `Axiom`, closed under the global context.

**v0.2's operative layer** is a chain of computational (`Type`/`bool`-valued,
extracted) functions, each proved sound, composed into one pipeline:

- **Boundary classification** (`Boundary.v`, `classify`): computed from a
  declared, identified, versioned `BoundarySpec` and an `EqbSpec`-witnessed
  evidence context. `boundary_verified_has_witness` /
  `boundary_undefined_no_witness` say a `Verified` outcome has a concrete
  procedure witness, not merely that a Boolean computation returned `true`;
  `boundary_verified_context_monotone` says adding evidence never loses one.
- **Admission validation** (`SelfAdmission.v`, `validate_admission`): an
  `AdmissionCertificate` is accepted only if it names the correct proposal,
  the admitting process is registered with `Verifier` authority, that
  process's identity differs from the proposer's, the decision is
  affirmative, and the proposal itself claims `Verified`.
  `proposer_certificate_rejected`, `certificate_for_wrong_proposal_rejected`,
  and `non_verifier_certificate_rejected` cover each way a certificate can
  fail.
- **Residual emission** (`Residual.v`, `process_dependency` /
  `classify_and_register`): a dependency that is not both `Verified` and
  validly admitted (`dep_ok`) automatically produces a residual entry
  (`nonadmitted_material_emits_residual`); one that is produces none
  (`admitted_verified_emits_no_open_residual`). `residual_preservation` /
  `residual_preservation_chain` (unchanged from v0.1) say the append-only
  register never loses an entry; `orphan_escalation_sound` says an
  ownerless entry is exactly what the orphan query returns.
- **Opinion decision** (`Admissibility.v`, `decide_opinion`): returns
  `Unqualified` only when every material dependency is `dep_ok`
  (`decide_opinion_unqualified_sound`), with eight corollaries covering
  every way a dependency can block it (`undefined_blocks_unqualified`
  through `invalid_admission_blocks_unqualified`) and a completeness
  theorem (`all_valid_dependencies_allow_unqualified`) showing the check
  is not vacuously impossible to pass.
- **The composed pipeline** (`Pipeline.v`, `run_pipeline`):
  `pipeline_unqualified_sound` is the end-to-end theorem — given one
  `PipelineInput` (boundary, context, assertions, registry, proposals,
  certificates), the pipeline cannot decide `Unqualified` unless every
  material assertion is classified `Verified` *and* carries a validly
  admitted certificate. It is a corollary of `decide_opinion_unqualified_sound`
  over the packets `run_pipeline` itself builds, not a separate proof, which
  is the point: composition of already-proved stages, not new trust.

**v0.1's declarative layer** remains, unchanged and still true, as a
specification rather than the central result: `OpinionAdmissible` /
`default_free_admissibility` / `contrapositive_inadmissible`
(`Admissibility.v`) and `no_self_admission` / `role_separation`
(`SelfAdmission.v`) state the same properties over a `Prop`-valued
predicate defined to contain them by construction, rather than over an
executable decision procedure.

`rocq/Cases.v` exercises the full v0.2 pipeline on three finite instances
matching the papers' own examples: Wirecard as four fixtures (incomplete
evidence; complete evidence without a certificate; complete evidence with
valid admission; complete evidence with proposer self-certification), a
ten-transaction continuous-auditing queue run through the same pipeline,
and a SQL-Unknown adapter connected to `classify` rather than left as a
standalone toy.

## What is not proved, and what running the CLI does not show

- **This is a classification kernel, not an audit.** The theorems say
  nothing about whether a bank confirmation is genuine, a transaction is
  fraudulent, or a risk model is well-calibrated. `material`,
  `independently_admitted`, and the contents of any `BoundarySpec` are
  supplied by the caller; the kernel enforces the *composition* rule over
  whatever those supplied predicates say, and no more.
- **The three worked cases are illustrative traces, not empirical
  findings.** `Cases.v`'s Wirecard module encodes the narrative in the
  papers' Section 7 as a boundary specification with five preconditions
  exercised across four fixtures; it is not a reconstruction of Ernst &
  Young's actual working papers, and the fixture using complete evidence
  is a demonstration that the boundary specification is not vacuous, not a
  claim about what would have happened.
- **Only the mechanical Verified/Undefined branch is modelled.** Boundary
  evaluation (`classify`) produces exactly those two outcomes, and every
  downstream v0.2 function — `dep_ok`, `decide_opinion`, `process_dependency`,
  `run_pipeline` — inherits that limitation: they can react to `Refuted`,
  the two presumptive states, or `EscalationRequired` if a caller supplies
  a `DependencyPacket` already classified that way (and `dep_ok`/the
  blocking theorems are stated generally enough to cover that case: see
  `refuted_blocks_unqualified`, `presumptive_blocks_unqualified`,
  `escalation_blocks_unqualified`), but no generic, provably-correct
  procedure for *assigning* one of those four states from a boundary
  specification and evidence context is formalised here. The papers
  describe them qualitatively (Section 2/3) and this repository does not
  yet close that gap. This was true in v0.1 and remains true in v0.2 by
  the scope decision recorded above, not by oversight.
- **No revocation, and no residual resolution or closure.** The boundary
  machinery is monotone in the evidence context
  (`boundary_verified_context_monotone`): nothing in this development
  retracts a fact or downgrades a `Verified` classification once evidence
  is added. Real audits sometimes need to un-verify something; that is
  out of scope, exactly as `RegisterLog`'s append-only `step` relation
  does not model deletion. v0.2 adds automatic residual *emission*
  (`process_dependency`, `classify_and_register` in `Residual.v`) but
  deliberately does not add a resolution or closure mechanism: there is
  no `ResidualEvent` state machine, no resolution certificate, and no
  "current open view" distinct from the full history. A dashboard
  clearing is representable only as a `step` that appends new entries;
  it cannot remove existing ones, but nothing in this development marks
  an existing entry as closed either. This is a stated v0.2 scope
  decision (see NON_CLAIMS.md's v0.2 scope note above), not a gap
  discovered after the fact.
- **"Independent" means registered identity and role, not organisational
  independence.** `validate_admission` checks a distinct, registered
  process identity holding `Verifier` authority in the supplied
  `ProcessRegistry` — this is real and checked, not merely a `Role` type
  with two constructors as in v0.1. It does not model *how* an
  organisation assigns roles, staffs an independent review function, or
  prevents collusion between two distinct processes, each honestly
  single-role, that are controlled by the same person or organisation.
  `no_self_admission` / `role_separation` remain as the underlying
  structural fact (`proc_role`); they were always about role separation,
  not about organisational independence, and v0.2 does not change that.
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
