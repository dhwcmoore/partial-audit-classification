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
  `AdmissionCertificate` is accepted only if it names the correct proposal
  by identifier, the admitting process is registered with `Verifier`
  authority, the proposing process is *also* registered, with `Proposer`
  authority, that process's identity differs from the admitting process's,
  the decision is affirmative, and the proposal itself claims `Verified` —
  six conjuncts, each with its own rejection theorem:
  `certificate_for_wrong_proposal_rejected`, `non_verifier_certificate_rejected`,
  `non_proposer_certificate_rejected`, `proposer_certificate_rejected`,
  `decision_false_certificate_rejected`, and
  `unverified_proposal_certificate_rejected`. The proposer-registration
  conjunct and its rejection theorem, and the two decision/classification
  rejection theorems, were added after an external review of an earlier
  version of this development found that the proposing process's identity
  was accepted unchecked against the registry (see the commit history
  around `591d28e`); that same review found that `Pipeline.v` accepted an
  arbitrary, caller-supplied `ClassificationProposal` per assertion with
  nothing checked against the assertion actually being classified —
  `build_packet_proposal_matches` (`Pipeline.v`) is the fix, and is
  described below.
- **Residual emission** (`Residual.v`, `process_dependency` /
  `classify_and_register`): a dependency that is material and not both
  `Verified` and validly admitted (`dep_ok`) automatically produces a
  residual entry (`nonadmitted_material_emits_residual`); a non-material
  one does not, regardless of `dep_ok` (`nonmaterial_emits_no_residual` —
  an earlier version emitted for every failing dependency regardless of
  materiality, broader than this document's own "every material
  dependency" wording, and was tightened to match it); one that is
  `dep_ok` produces none (`admitted_verified_emits_no_open_residual`).
  `residual_preservation` / `residual_preservation_chain` (unchanged from
  v0.1) say the append-only register never loses an entry;
  `classify_and_register_step` says one pipeline run's own emissions only
  extend the log it started from; `classify_and_register_emits_for_dependency`
  proves, by induction over the dependency list, that a specific failing
  dependency's entry is actually present in the resulting log, not merely
  that emission and the opinion decision cannot disagree in principle;
  `orphan_escalation_sound` says an ownerless entry is exactly what the
  orphan query returns.
- **Opinion decision** (`Admissibility.v`, `decide_opinion`): returns
  `Unqualified` only when every material dependency is `dep_ok`
  (`decide_opinion_unqualified_sound`), with eight corollaries covering
  every way a dependency can block it (`undefined_blocks_unqualified`
  through `invalid_admission_blocks_unqualified`) and a completeness
  theorem (`all_valid_dependencies_allow_unqualified`) showing the check
  is not vacuously impossible to pass.
- **The composed pipeline** (`Pipeline.v`, `run_pipeline`): a
  `PipelineInput` supplies a boundary spec, context, assertions, registry,
  a certificate function, and — as of the fix described above — a
  *proposal identity and proposer* per assertion (`pi_proposal_id`,
  `pi_proposer`), not a complete proposal. `build_packet` constructs the
  `ClassificationProposal` itself, from the real assertion and the real,
  freshly computed classification; `build_packet_proposal_matches` proves
  the two always agree, for every `PipelineInput`, so a proposal for one
  assertion or claiming one classification can no longer be attached to a
  dependency packet for a different assertion or classification.
  `pipeline_unqualified_sound` is the end-to-end theorem — the pipeline
  cannot decide `Unqualified` unless every material assertion is
  classified `Verified` *and* carries a validly admitted certificate. It
  is a corollary of `decide_opinion_unqualified_sound` over the packets
  `run_pipeline` itself builds, not a separate proof, which is the point:
  composition of already-proved stages, not new trust.
  `pipeline_failed_material_dependency_blocks_unqualified` and
  `pipeline_failed_material_dependency_emits_residual` (renamed from a
  single, inaccurately-named theorem after the same review — its
  hypothesis was `dep_ok = false` and it never mentioned residuals at
  all, despite a name suggesting it did) state, respectively, that a
  failing material dependency blocks `Unqualified` and that its entry is
  demonstrably present in the output log.

  **Not established by any of the above:** uniqueness of the
  caller-supplied `ProcessId` and `ProposalId` values. Two proposals
  sharing a `ProposalId` make a certificate drawn up for one also
  validate against the other, since the check compares identifiers, not
  proposal contents; two registry entries sharing a `ProcessId` make
  `process_lookup` return whichever is found first, so role and identity
  checks depend on declaration order rather than a well-defined
  population. This is a caller responsibility this development assumes
  rather than enforces, in the same sense the boundary specification and
  materiality predicate are caller-supplied without a well-formedness
  check; it is not detected or rejected by any theorem above.

**v0.1's declarative layer** remains, unchanged and still true, as a
specification rather than the central result: `OpinionAdmissible` /
`default_free_admissibility` / `contrapositive_inadmissible`
(`Admissibility.v`) and `no_self_admission` / `role_separation`
(`SelfAdmission.v`) state the same properties over a `Prop`-valued
predicate defined to contain them by construction, rather than over an
executable decision procedure.

`rocq/Cases.v` exercises the full v0.2 pipeline on three finite instances
matching the papers' own examples: Wirecard as six fixtures (incomplete
evidence; complete evidence without a certificate; complete evidence with
valid admission; complete evidence with proposer self-certification;
complete evidence with an unregistered proposer; complete evidence with a
proposer registered under the wrong role — the last two added as
adversarial regression tests after the external review described above,
isolated from each other with a second registered verifier so each tests
one failure mode), a ten-transaction continuous-auditing queue run through
the same pipeline, and a SQL-Unknown adapter connected to `classify`
rather than left as a standalone toy.

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
  exercised across six fixtures (four narrative, two adversarial); it is
  not a reconstruction of Ernst & Young's actual working papers, and the
  fixture using complete evidence is a demonstration that the boundary
  specification is not vacuous, not a claim about what would have
  happened.
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
- **Identifier uniqueness is a caller responsibility, not enforced.** The
  kernel does not establish uniqueness of `ProcessId` or `ProposalId`
  values. Claims that a certificate identifies one exact proposal, and
  that registry lookup identifies one exact process, are conditional on
  the caller supplying unique identifiers. Reusing a `ProposalId` across
  two distinct proposals lets a certificate drawn up for one validate
  against the other as well, since `validate_admission` compares
  identifiers, not proposal contents; reusing a `ProcessId` across two
  distinct registry entries makes `process_lookup` (and the role/identity
  checks built on it) depend on which entry is declared first rather than
  on a well-defined population. Neither is detected or rejected.
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
