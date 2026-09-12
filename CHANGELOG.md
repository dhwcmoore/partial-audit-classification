# Changelog

This project does not yet have a tagged release. The entries below group
the commit history into the two development phases so far; dates are the
dates of the commits themselves, not of any publication event. See
`NON_CLAIMS.md` for what each phase does and does not establish, and the
git history for the full, unabridged record.

## [Unreleased] — v0.2 development (2026-09-12)

v0.2 replaces the v0.1 declarative-only kernel with an executable
pipeline: a caller-supplied boundary specification and evidence context
are classified, a classification proposal is checked against a
certificate-based admission mechanism over a registered-process
population, non-admitted material dependencies automatically emit
residual entries, and an opinion-decision function is proved sound end
to end. `docs/` was added, carrying both accompanying manuscripts and
their compiled PDFs.

### Added
- `rocq/Pipeline.v`: the orchestration module (`build_packet`,
  `dep_ok`, `classify_and_register`, `run_pipeline`) and its soundness
  theorem, `pipeline_unqualified_sound`.
- `SelfAdmission.v`: `ProcessRegistry`, `ClassificationProposal`,
  `AdmissionCertificate`, and `validate_admission` — a six-conjunct
  computational admission check (proposal ID match; registered
  `Verifier`-role admitter; registered `Proposer`-role proposer;
  distinct admitter/proposer identity; affirmative decision; `Verified`
  proposal classification) — replacing the v0.1 model that proved only
  that `Proposer` and `Verifier` are distinct constructors. Six
  corresponding rejection theorems, one per conjunct.
- `Boundary.v`: `EqbSpec`, a correctness-carrying equality record
  replacing a trusted bare `Fact -> Fact -> bool`; versioned,
  identified `Procedure`/`BoundarySpec` records; witness theorems
  (`procedure_satisfied_sound`/`complete`,
  `boundary_verified_has_witness`/`boundary_undefined_no_witness`) and
  context-monotonicity theorems generalising v0.1's `has_fact_monotone`.
- `Residual.v`: automatic residual emission gated on materiality
  (`process_dependency`, `nonmaterial_emits_no_residual`), and
  `classify_and_register_emits_for_dependency`, proved by induction to
  establish genuine log membership rather than only that logs grow.
- `rocq/PrintAssumptions.v`: all 49 named `Theorem`/`Corollary`/`Lemma`
  declarations in the formal core, individually checked closed under
  the global context; wired into CI alongside a source-level check
  against `Admitted`, `admit`, `Axiom`, and unexpected `Parameter`.
- Six Wirecard fixtures in `Cases.v` (incomplete evidence; complete
  evidence without admission; complete evidence with a valid verifier
  certificate; proposer self-certification, rejected; unregistered
  proposer, rejected; registered non-`Proposer` proposer, rejected),
  replacing the single undefined/verified pair from v0.1.
- Both manuscripts: a "Note on a related submission" disclosing the
  companion manuscript, a rewritten Formal Development / Formal
  Statement section describing the executable pipeline in place of the
  v0.1 "machine-checked sketch" framing, and a corrected admissibility
  discussion naming all six certificate conditions.

### Changed
- `boundary_state` renamed `classify`, with the boundary specification
  as its first argument.
- `affirmative` renamed `supports_unqualified`.
- `pipeline_residual_implies_not_unqualified_witness` renamed
  `pipeline_failed_material_dependency_blocks_unqualified` to match
  what it actually proves (no residual-membership claim in its
  original form).
- `ocaml/cli/main.ml` rebuilt as a thin presentation layer over the
  extracted `run_pipeline`; it no longer infers opinion admissibility
  from `Verified` alone.

### Fixed
- A binding gap in the initial `Pipeline.v`: `build_packet` computed
  `dep_state` from the real classified assertion but accepted an
  unrelated, caller-supplied `ClassificationProposal` for
  `dep_proposal`, so a certificate for a `Verified` proposal about a
  *different* assertion could validate a packet for the one actually
  being decided. `build_packet` now constructs the proposal from the
  same assertion and computed state it classifies, structurally, with
  `build_packet_proposal_matches` as the corresponding lemma.
- `validate_admission` did not check the proposer's registration or
  role, only the verifier's; a proposal could name a fictitious or
  wrongly-roled proposer and still validate. Added the corresponding
  conjunct and `non_proposer_certificate_rejected`.
- Several stale cross-references caught across three external review
  passes: manuscript section numbers that no longer matched either
  paper's actual structure after edits: a false "mirrors the paper's
  ratio" comment in the continuous-auditing fixture; commit-hash
  citations that went stale the moment they were committed (now
  citing the repository URL without a pinned commit instead); an
  internally inconsistent submission-status claim across both
  manuscripts, `README.md`, and `NON_CLAIMS.md`.

## v0.1 (2026-09-11)

The initial formal development: the six-state `EvidenceState`
vocabulary, mechanical `Verified`/`Undefined` boundary classification
from a declared specification and evidence context, the
`OpinionAdmissible` declarative admissibility predicate and its
`default_free_admissibility`/`contrapositive_inadmissible` theorems, an
append-only residual register with `residual_preservation`, and a
`Proposer`/`Verifier` role-separation theorem, `no_self_admission`. All
three theorems proved generally, over abstract types, not only for the
Wirecard/continuous-auditing/SQL-Unknown worked instances in `Cases.v`.
Extracted to an OCaml CLI running those three cases.
