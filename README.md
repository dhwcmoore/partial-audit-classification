# Partial Audit Classification

> No audit conclusion may depend on a material assertion whose verification
> state is undefined.

**Status:** pre-v0.2.0 (untagged). An executable pipeline — boundary
classification, certificate-based admission, automatic residual emission,
and an opinion decision procedure — is built and proved sound end to end
(`pipeline_unqualified_sound`), extracted to OCaml, and exercised on six
Wirecard fixtures (including two adversarial ones added after an external
review found a proposal-binding gap; see the commit history around
`591d28e`), a ten-transaction continuous-auditing run, and a SQL Unknown
adapter. Coq 8.18.0, `coqchk` clean, no `Admitted`, no `Axiom`, all 49
named `Theorem`/`Corollary`/`Lemma` declarations in the formal core
individually confirmed closed under the global context
(`rocq/PrintAssumptions.v`).

This repository is the accompanying formal development for two manuscripts
by the same author:

- *A Discipline of Partial Audit Classification: A Machine-Checked Kernel
  for Default-Free Audit Decisions* (in preparation for submission to
  *International Journal on Software Tools for Technology Transfer*)
- *Boundary Discipline for Accounting Information Systems: A Design-Science
  Architecture for Preserving Verification Failure* (in preparation for submission
  to *International Journal of Digital Accounting Research*)

Both papers describe the same underlying formalism from two different
angles (formal methods and tooling; accounting information systems). This
repository formalises the shared core once, in Coq/Rocq, and extracts it to
an executable OCaml classifier. See `NON_CLAIMS.md` for exactly what is and
is not established here before citing either paper against it.

## 1. The invariant

Audit systems sometimes use unverifiable assertions where verified ones are
required. This is close enough to a type error to be a useful analogy: an
assertion classified `Undefined` used where an assertion classified
`Verified` is required. The discipline that makes this rests on one rule —
and on soundness of an executable decision procedure, not on the type
being unconstructible: nothing stops a caller from constructing the value
`Unqualified` directly, any more than a type system stops a wrong literal.
What is proved is narrower and is what this repository actually claims: no
execution of `run_pipeline` produces `Unqualified` under a declared
specification without satisfying the rule below.

```
Admissible(Opinion) =>
  for every material assertion a used by Opinion:
      state(a) = Verified
```

`Undefined` is a success state: it is the correct output of a classifier
that has refused to speak beyond its verified boundary. The failure mode
this repository rules out is *silent conversion* — treating an
unverifiable assertion as accepted because the workflow wants a binary
output.

## 2. The six-state vocabulary

```coq
Inductive EvidenceState : Type :=
  | Verified
  | Refuted
  | Undefined
  | PresumptivelyVerified
  | PresumptivelyRefuted
  | EscalationRequired.
```

Only `Verified` can support an unqualified conclusion. `Undefined` means no
declared procedure's preconditions were met. The presumptive states may
guide triage; they cannot bind consequence. `EscalationRequired` marks a
defect in the boundary specification itself. See `rocq/Base.v`.

## 3. One command

```bash
make verify        # build, coqchk, worked-case fixture agreement
make demo          # run the three worked cases through the extracted CLI
```

## 4. What is proved

| Result | File | What it says |
| --- | --- | --- |
| `pipeline_unqualified_sound` | `rocq/Pipeline.v` | The end-to-end theorem: `run_pipeline` cannot decide `Unqualified` unless every material assertion is classified `Verified` *and* carries a validly admitted certificate. |
| `boundary_verified_has_witness` / `boundary_undefined_no_witness` | `rocq/Boundary.v` | A `Verified` classification has a concrete procedure witness; `boundary_verified_context_monotone` says adding evidence never loses one. |
| `validate_admission` + six rejection theorems (`certificate_for_wrong_proposal_rejected`, `non_verifier_certificate_rejected`, `non_proposer_certificate_rejected`, `proposer_certificate_rejected`, `decision_false_certificate_rejected`, `unverified_proposal_certificate_rejected`) | `rocq/SelfAdmission.v` | An admission certificate is accepted only if it names the right proposal, a registered `Verifier` distinct from the proposer, a registered `Proposer`, an affirmative decision, and a `Verified` proposal — all six conjuncts, each with its own rejection theorem. `build_packet_proposal_matches` (`rocq/Pipeline.v`) additionally proves the proposal `validate_admission` checks is structurally tied to the real classified assertion and state, closing a binding gap an external review found in an earlier version (see the commit history around `591d28e`). **Not established:** uniqueness of caller-supplied `ProcessId`/`ProposalId` values; reusing one may permit certificate replay across proposals or order-dependent registry lookup — see `NON_CLAIMS.md`. |
| `decide_opinion_unqualified_sound` + eight blocking corollaries + `all_valid_dependencies_allow_unqualified` | `rocq/Admissibility.v` | Soundness and completeness of the executable opinion decision `decide_opinion`. |
| `nonadmitted_material_emits_residual` / `nonmaterial_emits_no_residual` / `admitted_verified_emits_no_open_residual` / `residual_preservation(_chain)` / `classify_and_register_emits_for_dependency` / `orphan_escalation_sound` | `rocq/Residual.v` | Materiality-gated residual emission (with membership in the output log proved, not just non-disagreement with blocking), append-only preservation, and orphan-query soundness. |
| `default_free_admissibility` / `contrapositive_inadmissible` (+ `no_self_admission` / `role_separation`) | `rocq/Admissibility.v` / `rocq/SelfAdmission.v` | The v0.1 declarative layer: the same properties stated over `OpinionAdmissible`, a `Prop` defined to contain them by construction. Still true; no longer the central result. |

`decide_opinion` is not a separate postulate bolted onto the theorem: it
*is* the computation "admissible as an unqualified opinion" — every
conjunct of `dep_ok` (classified `Verified`, certificate present and valid)
is checked, and there is no other route through `run_pipeline` to
`Unqualified` that bypasses it. The theorems above are proved
**generally**, over abstract `Fact`/`Assertion`/`Process` types and any
`PipelineInput` you construct — not only for the three cases below. See
`NON_CLAIMS.md`.

## 5. Three worked cases (`rocq/Cases.v`)

Every case below runs the full pipeline (`run_pipeline`) — the same
function the extracted CLI calls — rather than hand-building an `Opinion`
or a `ResidualEntry` that merely reproduces what the pipeline was intended
to do.

| Case | What it shows | Result |
| --- | --- | --- |
| **Wirecard** (`Wirecard`), 6 fixtures | A cash-existence assertion against a five-precondition boundary, varying evidence, admission, and (in the two adversarial fixtures) the named proposer | incomplete evidence → `Undefined`, inadmissible; complete evidence, no certificate → `Verified` but inadmissible (`MissingCertificate`); complete evidence, valid admission → `Unqualified`; complete evidence, proposer self-certifies → inadmissible (`InvalidCertificate`); complete evidence, unregistered proposer → inadmissible (`InvalidCertificate`); complete evidence, proposer registered with the wrong role → inadmissible (`InvalidCertificate`) |
| **Continuous auditing** (`ContinuousAuditing`) | Ten transactions run through the pipeline; two reviewed and admitted, eight not | 8 residual entries emitted automatically; all survive any further workflow `step` ("clearing the dashboard") |
| **SQL Unknown** (`SqlUnknown`) | Score presence as boundary evidence via a `nullable_score_to_classification` adapter, plus the pre-existing two-renderer illustration | absence classifies `Undefined` and can never reach `Unqualified` under *any* registry/proposal/certificate (`pipeline_failed_material_dependency_blocks_unqualified`); the undisciplined renderer collapses `Unknown` and `0`, the disciplined one keeps them apart |

Running `make demo` prints all three; see `ocaml/cli/main.ml`, which mirrors
`Cases.v`'s fixtures exactly. These are illustrative traces exercising the
pipeline, not a reconstruction of what actually happened at Wirecard or a
claim about any real dataset. See `NON_CLAIMS.md`.

## 6. Architecture

```text
Boundary specification + evidence context      rocq/Boundary.v
        |  classify: mechanical Verified/Undefined branch, with a witness
        v
Classification proposal + admission certificate rocq/SelfAdmission.v
        |  validate_admission: certificate-based, role- and identity-checked
        v
Residual emission (append-only register)        rocq/Residual.v
        |  process_dependency / classify_and_register
        v
Opinion decision                                 rocq/Admissibility.v
        |  decide_opinion: sound and complete over dep_ok
        v
Pipeline (composes all of the above)             rocq/Pipeline.v
        |  run_pipeline; pipeline_unqualified_sound

        ============ Extraction.v ============

Extracted OCaml kernel                           ocaml/audit_kernel.ml
        |  run_pipeline and its supporting machinery, verbatim
        v
CLI: thin presentation layer over run_pipeline   ocaml/cli/main.ml
```

Only the `Type`/`bool`-valued decision procedures are extracted (`classify`,
`validate_admission`, `decide_opinion`, `process_dependency` /
`classify_and_register`, `run_pipeline`, and their supporting machinery).
The `Prop`-valued specification predicates (`admissible`, `OpinionAdmissible`,
`proposes`, `admits`, `step`) are not extracted — Coq erases `Prop` at
extraction time because they carry no computational content. That is
correct here, not an omission: they are proved about the classifier, not
run by it.

## 7. Repository layout

```text
rocq/
  Base.v            EvidenceState, AuditUse, stable identifier types
  Boundary.v        EqbSpec, Procedure, BoundarySpec, classify, witness/monotonicity theorems
  SelfAdmission.v   Role, Process, ClassificationProposal, AdmissionCertificate, validate_admission
  Admissibility.v   OpinionAdmissible (v0.1) + DependencyPacket, decide_opinion (v0.2)
  Residual.v        ResidualEntry, RegisterLog, process_dependency, classify_and_register
  Pipeline.v        PipelineInput, run_pipeline, pipeline_unqualified_sound
  PrintAssumptions.v  Print Assumptions on all 49 named declarations
  Cases.v           Wirecard, ContinuousAuditing, SqlUnknown worked instances
  Extraction.v      Extraction directives -> audit_kernel.ml/.mli
  _CoqProject, Makefile

ocaml/
  audit_kernel.ml/.mli   extracted kernel (regenerated by `make ocaml`, not hand-edited)
  cli/main.ml             the three-case demo runner (thin layer over run_pipeline)

tools/
  fixture_check.py   runs the CLI and checks it against the Cases.v Examples

NON_CLAIMS.md                        what this repository does and does not establish
CHANGELOG.md                         v0.1 -> v0.2 by commit, grouped
CITATION.cff                         software citation metadata (no release tag yet: see the file)
partial-audit-classification.opam    pinned toolchain versions (opam lint passes)
```

## 8. Building

This development is pinned to exact toolchain versions, not a range, because
the goal is a fixed, reproducible artefact tied to a specific paper
submission rather than a library meant to track upstream Coq/OCaml/dune
releases. `partial-audit-classification.opam` records the pin
(`ocaml.4.14.1`, `dune.3.14.0`, `coq.8.18.0`); CI builds against exactly
these. On Debian/Ubuntu, the versions in the default repositories at the
time of writing happen to match:

```bash
sudo apt-get install coq ocaml-nox ocaml-findlib ocaml-dune
make verify
```

If your package manager gives you different versions, `make verify` is
the actual test of whether this development still holds together, not
`8.18+`/`4.14+` as a loose compatibility claim -- that looser phrasing is
what the opam pin above replaced.

## 9. Provenance

This project does not originate its verifier architecture. Claim-relative
judgement, an explicit evidence-admission gate, a small trusted decision
boundary bridged to a declarative semantics by soundness theorems, and
explicit non-claims follow the pattern of the author's prior
`proof-carrying-*` line of work; what is new here is the object of study —
a typed, six-state classification of audit assertions with `Undefined` as
a preserved success state through composition to audit consequence.

This project was developed with AI assistance (Claude). Project scope, the
formal claims, and the decision to publish the artefact were made by the
repository author, who is responsible for it.

## License

MIT. See `LICENSE`.
