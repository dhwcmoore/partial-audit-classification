# Partial Audit Classification

> No audit conclusion may depend on a material assertion whose verification
> state is undefined.

**Status:** v0.1.0. The kernel, the admissibility/residual/self-admission
theorems, three worked cases, and an extracted OCaml CLI are built. Coq
8.18.0, `coqchk` clean, no `Admitted`, no `Axiom`.

This repository is the accompanying formal development for two manuscripts
by the same author:

- *A Discipline of Partial Audit Classification: On the Correct Treatment
  of Undefined Audit Assertions* (submitted, *International Journal on
  Software Tools for Technology Transfer*)
- *Boundary Discipline for Accounting Information Systems: On the Correct
  Treatment of Undefined Audit Assertions* (submitted, *International
  Journal of Digital Accounting Research*)

Both papers describe the same underlying formalism from two different
angles (formal methods and tooling; accounting information systems). This
repository formalises the shared core once, in Coq/Rocq, and extracts it to
an executable OCaml classifier. See `NON_CLAIMS.md` for exactly what is and
is not established here before citing either paper against it.

## 1. The invariant

Audit systems sometimes use unverifiable assertions where verified ones are
required. This is a type error: an assertion of type `Undefined` used where
an assertion of type `Verified` is required. The discipline that makes this
error unrepresentable rests on one rule:

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

| Theorem | File | Paper reference |
| --- | --- | --- |
| Default-Free Admissibility (+ Contrapositive) | `rocq/Admissibility.v` | Theorem 1 / Corollary, both papers |
| Composition (weakest-link) | `rocq/Admissibility.v` | Composition rule, both papers |
| Residual Preservation (+ chained) | `rocq/Residual.v` | Theorem 2, both papers |
| No Self-Admission / Role Separation | `rocq/SelfAdmission.v` | Theorem 3, both papers |

`OpinionAdmissible` is not a separate postulate bolted onto the theorem: it
*is* the definition of "admissible as an unqualified opinion." There is no
other route to admissibility in this development that bypasses checking
every material dependency, which is what the papers mean by the type error
being "unrepresentable" rather than merely discouraged. The theorems above
are proved **generally**, over abstract `Fact`/`Assertion`/`Process` types —
not only for the three cases below. See `NON_CLAIMS.md`.

## 5. Three worked cases (`rocq/Cases.v`)

| Case | What it shows | Result |
| --- | --- | --- |
| **Wirecard** (`Wirecard`) | A cash-existence assertion checked against a five-precondition direct-bank-confirmation boundary, with three preconditions failing | `state = Undefined`; opinion inadmissible |
| **Continuous auditing** (`ContinuousAuditing`) | Ten transactions, two reviewed, eight deprioritised | 8 residual entries survive "clearing the dashboard"; none is `Verified` |
| **SQL Unknown** (`SqlUnknown`) | A risk score rendered two ways downstream of `NULL` | The undisciplined renderer collapses `Unknown` and `0` to the same value; the disciplined one keeps them apart |

Running `make demo` prints all three:

```
Case 1: Wirecard cash-existence assertion (Section 6.1 / Section 7)
----------------------------------------------------------------------
  Assertion:            EUR 1.9bn held in Philippine trustee accounts
  Observed evidence:    bank exists, account identifier supplied only
  Classification:       Undefined
  Admissible as unqualified opinion: no

  Counterfactual with full evidence (all five preconditions met):
  Classification:       Verified
```

These are illustrative traces exercising the boundary machinery, not a
reconstruction of what actually happened at Wirecard or a claim about any
real dataset. See `NON_CLAIMS.md`.

## 6. Architecture

```text
Boundary specification + evidence context      rocq/Boundary.v
        |  boundary_state: mechanical Verified/Undefined branch
        v
Admissibility over an Opinion's dependencies    rocq/Admissibility.v
        |  OpinionAdmissible, default_free_admissibility
        v
Residual register (append-only)                 rocq/Residual.v
        |  residual_preservation
        v
Role-separated proposal / admission              rocq/SelfAdmission.v
        |  no_self_admission

        ============ Extraction.v ============

Extracted OCaml kernel                           ocaml/audit_kernel.ml
        |  boundary_state and its supporting machinery, verbatim
        v
CLI running the three worked cases               ocaml/cli/main.ml
```

Only the `Type`/`bool`-valued decision procedures are extracted
(`boundary_state` and its supporting machinery). The `Prop`-valued
specification predicates (`admissible`, `OpinionAdmissible`, `proposes`,
`admits`, `step`) are not extracted — Coq erases `Prop` at extraction time
because they carry no computational content. That is correct here, not an
omission: they are proved about the classifier, not run by it.

## 7. Repository layout

```text
rocq/
  Base.v            EvidenceState, AuditUse
  Boundary.v        Procedures, preconditions, boundary_state
  Admissibility.v   Opinion, OpinionAdmissible, the three admissibility theorems
  Residual.v        ResidualEntry, RegisterLog, residual_preservation
  SelfAdmission.v   Role, Process, no_self_admission
  Cases.v           Wirecard, ContinuousAuditing, SqlUnknown worked instances
  Extraction.v      Extraction directives -> audit_kernel.ml/.mli
  _CoqProject, Makefile

ocaml/
  audit_kernel.ml/.mli   extracted kernel (regenerated by `make ocaml`, not hand-edited)
  cli/main.ml             the three-case demo runner

tools/
  fixture_check.py   runs the CLI and checks it against the Cases.v Examples

NON_CLAIMS.md         what this repository does and does not establish
```

## 8. Building

Requirements: Coq/Rocq 8.18+, OCaml 4.14+, dune 3.x. On Debian/Ubuntu:

```bash
sudo apt-get install coq ocaml-nox ocaml-findlib ocaml-dune
make verify
```

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
