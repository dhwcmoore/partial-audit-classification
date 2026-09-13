# Manuscript overlap report

Prepared while separating the two manuscripts into exclusive technical
(STTT) and exclusive AIS-architecture (IJDAR) contributions. This is
analysis for the corresponding author's use in the cover letter to each
editor; it is not itself sent to either editor, and neither manuscript
has been submitted, as of the commit this file was added in.

- **STTT**: *A Discipline of Partial Audit Classification: A
  Machine-Checked Kernel for Default-Free Audit Decisions*, prepared for
  the *International Journal on Software Tools for Technology Transfer*.
- **IJDAR**: *Boundary Discipline for Accounting Information Systems: A
  Design-Science Architecture for Preserving Verification Failure*,
  prepared for the *International Journal of Digital Accounting
  Research*.

## What is shared

**Problem and vocabulary.** Both manuscripts open from the same failure
mode -- silent conversion, the operational treatment of an unresolved
assertion as accepted without an explicit non-affirmative classification
-- and both state it against the same Central Invariant / Principle: no
unmodified audit opinion may rely affirmatively on a material assertion
unless it is classified Verified and validly admitted. Both use the same
six-state classification vocabulary (`Verified`, `Refuted`, `Undefined`,
`PresumptivelyVerified`, `PresumptivelyRefuted`, `EscalationRequired`),
the same composition rule (a single unresolved material dependency blocks
an unqualified opinion regardless of how many others pass), and the same
Wirecard and continuous-auditing narratives as running cases, corrected
against the same documented history in both places (the Philippine banks
were reachable and responded promptly once asked directly; the actual
failure was a confirmation route run through an uncontrolled third-party
trustee, not jurisdiction).

**Artefact.** Both manuscripts cite the same companion Coq/Rocq
development and its extracted OCaml classifier as their formal-validation
artefact. The artefact is not duplicated; each manuscript describes the
same repository, at the same level of trust, but at very different levels
of technical detail (see below).

Both manuscripts explicitly disclose this overlap to the reader, in a
"Note on a related submission" naming the other manuscript, its target
journal, and the division of contribution stated below, and state that
notification to both editors will occur before either submission.

## STTT-exclusive contribution

The executable kernel itself: the typed state and identifier model; the
`EqbSpec`/`classify` boundary-evaluation function and its witness and
monotonicity theorems; `validate_admission` and its six rejection
theorems; `process_dependency`/`classify_and_register` and the four
separate residual claims (emission, historical preservation, pipeline
log extension, orphan escalation); `decide_opinion` and its soundness and
completeness theorems; `run_pipeline` and the end-to-end soundness
theorem; the declarative layer retained alongside the executable one;
the trusted-computing-base analysis and extraction boundary; exact
declaration counts and `Print Assumptions` results; and the six Wirecard
fixtures, ten-transaction continuous-auditing fixture, and general
SQL-absence fixture as regression-tested demonstrations of the kernel
specifically. STTT states concrete Coq definitions, function bodies, and
complete theorem statements; IJDAR does not.

## IJDAR-exclusive contribution

The accounting-information-systems design-science architecture built on
top of the shared kernel: the design-science research method and its
evaluation criteria; the Verification Balance Sheet developed as an
accounting instrument with required fields, responsible organisational
roles, and creation/review points, including a worked Wirecard balance
sheet; the Risk Assignment Register developed as a full record schema
with a worked kernel/AIS-layer boundary and three illustrative entries;
an organisational responsibility model naming nine distinct roles and
stating precisely what registry-level identity separation does and does
not establish about organisational independence; a standards-mapping
table across ISA 500, 505, 580, 705, CAS 705, PCAOB AS 3105, and ESEF;
four precisely defined inspection measures (boundary coverage ratio,
undefined-region materiality, residual assignment rate, orphan rate); a
proposed XBRL/ESEF machine-readable assurance extension; and the
organisational depth of the Wirecard and continuous-auditing cases
(audit-committee escalation, management reporting, aggregation).

## What neither manuscript claims

Neither claims the shared material -- the invariant, the vocabulary, the
artefact, the corrected Wirecard history -- is exclusive to it. Neither
manuscript's findings depend on prior acceptance of the other. Formal
validation is described in one register-appropriate way in each: STTT
states it as the paper's own central technical result; IJDAR states it,
in far less detail, as supporting evaluation evidence for an architecture
whose own contribution lies elsewhere.

## One-page editor-facing overlap table

| | STTT (this submission to STTT) | IJDAR (this submission to IJDAR) |
|---|---|---|
| Target journal | International Journal on Software Tools for Technology Transfer | International Journal of Digital Accounting Research |
| Central claim | An executable audit-classification pipeline can be constructed and machine-checked so that it cannot return `Unqualified` unless every material dependency is verified and validly admitted | How an accounting information system should be designed so verification failure remains durable and consequence-bearing from evidence intake through disclosure |
| Primary audience | Formal methods / software tools | Accounting information systems |
| Exclusive contribution | Executable kernel: data structures, decision procedures, theorem suite, extraction, TCB analysis, regression fixtures | AIS architecture: design-science method, Verification Balance Sheet, Risk Assignment Register, responsibility model, standards mapping, inspection measures, XBRL/ESEF proposal |
| Shared | Central invariant, six-state vocabulary, composition rule, corrected Wirecard/CA narratives, companion Coq/Rocq artefact (cited, not reproduced in the other) |
| Formal proof detail | Full: concrete definitions, theorem statements, module structure, declaration counts | Minimal: one summary table (Table 7) plus a short paragraph; full detail deferred to STTT |
| Empirical claims | None | None (explicit design-science evaluation only; future-evaluation programme stated, not carried out) |
| Word/page order of magnitude | ~26 pages | ~31 pages |

*Prepared for the corresponding author's cover letters. Not sent to
either editor as part of this revision.*
