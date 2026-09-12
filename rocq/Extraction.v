Require Import PAC.Base.
Require Import PAC.Boundary.
Require Import PAC.Admissibility.
Require Import PAC.Residual.
Require Import PAC.SelfAdmission.

Require Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlString.
Require Import Coq.extraction.ExtrOcamlNatInt.

(** Extraction.v — the executable boundary. Only the Type/bool-valued
    decision procedures are extracted: [classify] and its supporting
    machinery, which is what a runtime classifier actually computes. The Prop-valued specification predicates (admissible,
    OpinionAdmissible, proposes, admits, step) are not extracted: Coq
    erases Prop at extraction time because they carry no computational
    content, and that is the correct behaviour here, not an omission --
    they are proved about the classifier, not run by it. This mirrors
    the two-layer structure both papers describe: a declarative
    semantics bridged to an executable classifier by the theorems in
    Admissibility.v and SelfAdmission.v. *)

Extraction Language OCaml.

Extraction "audit_kernel.ml"
  EvidenceState AuditUse eqb_state evidence_state_dec supports_unqualified
  mkEqbSpec eqb
  mkProcedure procedure_id procedure_name procedure_preconditions procedure_covers
  mkBoundarySpec boundary_id boundary_version boundary_procedures
  procedure_satisfied classify has_fact has_all
  mkOpinion op_deps
  mkResidualEntry residual_assertion residual_state residual_owner RegisterLog
  is_orphaned orphaned_entries
  Role Proposer Verifier mkProcess process_id process_role
  ProcessRegistry process_lookup
  mkClassificationProposal proposal_id proposal_assertion proposal_classification proposal_process
  mkAdmissionCertificate admission_proposal_id admission_verifier admission_decision
  validate_admission.
