Require Import PAC.Base.
Require Import PAC.Boundary.
Require Import PAC.SelfAdmission.
Require Import PAC.Admissibility.
Require Import PAC.Residual.
Require Import PAC.Pipeline.

(** PrintAssumptions.v — item 11's proof-assumption audit. `coqchk`
    confirms every compiled module is closed under the global context,
    but that is a statement about the .vo files as compiled, not a
    standing guarantee that stays true as the development grows: a new
    file added to _CoqProject without also being added to the
    top-level Makefile's `coqchk` invocation compiles and links fine
    while never actually being re-checked (this happened once already
    in this repository's own v0.2 history -- Pipeline.v was omitted
    from that hardcoded list for one commit; see the commit history).

    [Print Assumptions] is a different, complementary check: run per
    theorem rather than per compiled module, it reports every axiom
    the named theorem's proof term transitively depends on, and prints
    "Closed under the global context" when there are none. Listing
    every publication-facing theorem here, in one file, means `make
    assumptions` (or grepping this file's compiled output) is one
    place to look, rather than trusting that coqchk's hardcoded module
    list was kept in sync by hand. *)

Print Assumptions Boundary.classify_verified_iff.
Print Assumptions Boundary.classify_undefined_iff.
Print Assumptions Boundary.procedure_satisfied_sound.
Print Assumptions Boundary.procedure_satisfied_complete.
Print Assumptions Boundary.boundary_verified_has_witness.
Print Assumptions Boundary.boundary_undefined_no_witness.
Print Assumptions Boundary.procedure_satisfied_context_monotone.
Print Assumptions Boundary.boundary_verified_context_monotone.

Print Assumptions SelfAdmission.no_self_admission.
Print Assumptions SelfAdmission.role_separation.
Print Assumptions SelfAdmission.valid_admission_implies_verified.
Print Assumptions SelfAdmission.valid_admission_implies_distinct_process.
Print Assumptions SelfAdmission.proposer_certificate_rejected.
Print Assumptions SelfAdmission.certificate_for_wrong_proposal_rejected.
Print Assumptions SelfAdmission.non_verifier_certificate_rejected.
Print Assumptions SelfAdmission.non_proposer_certificate_rejected.
Print Assumptions SelfAdmission.decision_false_certificate_rejected.
Print Assumptions SelfAdmission.unverified_proposal_certificate_rejected.

Print Assumptions Admissibility.default_free_admissibility.
Print Assumptions Admissibility.contrapositive_inadmissible.
Print Assumptions Admissibility.composition_weakest_link.
Print Assumptions Admissibility.decide_opinion_unqualified_sound.
Print Assumptions Admissibility.decide_opinion_blocked.
Print Assumptions Admissibility.undefined_blocks_unqualified.
Print Assumptions Admissibility.refuted_blocks_unqualified.
Print Assumptions Admissibility.presumptive_blocks_unqualified.
Print Assumptions Admissibility.escalation_blocks_unqualified.
Print Assumptions Admissibility.verified_without_admission_blocks_unqualified.
Print Assumptions Admissibility.invalid_admission_blocks_unqualified.
Print Assumptions Admissibility.all_valid_dependencies_allow_unqualified.

Print Assumptions Residual.residual_preservation.
Print Assumptions Residual.residual_preservation_chain.
Print Assumptions Residual.orphan_escalation_sound.
Print Assumptions Residual.nonadmitted_material_emits_residual.
Print Assumptions Residual.admitted_verified_emits_no_open_residual.
Print Assumptions Residual.nonmaterial_emits_no_residual.
Print Assumptions Residual.classify_and_register_step.
Print Assumptions Residual.classify_and_register_emits_for_dependency.

Print Assumptions Pipeline.build_packet_proposal_matches.
Print Assumptions Pipeline.pipeline_unqualified_sound.
Print Assumptions Pipeline.pipeline_failed_material_dependency_blocks_unqualified.
Print Assumptions Pipeline.pipeline_failed_material_dependency_emits_residual.
