Require Import List.
Import ListNotations.
Require Import PAC.Base.
Require Import PAC.Boundary.
Require Import PAC.SelfAdmission.
Require Import PAC.Admissibility.
Require Import PAC.Residual.

(** Pipeline.v — the orchestration layer:

      boundary classification
              |
      classification proposal
              |
      admission validation
              |
      residual emission
              |
      opinion decision

    Every earlier module proves one stage sound in isolation:
    Boundary.v's [classify] (with its witness/monotonicity theorems),
    SelfAdmission.v's [validate_admission], Residual.v's
    [process_dependency]/[classify_and_register], and Admissibility.v's
    [decide_opinion]. This module is what actually wires them together
    into one function, [run_pipeline], and [pipeline_unqualified_sound]
    is the end-to-end theorem: not a new proof from scratch, but the
    composition of the per-stage theorems already proved, over one
    input record instead of a hand-assembled list of
    [DependencyPacket]s. This is the theorem that justifies "by
    construction" for the *pipeline*, as
    [decide_opinion_unqualified_sound] does for the decision stage
    alone. *)

(** Everything one run of the pipeline needs: a boundary specification
    and the evidence context to classify against (with the context's
    own stable identity, for the residual entries this run may emit),
    which assertions are in scope and which of those are material, a
    proposal identity and proposer per assertion, an optional admission
    certificate per assertion, and the process registry admission is
    checked against.

    v0.2 review finding: an earlier version of this record let the
    caller supply a complete [ClassificationProposal] per assertion
    ([pi_proposal : Assertion -> ClassificationProposal Assertion]).
    Nothing checked that a returned proposal's own
    [proposal_assertion]/[proposal_classification] fields matched the
    assertion [build_packet] was actually classifying, or the
    [dep_state] [classify] had just computed for it. A certificate
    validly admitting a *different* proposal -- for a different
    assertion, or claiming a different classification -- could
    therefore validate a packet it had nothing to do with, as long as
    [classify] separately happened to return [Verified] for the real
    assertion. [pi_proposal] is replaced below by [pi_proposal_id] and
    [pi_proposer]: [build_packet] constructs the [ClassificationProposal]
    itself, from the real assertion and the real, freshly computed
    classification, so a mismatched proposal is not a validation
    failure to be checked for -- it is not a value [build_packet] can
    construct in the first place. *)
Record PipelineInput (Fact Assertion : Type) := mkPipelineInput {
  pi_bspec       : BoundarySpec Fact Assertion;
  pi_eq          : EqbSpec Fact;
  pi_context     : list Fact;
  pi_context_id  : ContextId;
  pi_assertions  : list Assertion;
  pi_material    : Assertion -> bool;
  pi_proposal_id : Assertion -> ProposalId;
  pi_proposer    : Assertion -> ProcessId;
  pi_certificate : Assertion -> option AdmissionCertificate;
  pi_registry    : ProcessRegistry
}.
Arguments mkPipelineInput {Fact Assertion} _ _ _ _ _ _ _ _ _ _.
Arguments pi_bspec {Fact Assertion} _.
Arguments pi_eq {Fact Assertion} _.
Arguments pi_context {Fact Assertion} _.
Arguments pi_context_id {Fact Assertion} _.
Arguments pi_assertions {Fact Assertion} _.
Arguments pi_material {Fact Assertion} _.
Arguments pi_proposal_id {Fact Assertion} _.
Arguments pi_proposer {Fact Assertion} _.
Arguments pi_certificate {Fact Assertion} _.
Arguments pi_registry {Fact Assertion} _.

(** Stage 1-2: classify this assertion against the declared boundary,
    then construct its proposal from that same assertion and that same
    computed classification, and package the result as a dependency
    packet. This is where [classify]'s output actually becomes the
    [dep_state] every later stage reasons about, and also becomes
    [proposal_classification] on the proposal built for it: the two
    cannot diverge, because both are read from the one local [s]
    below rather than supplied independently. *)
Definition build_packet {Fact Assertion : Type}
    (inp : PipelineInput Fact Assertion) (a : Assertion) : DependencyPacket Assertion :=
  let s := classify (pi_bspec inp) (pi_eq inp) (pi_context inp) a in
  let p := mkClassificationProposal (pi_proposal_id inp a) a s (pi_proposer inp a) in
  mkDependencyPacket a (pi_material inp a) s p (pi_certificate inp a).

Lemma build_packet_proposal_matches :
  forall {Fact Assertion : Type} (inp : PipelineInput Fact Assertion) (a : Assertion),
    proposal_assertion (dep_proposal (build_packet inp a)) = a /\
    proposal_classification (dep_proposal (build_packet inp a)) = dep_state (build_packet inp a).
Proof.
  intros Fact Assertion inp a. unfold build_packet. simpl. split; reflexivity.
Qed.

Record AuditDecision (Assertion : Type) := mkAuditDecision {
  decision_classifications : list EvidenceState;
  decision_residuals       : RegisterLog Assertion;
  decision_opinion         : OpinionDecision Assertion
}.
Arguments mkAuditDecision {Assertion} _ _ _.
Arguments decision_classifications {Assertion} _.
Arguments decision_residuals {Assertion} _.
Arguments decision_opinion {Assertion} _.

(** Stages 3-5 in one pass: [classify_and_register] validates admission
    for every packet as it decides whether to emit a residual (stages
    3-4), and [decide_opinion] over the same packet list is the opinion
    decision (stage 5). [start_id]/[log] thread a fresh-identifier
    counter and the register's prior history through, exactly as
    [classify_and_register] requires. *)
Definition run_pipeline {Fact Assertion : Type}
    (inp : PipelineInput Fact Assertion) (start_id : ResidualId) (log : RegisterLog Assertion)
    : AuditDecision Assertion :=
  let deps := map (build_packet inp) (pi_assertions inp) in
  let result := classify_and_register (pi_registry inp) (boundary_id (pi_bspec inp))
                  (boundary_version (pi_bspec inp)) (pi_context_id inp) start_id deps log in
  mkAuditDecision (fst result) (snd result) (decide_opinion (pi_registry inp) deps).

(** The end-to-end soundness theorem. Given the declared boundary,
    evidence context, assertion set, process registry, and admission
    certificates threaded through [inp], the pipeline cannot decide
    [Unqualified] unless every material assertion in scope is both
    classified [Verified] under the declared boundary and carries a
    validly admitted certificate. *)
Theorem pipeline_unqualified_sound :
  forall {Fact Assertion : Type} (inp : PipelineInput Fact Assertion)
    (start_id : ResidualId) (log : RegisterLog Assertion),
    decision_opinion (run_pipeline inp start_id log) = Unqualified ->
    forall a, In a (pi_assertions inp) -> pi_material inp a = true ->
      classify (pi_bspec inp) (pi_eq inp) (pi_context inp) a = Verified /\
      dep_valid_admission (pi_registry inp) (build_packet inp a) = true.
Proof.
  intros Fact Assertion inp start_id log Hdec a Hin Hmat.
  unfold run_pipeline in Hdec; simpl in Hdec.
  assert (Hin' : In (build_packet inp a) (map (build_packet inp) (pi_assertions inp)))
    by (apply in_map; exact Hin).
  assert (Hmat' : dep_material (build_packet inp a) = true) by (simpl; exact Hmat).
  destruct (decide_opinion_unqualified_sound (pi_registry inp)
              (map (build_packet inp) (pi_assertions inp)) Hdec
              (build_packet inp a) Hin' Hmat') as [Hs Hv].
  split; [simpl in Hs; exact Hs | exact Hv].
Qed.

(** A material assertion that is not [dep_ok] blocks [Unqualified] --
    a direct instance of [decide_opinion_blocked] over the packet
    [run_pipeline] itself builds. This is a weaker statement than its
    v0.2-review-era name suggested (that name promised a residual-log
    relationship this theorem's statement never mentioned), so it is
    named for exactly what it proves; see
    [pipeline_failed_material_dependency_emits_residual] below for the
    residual-membership statement the earlier name was reaching for. *)
Theorem pipeline_failed_material_dependency_blocks_unqualified :
  forall {Fact Assertion : Type} (inp : PipelineInput Fact Assertion)
    (start_id : ResidualId) (log : RegisterLog Assertion) (a : Assertion),
    In a (pi_assertions inp) -> pi_material inp a = true ->
    dep_ok (pi_registry inp) (build_packet inp a) = false ->
    decision_opinion (run_pipeline inp start_id log) <> Unqualified.
Proof.
  intros Fact Assertion inp start_id log a Hin Hmat Hnok.
  unfold run_pipeline; simpl.
  eapply decide_opinion_blocked with (d := build_packet inp a).
  - apply in_map. exact Hin.
  - simpl. exact Hmat.
  - exact Hnok.
Qed.

(** The stronger, residual-aware statement: a material assertion that
    is not [dep_ok] not only blocks [Unqualified]
    (above) but has a matching entry demonstrably present in
    [decision_residuals], with the same assertion and the same
    classification -- not merely that emission and blocking cannot
    disagree in principle, but that this specific run's output log
    actually contains the entry. Built from
    [classify_and_register_emits_for_dependency] (Residual.v) applied
    to the packet [build_packet] constructs for [a], rather than
    proved independently. *)
Theorem pipeline_failed_material_dependency_emits_residual :
  forall {Fact Assertion : Type} (inp : PipelineInput Fact Assertion)
    (start_id : ResidualId) (log : RegisterLog Assertion) (a : Assertion),
    In a (pi_assertions inp) -> pi_material inp a = true ->
    dep_ok (pi_registry inp) (build_packet inp a) = false ->
    exists e, residual_assertion e = a /\
              residual_state e = classify (pi_bspec inp) (pi_eq inp) (pi_context inp) a /\
              In e (decision_residuals (run_pipeline inp start_id log)).
Proof.
  intros Fact Assertion inp start_id log a Hin Hmat Hnok.
  unfold run_pipeline, decision_residuals; simpl.
  destruct (classify_and_register_emits_for_dependency (pi_registry inp)
              (boundary_id (pi_bspec inp)) (boundary_version (pi_bspec inp)) (pi_context_id inp)
              start_id (map (build_packet inp) (pi_assertions inp)) (build_packet inp a)
              (in_map (build_packet inp) (pi_assertions inp) a Hin) Hmat Hnok log)
    as [e [He1 [He2 He3]]].
  exists e. repeat split; assumption.
Qed.
