Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import PAC.Base.
Require Import PAC.Boundary.
Require Import PAC.SelfAdmission.
Require Import PAC.Admissibility.
Require Import PAC.Residual.
Require Import PAC.Pipeline.

(** Cases.v — the three worked examples from Section 7 (STTT) / Sections
    7-8 (AIS): Wirecard as a classification trace, continuous auditing
    exception queues, and the SQL Unknown collapse. These exercise the
    general theorems in Pipeline.v, Admissibility.v, and Residual.v on
    finite instances; they are illustrations of theorems proved
    generally, not the extent of what is proved and not a claim that
    every possible boundary specification or workflow has been
    enumerated. See NON_CLAIMS.md.

    v0.2 change from v0.1: every fixture below is run through
    [run_pipeline] -- boundary classification, admission validation,
    residual emission, and opinion decision all computed by the same
    function the extracted classifier runs -- rather than hand-building
    an [Opinion] or a [ResidualEntry] that merely reproduces what the
    pipeline was intended to do. *)

Module Wirecard.

  (** The five preconditions of "direct bank confirmation" (Section 4's
      running example / the Wirecard trace of Section 7.1 and Section
      7 of the AIS paper). *)
  Inductive WFact :=
    | BankExistsIndependent
    | ConfirmationRouteControlledByAuditor
    | JurisdictionPermitsDirectConfirmation
    | AccountIdentifierSupplied
    | AuthenticatedChannel.

  Definition wfeq (x y : WFact) : bool :=
    match x, y with
    | BankExistsIndependent, BankExistsIndependent => true
    | ConfirmationRouteControlledByAuditor, ConfirmationRouteControlledByAuditor => true
    | JurisdictionPermitsDirectConfirmation, JurisdictionPermitsDirectConfirmation => true
    | AccountIdentifierSupplied, AccountIdentifierSupplied => true
    | AuthenticatedChannel, AuthenticatedChannel => true
    | _, _ => false
    end.

  Lemma wfeq_true_iff : forall x y, wfeq x y = true <-> x = y.
  Proof.
    intros x y; split; intro H.
    - destruct x, y; simpl in H; try congruence.
    - subst; destruct y; reflexivity.
  Qed.

  Definition WFactEq : EqbSpec WFact := mkEqbSpec wfeq wfeq_true_iff.

  Inductive WAssertion := CashExistencePhilippineTrustee.

  Definition direct_bank_confirmation : Procedure WFact WAssertion :=
    mkProcedure 0 "Direct bank confirmation"
      [BankExistsIndependent; ConfirmationRouteControlledByAuditor;
       JurisdictionPermitsDirectConfirmation; AccountIdentifierSupplied;
       AuthenticatedChannel]
      (fun _ => true).

  Definition boundary : BoundarySpec WFact WAssertion :=
    mkBoundarySpec 0 1 [direct_bank_confirmation].

  (** Observed evidence per Section 7.1: an independent bank exists, an
      account identifier was supplied, and the jurisdiction permits
      direct confirmation -- the Philippine banks were reachable and, in
      fact, responded promptly once asked directly in June 2020. What
      was never established was that the confirmation route was
      controlled by the auditor (it ran through a third-party trustee
      for years) or that any response came through an authenticated
      direct channel. Two of five preconditions fail; the jurisdiction
      one does not. *)
  Definition observed_evidence : list WFact :=
    [BankExistsIndependent; JurisdictionPermitsDirectConfirmation; AccountIdentifierSupplied].

  Example wirecard_state_undefined :
    classify boundary WFactEq observed_evidence CashExistencePhilippineTrustee = Undefined.
  Proof. reflexivity. Qed.

  (** The disciplined counterfactual: with every precondition satisfied,
      the same assertion is Verified. This is not a claim about what
      actually happened at Wirecard; it exhibits that the boundary
      specification is not vacuous and can produce Verified when the
      evidence genuinely supports it. *)
  Definition full_evidence : list WFact :=
    [BankExistsIndependent; ConfirmationRouteControlledByAuditor;
     JurisdictionPermitsDirectConfirmation; AccountIdentifierSupplied;
     AuthenticatedChannel].

  Example wirecard_state_verified_with_full_evidence :
    classify boundary WFactEq full_evidence CashExistencePhilippineTrustee = Verified.
  Proof. reflexivity. Qed.

  Definition material_all (_ : WAssertion) : bool := true.

  (** A minimal registry: one proposing process, one verifying process,
      distinct identities, plus a second verifier used only by the
      wrong-role adversarial fixture below (fixture 6), so that fixture
      isolates "registered with the wrong role" from "same identity as
      the admitting verifier" rather than conflating the two. *)
  Definition proposer : Process := mkProcess 1 Proposer.
  Definition verifier : Process := mkProcess 2 Verifier.
  Definition verifier2 : Process := mkProcess 3 Verifier.
  Definition registry : ProcessRegistry := [proposer; verifier; verifier2].

  Definition valid_cert : AdmissionCertificate :=
    mkAdmissionCertificate 100 (process_id verifier) true.
  Definition self_cert : AdmissionCertificate :=
    mkAdmissionCertificate 100 (process_id proposer) true.

  (** No [claimed : EvidenceState] parameter here (v0.1 of this fixture
      had one): [build_packet] (Pipeline.v) now constructs the
      proposal's classification from the actual [classify] output for
      the actual assertion, not from a value the fixture separately
      asserted. There is consequently nothing left for a fixture, or
      any other caller, to get out of sync with the real classification
      -- the parameter that could have disagreed with it no longer
      exists. *)
  Definition input_for (ctx : list WFact) (cert : option AdmissionCertificate)
      : PipelineInput WFact WAssertion :=
    mkPipelineInput boundary WFactEq ctx 0
      [CashExistencePhilippineTrustee] material_all
      (fun _ => 100) (fun _ => process_id proposer) (fun _ => cert) registry.

  (** Fixture 1: incomplete evidence. Classification is Undefined; no
      certificate is even presented, since there is nothing to admit.
      A residual is emitted for the failure to verify, and the opinion
      is inadmissible. *)
  Definition input_incomplete := input_for observed_evidence None.

  Example fixture1_decision :
    decision_opinion (run_pipeline input_incomplete 0 []) =
      InadmissibleOpinion [NotVerified CashExistencePhilippineTrustee Undefined].
  Proof. reflexivity. Qed.

  Example fixture1_residual_emitted :
    List.length (decision_residuals (run_pipeline input_incomplete 0 [])) = 1.
  Proof. reflexivity. Qed.

  (** Fixture 2: complete evidence, but no admission certificate was
      presented. Classification is Verified -- the boundary genuinely
      supports it -- but Verified alone is not [dep_ok]: a residual is
      still emitted, for the missing certificate rather than for a
      classification failure, and the opinion is still inadmissible.
      This is the fixture that exercises the paper's two-conjunct rule
      most directly: state = Verified is necessary but not sufficient. *)
  Definition input_no_certificate := input_for full_evidence None.

  Example fixture2_decision :
    decision_opinion (run_pipeline input_no_certificate 0 []) =
      InadmissibleOpinion [MissingCertificate CashExistencePhilippineTrustee].
  Proof. reflexivity. Qed.

  Example fixture2_residual_emitted :
    List.length (decision_residuals (run_pipeline input_no_certificate 0 [])) = 1.
  Proof. reflexivity. Qed.

  (** Fixture 3: complete evidence, admitted by the verifier, whose
      identity is distinct from the proposer's. Classification is
      Verified, the certificate validates, no residual is left open,
      and the opinion is Unqualified. *)
  Definition input_valid_admission := input_for full_evidence (Some valid_cert).

  Example fixture3_decision :
    decision_opinion (run_pipeline input_valid_admission 0 []) = Unqualified.
  Proof. reflexivity. Qed.

  Example fixture3_no_residual :
    decision_residuals (run_pipeline input_valid_admission 0 []) = [].
  Proof. reflexivity. Qed.

  (** Fixture 4: complete evidence, but the "certificate" names the
      proposer as its own admitting verifier. [validate_admission]
      rejects it (SelfAdmission.v's [proposer_certificate_rejected]),
      the certificate is invalid rather than merely missing, and the
      opinion is inadmissible even though the classification itself is
      Verified. This is the fixture that exhibits Theorem 3 (No
      Self-Admission) inside the pipeline, not just at the level of the
      abstract [Role] type. *)
  Definition input_self_certified := input_for full_evidence (Some self_cert).

  Example fixture4_decision :
    decision_opinion (run_pipeline input_self_certified 0 []) =
      InadmissibleOpinion [InvalidCertificate CashExistencePhilippineTrustee].
  Proof. reflexivity. Qed.

  Example fixture4_residual_emitted :
    List.length (decision_residuals (run_pipeline input_self_certified 0 [])) = 1.
  Proof. reflexivity. Qed.

  (** ** Adversarial fixtures

      Two classes of malformed input a v0.2 review found this
      development did not yet reject.

      Proposal/assertion substitution (a proposal returned for
      assertion A actually naming assertion B) and
      proposal/classification substitution (a proposal claiming
      Verified when the real computed state disagrees) are not tested
      here as fixtures, because [PipelineInput] no longer has a field
      through which either is expressible: [build_packet]
      (Pipeline.v) constructs the [ClassificationProposal] itself from
      the real assertion and the real [classify] output, and
      [build_packet_proposal_matches] (Pipeline.v) proves the two
      always agree, for every [PipelineInput], not merely for the
      fixtures below. There is consequently nothing left to write an
      adversarial fixture *of*: the class of bug is gone by
      construction, not merely rejected at validation time. *)

  (** Fixture 5: complete evidence, a certificate that would otherwise
      validate, but naming a proposer identifier ([999]) that is not
      in the registry at all. [non_proposer_certificate_rejected]
      (SelfAdmission.v) is what rejects this. *)
  Definition input_unregistered_proposer : PipelineInput WFact WAssertion :=
    mkPipelineInput boundary WFactEq full_evidence 0
      [CashExistencePhilippineTrustee] material_all
      (fun _ => 100) (fun _ => 999) (fun _ => Some valid_cert) registry.

  Example fixture5_decision :
    decision_opinion (run_pipeline input_unregistered_proposer 0 []) =
      InadmissibleOpinion [InvalidCertificate CashExistencePhilippineTrustee].
  Proof. reflexivity. Qed.

  (** Fixture 6: complete evidence, a certificate that would otherwise
      validate, but naming the second verifier's identity as the
      proposer -- registered, distinct from the admitting verifier
      (so the distinct-identity conjunct passes), but with [Verifier]
      rather than [Proposer] authority. Isolates
      [non_proposer_certificate_rejected] specifically, rather than
      also tripping the distinct-identity check as reusing the
      admitting verifier's own id would. *)
  Definition input_wrong_role_proposer : PipelineInput WFact WAssertion :=
    mkPipelineInput boundary WFactEq full_evidence 0
      [CashExistencePhilippineTrustee] material_all
      (fun _ => 100) (fun _ => process_id verifier2) (fun _ => Some valid_cert) registry.

  Example fixture6_decision :
    decision_opinion (run_pipeline input_wrong_role_proposer 0 []) =
      InadmissibleOpinion [InvalidCertificate CashExistencePhilippineTrustee].
  Proof. reflexivity. Qed.

End Wirecard.


Module ContinuousAuditing.

  (** Ten transactions stand in for the paper's 10,000-transaction
      example (Section 7.2 / Section 8), at a size Coq can evaluate
      directly by [reflexivity]. The 2-of-10 reviewed proportion is
      chosen for a clean [reflexivity] count, not to reproduce the
      paper's 200-of-10,000 (2%) reviewed rate. *)
  Inductive CAAssertion := Txn (n : nat).

  Inductive CAFact := ReviewedByAnalyst (n : nat).

  Definition cafeq (x y : CAFact) : bool :=
    match x, y with ReviewedByAnalyst n, ReviewedByAnalyst m => Nat.eqb n m end.

  Lemma cafeq_true_iff : forall x y, cafeq x y = true <-> x = y.
  Proof.
    intros [n] [m]; simpl; split; intro H.
    - f_equal. apply Nat.eqb_eq. exact H.
    - apply Nat.eqb_eq. congruence.
  Qed.

  Definition CAFactEq : EqbSpec CAFact := mkEqbSpec cafeq cafeq_true_iff.

  (** Each transaction gets its own single-precondition procedure,
      "reviewed by an analyst for this transaction", rather than one
      generic procedure shared across all ten: this keeps has_all
      honest about what was actually checked for which transaction. *)
  Definition proc_for (n : nat) : Procedure CAFact CAAssertion :=
    mkProcedure n "Human review" [ReviewedByAnalyst n]
      (fun a => match a with Txn m => Nat.eqb n m end).

  Definition boundary : BoundarySpec CAFact CAAssertion :=
    mkBoundarySpec 1 1 (map proc_for (seq 0 10)).

  (** Transactions 0 and 1 were reviewed; 2 through 9 were deprioritised
      by the thresholding layer, exactly as in Section 7.2's
      three-line algorithm. *)
  Definition observed_evidence : list CAFact := [ReviewedByAnalyst 0; ReviewedByAnalyst 1].

  Example txn0_verified : classify boundary CAFactEq observed_evidence (Txn 0) = Verified.
  Proof. reflexivity. Qed.

  Example txn1_verified : classify boundary CAFactEq observed_evidence (Txn 1) = Verified.
  Proof. reflexivity. Qed.

  Example txn5_undefined : classify boundary CAFactEq observed_evidence (Txn 5) = Undefined.
  Proof. reflexivity. Qed.

  (** The analyst proposes; a supervisor, a distinct registered
      identity, admits transactions 0 and 1 (the ones the boundary
      actually classifies Verified). Transactions 2 through 9 carry no
      certificate: nothing was reviewed for them to admit. *)
  Definition analyst : Process := mkProcess 0 Proposer.
  Definition supervisor : Process := mkProcess 1 Verifier.
  Definition ca_registry : ProcessRegistry := [analyst; supervisor].

  Definition ca_certificate (n : nat) : option AdmissionCertificate :=
    if Nat.eqb n 0 then Some (mkAdmissionCertificate 0 (process_id supervisor) true)
    else if Nat.eqb n 1 then Some (mkAdmissionCertificate 1 (process_id supervisor) true)
    else None.

  (** Proposal identity and proposer, not a complete proposal: see
      Pipeline.v's PipelineInput docstring for why -- [build_packet]
      constructs the proposal itself, from the real assertion and the
      real classify output, so there is no field here through which a
      mismatched assertion or classification could enter. *)
  Definition ca_input : PipelineInput CAFact CAAssertion :=
    mkPipelineInput boundary CAFactEq observed_evidence 0
      (map Txn (seq 0 10)) (fun _ => true)
      (fun a => match a with Txn n => n end)
      (fun _ => process_id analyst)
      (fun a => match a with Txn n => ca_certificate n end)
      ca_registry.

  Definition ca_decision : AuditDecision CAAssertion := run_pipeline ca_input 0 [].

  (** The disciplined algorithm of Section 7.2, made literal: every
      transaction that is not both Verified and admitted -- eight of
      the ten -- automatically writes a residual entry via
      [process_dependency]/[classify_and_register] (Residual.v); none
      of them silently vanishes into "no exception noted", and the
      opinion cannot be Unqualified while they remain (this is the same
      [decide_opinion] the Wirecard fixtures above exercise, not a
      separate check). *)
  Example eight_residuals_from_pipeline :
    List.length (decision_residuals ca_decision) = 8.
  Proof. reflexivity. Qed.

  Example ca_opinion_inadmissible :
    decision_opinion ca_decision <> Unqualified.
  Proof. unfold ca_decision. discriminate. Qed.

  Lemma ca_residual_states :
    map residual_state (decision_residuals ca_decision) =
    [Undefined; Undefined; Undefined; Undefined; Undefined; Undefined; Undefined; Undefined].
  Proof. reflexivity. Qed.

  Example no_residual_is_verified :
    forall e, In e (decision_residuals ca_decision) -> residual_state e <> Verified.
  Proof.
    intros e Hin Hcontra.
    assert (Hin' : In (residual_state e) (map residual_state (decision_residuals ca_decision)))
      by (apply in_map; exact Hin).
    rewrite ca_residual_states, Hcontra in Hin'.
    simpl in Hin'. intuition discriminate.
  Qed.

  (** Dashboard clearing is any permitted workflow transition, i.e. any
      [step]: it can only append, never remove. Applying
      [residual_preservation] to the pipeline's own output shows the
      eight residuals survive *any* such clearing, not merely the
      specific empty one -- there is no [Unreviewed] state to invoke
      here, only the append-only register already proved in
      Residual.v. *)
  Example dashboard_clearing_preserves_residuals :
    forall (cleared_log : RegisterLog CAAssertion),
      step (decision_residuals ca_decision) cleared_log ->
      forall e, In e (decision_residuals ca_decision) -> In e cleared_log.
  Proof.
    intros cleared_log Hstep e Hin.
    eapply residual_preservation; eauto.
  Qed.

End ContinuousAuditing.


Module SqlUnknown.

  (** A minimal model of the reporting-layer collapse from Section 7.3
      (STTT) / Section 2.3 of the AIS paper, now connected to the
      central pipeline rather than left as a standalone two-constructor
      toy: presence of a risk score is boundary evidence like any
      other, so absence classifies Undefined *by construction*, through
      the same [classify] every other fixture uses, and
      [pipeline_failed_material_dependency_blocks_unqualified]
      (Pipeline.v) is what rules out an absent score ever reaching
      Unqualified -- not a fact re-derived for this module specifically. *)

  Inductive SqlFact := ScoreIsPresent.
  Inductive SqlAssertion := RiskScoreAssertion.

  Definition sqlfeq (x y : SqlFact) : bool := match x, y with ScoreIsPresent, ScoreIsPresent => true end.

  Lemma sqlfeq_true_iff : forall x y, sqlfeq x y = true <-> x = y.
  Proof. intros [] []; simpl; split; intro H; [reflexivity | reflexivity]. Qed.

  Definition SqlFactEq : EqbSpec SqlFact := mkEqbSpec sqlfeq sqlfeq_true_iff.

  Definition score_procedure : Procedure SqlFact SqlAssertion :=
    mkProcedure 0 "Risk score present" [ScoreIsPresent] (fun _ => true).

  Definition sql_boundary : BoundarySpec SqlFact SqlAssertion :=
    mkBoundarySpec 2 1 [score_procedure].

  (** The adapter: a [option nat] risk score becomes boundary evidence
      -- [ScoreIsPresent] in the context iff the score is [Some _] --
      and the classification is whatever [classify] computes from
      that, never a numeric coercion. *)
  Definition context_for (r : option nat) : list SqlFact :=
    match r with
    | Some _ => [ScoreIsPresent]
    | None => []
    end.

  Definition nullable_score_to_classification (r : option nat) : EvidenceState :=
    classify sql_boundary SqlFactEq (context_for r) RiskScoreAssertion.

  (** Absence does not become numeric zero: it classifies Undefined,
      the same outcome any other absent evidence produces, and it
      remains distinguishable from an honestly-zero score, which
      classifies Verified because the score is present. *)
  Example absent_score_undefined :
    nullable_score_to_classification None = Undefined.
  Proof. reflexivity. Qed.

  Example honest_zero_verified :
    nullable_score_to_classification (Some 0) = Verified.
  Proof. reflexivity. Qed.

  Example absence_distinguishable_from_honest_zero :
    nullable_score_to_classification None <> nullable_score_to_classification (Some 0).
  Proof. discriminate. Qed.

  (** The downstream adapter cannot produce an admitted Verified
      assertion merely from absence: for *any* registry, proposal
      identity/proposer, and certificate a caller might supply -- not
      only the ones this module happens to construct -- a pipeline run
      over an absent score cannot decide Unqualified. This is
      [pipeline_failed_material_dependency_blocks_unqualified]
      (Pipeline.v) applied here, not a fact special to this fixture. *)
  Example absence_cannot_reach_unqualified :
    forall (registry : ProcessRegistry) (start_id : ResidualId) (log : RegisterLog SqlAssertion)
      (proposal_id_of : SqlAssertion -> ProposalId) (proposer_of : SqlAssertion -> ProcessId)
      (cert : SqlAssertion -> option AdmissionCertificate),
      let inp := mkPipelineInput sql_boundary SqlFactEq (context_for None) 0
                   [RiskScoreAssertion] (fun _ => true) proposal_id_of proposer_of cert registry in
      decision_opinion (run_pipeline inp start_id log) <> Unqualified.
  Proof.
    intros registry start_id log proposal_id_of proposer_of cert inp.
    unfold inp.
    eapply pipeline_failed_material_dependency_blocks_unqualified with (a := RiskScoreAssertion).
    - left. reflexivity.
    - reflexivity.
    - unfold dep_ok, build_packet. simpl. reflexivity.
  Qed.

  (** The pre-existing renderer illustration: two ways of turning a
      classification back into a downstream value, one that collapses
      Unknown into an honest zero and one that keeps them apart. This
      is about *rendering* a classification, the layer above the
      boundary machinery above; [nullable_score_to_classification]
      above is about *computing* it. *)
  Inductive RiskScore := Score (n : nat) | ScoreUnknown.

  Definition silently_converted_render (r : RiskScore) : nat :=
    match r with
    | Score n => n
    | ScoreUnknown => 0
    end.

  Inductive RenderedState := RNumeric (n : nat) | RUndefined.

  Definition disciplined_render (r : RiskScore) : RenderedState :=
    match r with
    | Score n => RNumeric n
    | ScoreUnknown => RUndefined
    end.

  Example silent_conversion_collides_with_honest_zero :
    silently_converted_render ScoreUnknown = silently_converted_render (Score 0).
  Proof. reflexivity. Qed.

  Example disciplined_render_distinguishes :
    disciplined_render ScoreUnknown <> disciplined_render (Score 0).
  Proof. discriminate. Qed.

End SqlUnknown.
