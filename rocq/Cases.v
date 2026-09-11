Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import PAC.Base.
Require Import PAC.Boundary.
Require Import PAC.Admissibility.
Require Import PAC.Residual.

(** Cases.v — the three worked examples from Section 6 (STTT) / Sections
    7-8 (AIS): Wirecard as a classification trace, continuous auditing
    exception queues, and the SQL Unknown collapse. These are the
    "finite instances exercised" referred to in the STTT paper's Remark
    on "machine-checked sketch": concrete instantiations of the generic
    development in Admissibility.v and Residual.v, not a claim that
    every possible boundary specification or workflow has been
    enumerated. See NON_CLAIMS.md. *)

Module Wirecard.

  (** The five preconditions of "direct bank confirmation" (Section 4's
      running example / the Wirecard trace of Section 6.1 and Section
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

  Inductive WAssertion := CashExistencePhilippineTrustee.

  Definition direct_bank_confirmation : Procedure WFact WAssertion :=
    mkProcedure "Direct bank confirmation"
      [BankExistsIndependent; ConfirmationRouteControlledByAuditor;
       JurisdictionPermitsDirectConfirmation; AccountIdentifierSupplied;
       AuthenticatedChannel]
      (fun _ => true).

  Definition boundary : BoundarySpec WFact WAssertion := [direct_bank_confirmation].

  (** Observed evidence per Section 6.1: an independent bank exists and
      an account identifier was supplied, but the confirmation route was
      not controlled by the auditor, the jurisdiction did not permit
      direct confirmation, and no authenticated channel was used. Three
      of five preconditions fail. *)
  Definition observed_evidence : list WFact :=
    [BankExistsIndependent; AccountIdentifierSupplied].

  Example wirecard_state_undefined :
    boundary_state wfeq observed_evidence CashExistencePhilippineTrustee boundary = Undefined.
  Proof. reflexivity. Qed.

  Definition material_all (_ : WAssertion) : bool := true.
  Definition no_admissions (_ : WAssertion) : Prop := False.

  Definition wirecard_opinion : Opinion WAssertion := mkOpinion [CashExistencePhilippineTrustee].

  Example wirecard_opinion_inadmissible :
    ~ OpinionAdmissible wfeq material_all no_admissions observed_evidence boundary wirecard_opinion.
  Proof.
    eapply contrapositive_inadmissible with (a := CashExistencePhilippineTrustee).
    - simpl. left. reflexivity.
    - reflexivity.
    - exact wirecard_state_undefined.
  Qed.

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
    boundary_state wfeq full_evidence CashExistencePhilippineTrustee boundary = Verified.
  Proof. reflexivity. Qed.

End Wirecard.


Module ContinuousAuditing.

  (** Ten transactions stand in for the paper's 10,000-transaction
      example (Section 6.2 / Section 8); the 2-reviewed-of-10
      proportion mirrors the paper's 200-of-10,000 ratio at a size Coq
      can evaluate directly by [reflexivity]. *)
  Inductive CAAssertion := Txn (n : nat).

  Inductive CAFact := ReviewedByAnalyst (n : nat).

  Definition cafeq (x y : CAFact) : bool :=
    match x, y with ReviewedByAnalyst n, ReviewedByAnalyst m => Nat.eqb n m end.

  (** Each transaction gets its own single-precondition procedure,
      "reviewed by an analyst for this transaction", rather than one
      generic procedure shared across all ten: this keeps has_all
      honest about what was actually checked for which transaction. *)
  Definition proc_for (n : nat) : Procedure CAFact CAAssertion :=
    mkProcedure "Human review" [ReviewedByAnalyst n]
      (fun a => match a with Txn m => Nat.eqb n m end).

  Definition boundary : BoundarySpec CAFact CAAssertion := map proc_for (seq 0 10).

  (** Transactions 0 and 1 were reviewed; 2 through 9 were deprioritised
      by the thresholding layer, exactly as in Section 6.2's
      three-line algorithm. *)
  Definition observed_evidence : list CAFact := [ReviewedByAnalyst 0; ReviewedByAnalyst 1].

  Example txn0_verified : boundary_state cafeq observed_evidence (Txn 0) boundary = Verified.
  Proof. reflexivity. Qed.

  Example txn1_verified : boundary_state cafeq observed_evidence (Txn 1) boundary = Verified.
  Proof. reflexivity. Qed.

  Example txn5_undefined : boundary_state cafeq observed_evidence (Txn 5) boundary = Undefined.
  Proof. reflexivity. Qed.

  (** The disciplined algorithm of Section 6.2: every non-Verified
      transaction writes a residual entry. This is
      [state(e) := Unreviewed; residual_register.add(e)] made concrete;
      the governing inequality "Unreviewed != Accepted" is
      [no_residual_is_verified] below. *)
  Definition undefined_txns : list nat :=
    filter (fun n => match boundary_state cafeq observed_evidence (Txn n) boundary with
                      | Verified => false
                      | _ => true
                      end)
           (seq 0 10).

  Definition cleared_dashboard_log : RegisterLog CAAssertion :=
    map (fun n => mkResidualEntry (Txn n)
                    (boundary_state cafeq observed_evidence (Txn n) boundary) None)
        undefined_txns.

  (** Eight of the ten transactions survive dashboard clearing as
      residuals; none of them silently vanishes into "no exception
      noted". *)
  Example eight_residuals_survive_clearing :
    List.length cleared_dashboard_log = 8.
  Proof. reflexivity. Qed.

  Example no_residual_is_verified :
    forall e, In e cleared_dashboard_log -> residual_state e <> Verified.
  Proof.
    intros e Hin Hcontra.
    unfold cleared_dashboard_log, undefined_txns in Hin.
    apply in_map_iff in Hin as [n [Heq Hin2]].
    apply filter_In in Hin2 as [_ Hcond].
    subst e.
    simpl in Hcontra.
    rewrite Hcontra in Hcond.
    simpl in Hcond.
    discriminate.
  Qed.

End ContinuousAuditing.


Module SqlUnknown.

  (** A minimal model of the reporting-layer collapse from Section 6.3
      (STTT) / Section 5.3 of the AIS paper: a risk score that is either
      a concrete value or Unknown, and two candidate ways of rendering
      it downstream. This is deliberately not a model of SQL's
      three-valued logic itself (Codd 1979 already supplies that at the
      data layer); it models what happens one layer up, where the
      papers locate the actual failure. *)

  Inductive RiskScore := Score (n : nat) | ScoreUnknown.

  (** The undisciplined collapse: Unknown is rendered as zero, exactly
      the "null risk score rendered as zero" example in both papers. *)
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

  (** The undisciplined renderer makes an honestly-zero score
      indistinguishable from Unknown: a downstream reader cannot tell
      "no risk" from "we don't know". *)
  Example silent_conversion_collides_with_honest_zero :
    silently_converted_render ScoreUnknown = silently_converted_render (Score 0).
  Proof. reflexivity. Qed.

  (** The disciplined renderer keeps them apart by construction. *)
  Example disciplined_render_distinguishes :
    disciplined_render ScoreUnknown <> disciplined_render (Score 0).
  Proof. discriminate. Qed.

End SqlUnknown.
