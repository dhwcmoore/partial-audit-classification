Require Import List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import PAC.Base.
Require Import PAC.Boundary.
Require Import PAC.SelfAdmission.
Require Import PAC.Admissibility.

(** Residual.v — the residual register: Residual Emission, Residual
    Preservation, and Orphan Escalation (STTT "Formal Sketch" / AIS
    Theorem 6.3). v0.1 combined emission and preservation into one
    theorem; v0.2 separates them, since they are different claims about
    different things:

    - Residual Emission ([nonadmitted_material_emits_residual] /
      [process_dependency]): every material dependency that is not
      [dep_ok] (Admissibility.v: classified Verified *and* validly
      admitted) automatically produces a matching residual entry. This
      is new in v0.2 -- v0.1 required a caller to construct residual
      entries by hand (see how Cases.v built [cleared_dashboard_log]
      before this commit); the emission is now a proved property of a
      function, not a convention Cases.v happened to follow.
    - Residual Preservation ([residual_preservation],
      [residual_preservation_chain]): once emitted, a residual entry is
      never removed or edited by [step], the register's only permitted
      transition. Carried over from v0.1 unchanged.
    - Orphan Escalation ([orphan_escalation_sound]): an entry with no
      declared owner is exactly what [orphaned_entries] returns. New in
      v0.2; v0.1 had the query and its preservation across [step] but
      not the soundness statement that ties the query to the property
      it is supposed to detect.

    v0.2 scope: this module does not model resolution or closure of a
    residual. [step] is still the only transition, and it is still
    purely additive; there is no [ResidualEvent] state machine, no
    resolution certificate, and no "current open view" distinct from
    the full history. That is a deliberate scope decision, not an
    oversight discovered later: the frozen v0.2 target in
    NON_CLAIMS.md commits to *emitting* a residual for every
    non-admitted material result, not to modelling how residuals are
    later closed. A dashboard-clearing operation is not representable
    as anything other than a [step] that appends whatever new entries
    the clearing workflow itself produces; it cannot remove existing
    ones, but this module does not yet distinguish "still open" from
    "closed" within the entries that remain. *)

Record ResidualEntry (Assertion : Type) := mkResidualEntry {
  residual_id              : ResidualId;
  residual_assertion       : Assertion;
  residual_state           : EvidenceState;
  residual_boundary_id     : BoundaryId;
  residual_boundary_version : nat;
  residual_context_id      : ContextId;
  residual_reason          : InadmissibilityReason Assertion;
  residual_owner           : option OwnerId  (* None marks an orphaned residual *)
}.
Arguments mkResidualEntry {Assertion} _ _ _ _ _ _ _ _.
Arguments residual_id {Assertion} _.
Arguments residual_assertion {Assertion} _.
Arguments residual_state {Assertion} _.
Arguments residual_boundary_id {Assertion} _.
Arguments residual_boundary_version {Assertion} _.
Arguments residual_context_id {Assertion} _.
Arguments residual_reason {Assertion} _.
Arguments residual_owner {Assertion} _.

Definition RegisterLog (Assertion : Type) := list (ResidualEntry Assertion).

Inductive step {Assertion : Type} : RegisterLog Assertion -> RegisterLog Assertion -> Prop :=
  | step_append : forall log new_entries, step log (new_entries ++ log).

Theorem residual_preservation :
  forall {Assertion : Type} (log1 log2 : RegisterLog Assertion) (e : ResidualEntry Assertion),
    step log1 log2 -> In e log1 -> In e log2.
Proof.
  intros Assertion log1 log2 e Hstep Hin.
  inversion Hstep as [log new_entries Heq]; subst.
  apply in_or_app; right; exact Hin.
Qed.

(** Preservation across any finite chain of steps, not merely a single
    one, since a real workflow clears many queues over time. *)
Inductive steps {Assertion : Type} : RegisterLog Assertion -> RegisterLog Assertion -> Prop :=
  | steps_refl  : forall log, steps log log
  | steps_trans : forall log1 log2 log3, step log1 log2 -> steps log2 log3 -> steps log1 log3.

Theorem residual_preservation_chain :
  forall {Assertion : Type} (log1 log2 : RegisterLog Assertion) (e : ResidualEntry Assertion),
    steps log1 log2 -> In e log1 -> In e log2.
Proof.
  intros Assertion log1 log2 e Hsteps.
  induction Hsteps as [log | log1' log2' log3' Hstep Hsteps' IH]; intro Hin.
  - exact Hin.
  - apply IH. eapply residual_preservation; eauto.
Qed.

(** An orphaned residual (no owner) is a first-class finding: this
    predicate is what an escalation check would decide over the
    register (Definition "Risk Assignment Register" / Principle "Risk
    Ownership"). *)
Definition is_orphaned {Assertion : Type} (e : ResidualEntry Assertion) : bool :=
  match residual_owner e with
  | None => true
  | Some _ => false
  end.

Definition orphaned_entries {Assertion : Type} (log : RegisterLog Assertion) : RegisterLog Assertion :=
  filter is_orphaned log.

Lemma orphaned_entries_preserved :
  forall {Assertion : Type} (log1 log2 : RegisterLog Assertion) (e : ResidualEntry Assertion),
    step log1 log2 -> In e (orphaned_entries log1) -> In e (orphaned_entries log2).
Proof.
  intros Assertion log1 log2 e Hstep Hin.
  unfold orphaned_entries in *.
  apply filter_In in Hin as [Hin Horph].
  apply filter_In; split; [eapply residual_preservation; eauto | exact Horph].
Qed.

(** Orphan Escalation: the query is sound, not merely preserved -- an
    entry that is actually ownerless is exactly one the query returns.
    ([orphaned_entries_preserved] above says a *found* orphan stays
    found; this says the query finds every orphan there is.) *)
Theorem orphan_escalation_sound :
  forall {Assertion : Type} (log : RegisterLog Assertion) (e : ResidualEntry Assertion),
    In e log -> residual_owner e = None -> In e (orphaned_entries log).
Proof.
  intros Assertion log e Hin Hnone.
  unfold orphaned_entries. apply filter_In. split.
  - exact Hin.
  - unfold is_orphaned. rewrite Hnone. reflexivity.
Qed.

(** ** Residual Emission

    [process_dependency] is the automatic-emission function: given the
    declared boundary's identity and version, the evidence context's
    identity, a fresh residual identifier, and a [DependencyPacket]
    (Admissibility.v), it returns the dependency's classification
    together with a residual entry exactly when the dependency is
    material and not [dep_ok] -- not both Verified and validly
    admitted. The owner field is left unassigned ([None]) at emission
    time: this function only emits, it does not itself assign risk
    ownership.

    v0.2 review finding: an earlier version emitted for *every*
    dependency failing [dep_ok], regardless of [dep_material], which
    is broader than the STTT/AIS manuscripts' and NON_CLAIMS.md's
    stated claim ("every material dependency..."); a non-material
    failing dependency would have produced a residual with no
    corresponding promise anywhere that it should. Emission is now
    explicitly gated on materiality, matching the documented claim
    exactly rather than a superset of it, with
    [nonmaterial_emits_no_residual] below stating the excluded case
    directly. *)
Definition process_dependency {Assertion : Type}
    (registry : ProcessRegistry) (bid : BoundaryId) (bver : nat) (cid : ContextId)
    (rid : ResidualId) (d : DependencyPacket Assertion)
    : EvidenceState * option (ResidualEntry Assertion) :=
  if dep_material d && negb (dep_ok registry d)
  then (dep_state d,
        Some (mkResidualEntry rid (dep_assertion d) (dep_state d) bid bver cid (reason_for d) None))
  else (dep_state d, None).

Theorem nonadmitted_material_emits_residual :
  forall {Assertion : Type} (registry : ProcessRegistry) (bid : BoundaryId) (bver : nat)
    (cid : ContextId) (rid : ResidualId) (d : DependencyPacket Assertion),
    dep_material d = true -> dep_ok registry d = false ->
    exists e, snd (process_dependency registry bid bver cid rid d) = Some e /\
              residual_assertion e = dep_assertion d /\ residual_state e = dep_state d.
Proof.
  intros Assertion registry bid bver cid rid d Hmat Hnok.
  unfold process_dependency. rewrite Hmat, Hnok.
  eexists. repeat split.
Qed.

Theorem admitted_verified_emits_no_open_residual :
  forall {Assertion : Type} (registry : ProcessRegistry) (bid : BoundaryId) (bver : nat)
    (cid : ContextId) (rid : ResidualId) (d : DependencyPacket Assertion),
    dep_ok registry d = true ->
    snd (process_dependency registry bid bver cid rid d) = None.
Proof.
  intros Assertion registry bid bver cid rid d Hok.
  unfold process_dependency. rewrite Hok.
  destruct (dep_material d); reflexivity.
Qed.

Theorem nonmaterial_emits_no_residual :
  forall {Assertion : Type} (registry : ProcessRegistry) (bid : BoundaryId) (bver : nat)
    (cid : ContextId) (rid : ResidualId) (d : DependencyPacket Assertion),
    dep_material d = false ->
    snd (process_dependency registry bid bver cid rid d) = None.
Proof.
  intros Assertion registry bid bver cid rid d Hmat.
  unfold process_dependency. rewrite Hmat. reflexivity.
Qed.

(** [classify_and_register] folds [process_dependency] over a list of
    dependencies, handing out increasing residual identifiers and
    threading a [RegisterLog]: every emitted entry is prepended, so the
    resulting log extends the input log exactly as [step] permits (see
    [classify_and_register_step] below). *)
Fixpoint classify_and_register {Assertion : Type}
    (registry : ProcessRegistry) (bid : BoundaryId) (bver : nat) (cid : ContextId)
    (next_id : ResidualId) (deps : list (DependencyPacket Assertion)) (log : RegisterLog Assertion)
    : list EvidenceState * RegisterLog Assertion :=
  match deps with
  | [] => ([], log)
  | d :: rest =>
      match process_dependency registry bid bver cid next_id d with
      | (s, Some e) =>
          let '(states, log') := classify_and_register registry bid bver cid (S next_id) rest (e :: log) in
          (s :: states, log')
      | (s, None) =>
          let '(states, log') := classify_and_register registry bid bver cid next_id rest log in
          (s :: states, log')
      end
  end.

Theorem classify_and_register_step :
  forall {Assertion : Type} (registry : ProcessRegistry) (bid : BoundaryId) (bver : nat)
    (cid : ContextId) (next_id : ResidualId) (deps : list (DependencyPacket Assertion))
    (log : RegisterLog Assertion),
    steps log (snd (classify_and_register registry bid bver cid next_id deps log)).
Proof.
  intros Assertion registry bid bver cid next_id deps.
  revert next_id.
  induction deps as [| d rest IH]; intro next_id; simpl; intro log.
  - apply steps_refl.
  - destruct (process_dependency registry bid bver cid next_id d) as [s [e |]] eqn:Hpd.
    + destruct (classify_and_register registry bid bver cid (S next_id) rest (e :: log))
        as [states log'] eqn:Hrec.
      simpl.
      eapply steps_trans.
      * exact (step_append log [e]).
      * specialize (IH (S next_id) (e :: log)). rewrite Hrec in IH. exact IH.
    + destruct (classify_and_register registry bid bver cid next_id rest log)
        as [states log'] eqn:Hrec.
      simpl.
      specialize (IH next_id log). rewrite Hrec in IH. exact IH.
Qed.

(** The theorem [pipeline_residual_implies_not_unqualified_witness]
    (Pipeline.v) is named for a residual-to-decision relationship it
    did not originally state -- its hypothesis was [dep_ok = false],
    with no reference to [decision_residuals] at all. This theorem is
    what actually earns that name: a specific material, failing
    dependency's emitted entry is not merely blocked from
    [Unqualified] (that much follows from [decide_opinion_blocked]
    alone) but demonstrably present in [classify_and_register]'s
    output log, wherever in the dependency list it occurs. *)
Theorem classify_and_register_emits_for_dependency :
  forall {Assertion : Type} (registry : ProcessRegistry) (bid : BoundaryId) (bver : nat)
    (cid : ContextId) (next_id : ResidualId) (deps : list (DependencyPacket Assertion))
    (d : DependencyPacket Assertion),
    In d deps -> dep_material d = true -> dep_ok registry d = false ->
    forall log : RegisterLog Assertion,
      exists e, residual_assertion e = dep_assertion d /\ residual_state e = dep_state d /\
                In e (snd (classify_and_register registry bid bver cid next_id deps log)).
Proof.
  intros Assertion registry bid bver cid next_id deps.
  revert next_id.
  induction deps as [| d0 rest IH]; intros next_id d Hin Hmat Hnok log.
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst d0.
      simpl.
      unfold process_dependency at 1.
      rewrite Hmat, Hnok.
      simpl.
      set (e0 := mkResidualEntry next_id (dep_assertion d) (dep_state d) bid bver cid (reason_for d) None).
      destruct (classify_and_register registry bid bver cid (S next_id) rest (e0 :: log))
        as [states log'] eqn:Hrec.
      simpl.
      exists e0.
      split; [reflexivity |]. split; [reflexivity |].
      eapply residual_preservation_chain.
      * pose proof (classify_and_register_step registry bid bver cid (S next_id) rest (e0 :: log)) as Hsteps.
        rewrite Hrec in Hsteps. simpl in Hsteps. exact Hsteps.
      * left. reflexivity.
    + simpl.
      destruct (process_dependency registry bid bver cid next_id d0) as [s [e |]] eqn:Hpd.
      * destruct (classify_and_register registry bid bver cid (S next_id) rest (e :: log))
          as [states log'] eqn:Hrec.
        simpl.
        destruct (IH (S next_id) d Hin Hmat Hnok (e :: log)) as [w [Hw1 [Hw2 Hw3]]].
        exists w. repeat split; try assumption.
        rewrite Hrec in Hw3. exact Hw3.
      * destruct (classify_and_register registry bid bver cid next_id rest log)
          as [states log'] eqn:Hrec.
        simpl.
        destruct (IH next_id d Hin Hmat Hnok log) as [w [Hw1 [Hw2 Hw3]]].
        exists w. repeat split; try assumption.
        rewrite Hrec in Hw3. exact Hw3.
Qed.
