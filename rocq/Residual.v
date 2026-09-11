Require Import List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import PAC.Base.

(** Residual.v — the residual register and Theorem 2 (Residual
    Preservation): "Every non-affirmative classification of a material
    assertion writes an entry to the residual register, and no workflow
    operation deletes or downgrades an entry" (STTT Theorem 4.2 /
    AIS Theorem 6.3).

    The register is modelled as a list, and [step] is its only
    permitted transition: strictly additive. There is deliberately no
    constructor that removes or edits an existing entry, which is what
    makes [residual_preservation] a monotonicity property rather than
    an operational promise that some external process happens to keep. *)

Record ResidualEntry (Assertion : Type) := mkResidualEntry {
  residual_assertion : Assertion;
  residual_state     : EvidenceState;
  residual_owner     : option string  (* None marks an orphaned residual *)
}.
Arguments mkResidualEntry {Assertion} _ _ _.
Arguments residual_assertion {Assertion} _.
Arguments residual_state {Assertion} _.
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
