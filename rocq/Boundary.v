Require Import List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import PAC.Base.

(** Boundary.v — verification boundaries and preconditions (Section 4 of
    the STTT paper; Section 5.1-5.2 of the AIS paper). A [Procedure] is
    a verification method with an explicit precondition list and an
    assertion class it covers. A [BoundarySpec] is a declared list of
    such procedures. [boundary_state] computes the mechanical
    Verified/Undefined branch of the state function from a boundary
    specification and an evidence context: it is deliberately not
    primitive, exactly as both papers require ("the state function is
    not primitive: its value is computed from the declared boundary
    specification"). The remaining four states (Refuted, the two
    presumptive states, and EscalationRequired) are assigned by separate
    judgments, not by boundary evaluation; see Cases.v for worked
    instances of the Verified/Undefined branch, and NON_CLAIMS.md for
    what this development does not attempt to formalise about the other
    four. *)

Fixpoint has_fact {Fact : Type} (feq : Fact -> Fact -> bool) (ctx : list Fact) (f : Fact) : bool :=
  match ctx with
  | [] => false
  | g :: rest => if feq f g then true else has_fact feq rest f
  end.

Fixpoint has_all {Fact : Type} (feq : Fact -> Fact -> bool) (ctx : list Fact) (needed : list Fact) : bool :=
  match needed with
  | [] => true
  | f :: rest => has_fact feq ctx f && has_all feq ctx rest
  end.

Record Procedure (Fact Assertion : Type) := mkProcedure {
  proc_name          : string;
  proc_preconditions : list Fact;
  proc_covers        : Assertion -> bool
}.

Arguments mkProcedure {Fact Assertion} _ _ _.
Arguments proc_name {Fact Assertion} _.
Arguments proc_preconditions {Fact Assertion} _.
Arguments proc_covers {Fact Assertion} _ _.

Definition BoundarySpec (Fact Assertion : Type) := list (Procedure Fact Assertion).

Fixpoint procedure_satisfied {Fact Assertion : Type}
    (feq : Fact -> Fact -> bool) (ctx : list Fact) (a : Assertion)
    (bspec : BoundarySpec Fact Assertion) : bool :=
  match bspec with
  | [] => false
  | p :: rest =>
      if proc_covers p a && has_all feq ctx (proc_preconditions p)
      then true
      else procedure_satisfied feq ctx a rest
  end.

(** The only two outcomes a boundary specification can mechanically
    produce. This is Section 5's "an assertion for which no declared
    procedure's preconditions hold is classified Undefined by
    construction," made literal: there is no third branch here for the
    function to take. *)
Definition boundary_state {Fact Assertion : Type}
    (feq : Fact -> Fact -> bool) (ctx : list Fact) (a : Assertion)
    (bspec : BoundarySpec Fact Assertion) : EvidenceState :=
  if procedure_satisfied feq ctx a bspec then Verified else Undefined.

Lemma boundary_state_verified_iff :
  forall {Fact Assertion : Type} (feq : Fact -> Fact -> bool) (ctx : list Fact)
    (a : Assertion) (bspec : BoundarySpec Fact Assertion),
    boundary_state feq ctx a bspec = Verified <-> procedure_satisfied feq ctx a bspec = true.
Proof.
  intros. unfold boundary_state.
  destruct (procedure_satisfied feq ctx a bspec); split; congruence.
Qed.

Lemma boundary_state_undefined_iff :
  forall {Fact Assertion : Type} (feq : Fact -> Fact -> bool) (ctx : list Fact)
    (a : Assertion) (bspec : BoundarySpec Fact Assertion),
    boundary_state feq ctx a bspec = Undefined <-> procedure_satisfied feq ctx a bspec = false.
Proof.
  intros. unfold boundary_state.
  destruct (procedure_satisfied feq ctx a bspec); split; congruence.
Qed.

(** Adding evidence never turns a satisfied procedure unsatisfied: the
    boundary specification is monotone in the context. This is the
    structural fact behind the papers' claim that the classification
    logic never needs to retract a Verified result once earned (v0.1
    scope: no revocation of facts is modelled). *)
Lemma has_fact_monotone {Fact : Type} (feq : Fact -> Fact -> bool) :
  (forall x y, feq x y = true -> x = y) ->
  (forall x, feq x x = true) ->
  forall (extra ctx : list Fact) (f : Fact),
    has_fact feq ctx f = true -> has_fact feq (extra ++ ctx) f = true.
Proof.
  intros _ Hrefl extra ctx f Hin.
  induction extra as [| e rest IH]; simpl.
  - exact Hin.
  - destruct (feq f e) eqn:E.
    + reflexivity.
    + exact IH.
Qed.
