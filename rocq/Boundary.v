Require Import List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import PAC.Base.

(** Boundary.v — verification boundaries and preconditions (Section 4 of
    the STTT paper; Section 6.1-6.2 of the AIS paper). A [Procedure] is
    a verification method with an explicit precondition list, an
    assertion class it covers, and a stable identity. A [BoundarySpec]
    is a declared, versioned, identified list of such procedures.
    [classify] computes the mechanical Verified/Undefined branch of the
    state function from a boundary specification and an evidence
    context: it is deliberately not primitive, exactly as both papers
    require ("the state function is not primitive: its value is
    computed from the declared boundary specification"). The remaining
    four states (Refuted, the two presumptive states, and
    EscalationRequired) are assigned by separate judgments, not by
    boundary evaluation; see Cases.v for worked instances of the
    Verified/Undefined branch, and NON_CLAIMS.md for what this
    development does not attempt to formalise about the other four.

    v0.2 change from v0.1: the caller no longer supplies a bare
    [Fact -> Fact -> bool] equality test. [EqbSpec] carries the
    correctness proof that test would otherwise be trusted to satisfy,
    so a defective or malicious equality test (one that returns [true]
    for every pair) can no longer be passed in and silently make every
    precondition appear satisfied: it must instead be proved to decide
    equality. [Procedure] and [BoundarySpec] additionally carry stable
    identifiers ([ProcedureId], [BoundaryId]) and a version number,
    rather than relying on list position as identity. *)

(** A decidable-equality witness, carried with its own correctness
    proof rather than trusted by convention. [eqb_true_iff] rules out
    an equality test that is unsound (claims two different facts are
    equal) or incomplete (fails to recognise two equal facts); both
    would otherwise let a caller manufacture or hide precondition
    satisfaction. *)
Record EqbSpec (A : Type) := mkEqbSpec {
  eqb          : A -> A -> bool;
  eqb_true_iff : forall x y, eqb x y = true <-> x = y
}.
Arguments mkEqbSpec {A} _ _.
Arguments eqb {A} _ _ _.
Arguments eqb_true_iff {A} _ _ _.

Lemma eqb_refl {A : Type} (E : EqbSpec A) : forall x, eqb E x x = true.
Proof. intro x. apply (eqb_true_iff E). reflexivity. Qed.

Fixpoint has_fact {Fact : Type} (E : EqbSpec Fact) (ctx : list Fact) (f : Fact) : bool :=
  match ctx with
  | [] => false
  | g :: rest => if eqb E f g then true else has_fact E rest f
  end.

Fixpoint has_all {Fact : Type} (E : EqbSpec Fact) (ctx : list Fact) (needed : list Fact) : bool :=
  match needed with
  | [] => true
  | f :: rest => has_fact E ctx f && has_all E ctx rest
  end.

(** A verification procedure: a stable identity, a human-readable name,
    the preconditions it requires, and the assertion class it covers.
    (v0.2 keeps this to the mechanical Verified/Undefined branch; it
    does not carry a declared evidentiary strength or finding type --
    see the v0.2 scope note in NON_CLAIMS.md for why that generalisation
    is left unmechanised rather than added and under-proved.) *)
Record Procedure (Fact Assertion : Type) := mkProcedure {
  procedure_id            : ProcedureId;
  procedure_name          : string;
  procedure_preconditions : list Fact;
  procedure_covers        : Assertion -> bool
}.

Arguments mkProcedure {Fact Assertion} _ _ _ _.
Arguments procedure_id {Fact Assertion} _.
Arguments procedure_name {Fact Assertion} _.
Arguments procedure_preconditions {Fact Assertion} _.
Arguments procedure_covers {Fact Assertion} _ _.

(** A boundary specification: an identified, versioned, declared list of
    procedures. The identifier and version exist so that a residual
    entry (Residual.v) can record *which* declared boundary, at *which*
    version, produced a classification, rather than only the outcome. *)
Record BoundarySpec (Fact Assertion : Type) := mkBoundarySpec {
  boundary_id         : BoundaryId;
  boundary_version     : nat;
  boundary_procedures  : list (Procedure Fact Assertion)
}.

Arguments mkBoundarySpec {Fact Assertion} _ _ _.
Arguments boundary_id {Fact Assertion} _.
Arguments boundary_version {Fact Assertion} _.
Arguments boundary_procedures {Fact Assertion} _.

Fixpoint procedure_satisfied {Fact Assertion : Type}
    (E : EqbSpec Fact) (ctx : list Fact) (a : Assertion)
    (procs : list (Procedure Fact Assertion)) : bool :=
  match procs with
  | [] => false
  | p :: rest =>
      if procedure_covers p a && has_all E ctx (procedure_preconditions p)
      then true
      else procedure_satisfied E ctx a rest
  end.

(** The only two outcomes a boundary specification can mechanically
    produce. This is Section 4's "an assertion for which no declared
    procedure's preconditions hold is classified Undefined by
    construction," made literal: there is no third branch here for the
    function to take. (v0.2 renames [boundary_state] to [classify] and
    reorders its arguments to [BoundarySpec] then [EqbSpec] then context
    then assertion is *not* the chosen order -- see below -- matching
    the natural reading "classify this boundary spec, in this context,
    for this assertion.") *)
Definition classify {Fact Assertion : Type}
    (bspec : BoundarySpec Fact Assertion) (E : EqbSpec Fact)
    (ctx : list Fact) (a : Assertion) : EvidenceState :=
  if procedure_satisfied E ctx a (boundary_procedures bspec) then Verified else Undefined.

Lemma classify_verified_iff :
  forall {Fact Assertion : Type} (bspec : BoundarySpec Fact Assertion)
    (E : EqbSpec Fact) (ctx : list Fact) (a : Assertion),
    classify bspec E ctx a = Verified <->
    procedure_satisfied E ctx a (boundary_procedures bspec) = true.
Proof.
  intros. unfold classify.
  destruct (procedure_satisfied E ctx a (boundary_procedures bspec)); split; congruence.
Qed.

Lemma classify_undefined_iff :
  forall {Fact Assertion : Type} (bspec : BoundarySpec Fact Assertion)
    (E : EqbSpec Fact) (ctx : list Fact) (a : Assertion),
    classify bspec E ctx a = Undefined <->
    procedure_satisfied E ctx a (boundary_procedures bspec) = false.
Proof.
  intros. unfold classify.
  destruct (procedure_satisfied E ctx a (boundary_procedures bspec)); split; congruence.
Qed.

(** ** Soundness and completeness: a [Verified] outcome has a witness

    These are the "substantive boundary theorems" the v0.1 development
    lacked: [classify_verified_iff] only unfolds the Boolean branch, it
    does not say *why* the branch was taken. The theorems below say
    that [procedure_satisfied]/[classify] returning [true]/[Verified]
    is equivalent to a concrete witnessing procedure existing in the
    supplied specification -- one that both covers the assertion and
    has every declared precondition present in the evidence context --
    not merely that some Boolean computation happened to return [true]. *)

Theorem procedure_satisfied_sound :
  forall {Fact Assertion : Type} (E : EqbSpec Fact) (ctx : list Fact)
    (a : Assertion) (procs : list (Procedure Fact Assertion)),
    procedure_satisfied E ctx a procs = true ->
    exists p, In p procs /\ procedure_covers p a = true /\
              has_all E ctx (procedure_preconditions p) = true.
Proof.
  intros Fact Assertion E ctx a procs.
  induction procs as [| q rest IH]; simpl; intro H.
  - discriminate.
  - destruct (procedure_covers q a && has_all E ctx (procedure_preconditions q)) eqn:Hq.
    + apply andb_true_iff in Hq as [Hcov Hall].
      exists q. split; [left; reflexivity | split; assumption].
    + destruct (IH H) as [p [Hin [Hcov Hall]]].
      exists p. split; [right; exact Hin | split; assumption].
Qed.

Theorem procedure_satisfied_complete :
  forall {Fact Assertion : Type} (E : EqbSpec Fact) (ctx : list Fact)
    (a : Assertion) (procs : list (Procedure Fact Assertion)) (p : Procedure Fact Assertion),
    In p procs -> procedure_covers p a = true ->
    has_all E ctx (procedure_preconditions p) = true ->
    procedure_satisfied E ctx a procs = true.
Proof.
  intros Fact Assertion E ctx a procs p.
  induction procs as [| q rest IH]; simpl; intros Hin Hcov Hall.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst q. rewrite Hcov, Hall. reflexivity.
    + destruct (procedure_covers q a && has_all E ctx (procedure_preconditions q)).
      * reflexivity.
      * exact (IH Hin Hcov Hall).
Qed.

Theorem boundary_verified_has_witness :
  forall {Fact Assertion : Type} (bspec : BoundarySpec Fact Assertion)
    (E : EqbSpec Fact) (ctx : list Fact) (a : Assertion),
    classify bspec E ctx a = Verified ->
    exists p, In p (boundary_procedures bspec) /\ procedure_covers p a = true /\
              has_all E ctx (procedure_preconditions p) = true.
Proof.
  intros. apply procedure_satisfied_sound. apply classify_verified_iff. assumption.
Qed.

Theorem boundary_undefined_no_witness :
  forall {Fact Assertion : Type} (bspec : BoundarySpec Fact Assertion)
    (E : EqbSpec Fact) (ctx : list Fact) (a : Assertion),
    classify bspec E ctx a = Undefined ->
    forall p, In p (boundary_procedures bspec) -> procedure_covers p a = true ->
      has_all E ctx (procedure_preconditions p) = false.
Proof.
  intros Fact Assertion bspec E ctx a Hundef p Hin Hcov.
  destruct (has_all E ctx (procedure_preconditions p)) eqn:Hall; [| reflexivity].
  assert (Hsat : procedure_satisfied E ctx a (boundary_procedures bspec) = true)
    by (eapply procedure_satisfied_complete; eauto).
  apply classify_undefined_iff in Hundef. congruence.
Qed.

(** ** Monotonicity: adding evidence never loses a satisfied procedure

    Adding facts never turns a satisfied procedure unsatisfied, nor a
    [Verified] classification into an [Undefined] one: the boundary
    specification is monotone in the context. This is the structural
    fact behind the papers' claim that the classification logic never
    needs to retract a Verified result once earned (v0.2 scope: no
    revocation of facts is modelled). *)

Lemma has_fact_monotone {Fact : Type} (E : EqbSpec Fact) :
  forall (extra ctx : list Fact) (f : Fact),
    has_fact E ctx f = true -> has_fact E (extra ++ ctx) f = true.
Proof.
  intros extra ctx f Hin.
  induction extra as [| e rest IH]; simpl.
  - exact Hin.
  - destruct (eqb E f e) eqn:Ef.
    + reflexivity.
    + exact IH.
Qed.

Lemma has_all_monotone {Fact : Type} (E : EqbSpec Fact) :
  forall (extra ctx needed : list Fact),
    has_all E ctx needed = true -> has_all E (extra ++ ctx) needed = true.
Proof.
  intros extra ctx needed.
  induction needed as [| f rest IH]; simpl; intro H.
  - reflexivity.
  - apply andb_true_iff in H as [Hf Hrest].
    rewrite (has_fact_monotone E extra ctx f Hf), (IH Hrest). reflexivity.
Qed.

Theorem procedure_satisfied_context_monotone :
  forall {Fact Assertion : Type} (E : EqbSpec Fact) (extra ctx : list Fact)
    (a : Assertion) (procs : list (Procedure Fact Assertion)),
    procedure_satisfied E ctx a procs = true ->
    procedure_satisfied E (extra ++ ctx) a procs = true.
Proof.
  intros Fact Assertion E extra ctx a procs.
  induction procs as [| q rest IH]; simpl; intro H.
  - discriminate.
  - destruct (procedure_covers q a && has_all E ctx (procedure_preconditions q)) eqn:Hq.
    + apply andb_true_iff in Hq as [Hcov Hall].
      rewrite Hcov, (has_all_monotone E extra ctx _ Hall). reflexivity.
    + destruct (procedure_covers q a && has_all E (extra ++ ctx) (procedure_preconditions q)).
      * reflexivity.
      * exact (IH H).
Qed.

Theorem boundary_verified_context_monotone :
  forall {Fact Assertion : Type} (bspec : BoundarySpec Fact Assertion)
    (E : EqbSpec Fact) (extra ctx : list Fact) (a : Assertion),
    classify bspec E ctx a = Verified ->
    classify bspec E (extra ++ ctx) a = Verified.
Proof.
  intros Fact Assertion bspec E extra ctx a H.
  apply classify_verified_iff.
  apply procedure_satisfied_context_monotone.
  apply classify_verified_iff. assumption.
Qed.
