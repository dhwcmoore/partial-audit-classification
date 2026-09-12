Require Import List.
Import ListNotations.
Require Import PAC.Base.
Require Import PAC.Boundary.

(** Admissibility.v — the Admissibility definition (Section 3) and
    Theorem 1 (Default-Free Admissibility) with its Corollary (Contrapositive),
    stated identically in both papers ("For any audit opinion O, if O is
    unqualified, then every material assertion on which O depends is
    classified Verified under the declared boundary specification and
    admitted by an independent verifier").

    [OpinionAdmissible] is not a separate postulate: it *is* the
    definition of what "admissible as an unqualified opinion" means, so
    [default_free_admissibility] is a direct unfolding of that
    definition. That is deliberate and is the whole point of the
    papers' claim that the type error is "unrepresentable" rather than
    merely discouraged: there is no other constructor in this
    development for "an opinion is admissible as unqualified" that
    bypasses the per-assertion check. The non-trivial content is in the
    Corollary, which is what a reviewer would actually want to see: a
    single Undefined material dependency is enough to rule out
    admissibility, however many other dependencies are Verified.

    v0.2 status: this module is carried over from v0.1 with only the
    mechanical updates needed to compile against the v0.2 [Boundary.v]
    API ([EqbSpec] instead of a bare equality function; [classify]
    instead of [boundary_state]). [independently_admitted] here is
    still the abstract, caller-supplied predicate from v0.1. The
    certificate-based replacement for it -- [valid_admission] against a
    [ProcessRegistry], with [decide_opinion] as the executable decision
    procedure this predicate only specifies -- is added in
    Pipeline.v/SelfAdmission.v; [default_free_admissibility] below
    remains a valid, but no longer central, specification lemma once
    that lands. See NON_CLAIMS.md. *)

Record Opinion (Assertion : Type) := mkOpinion { op_deps : list Assertion }.
Arguments mkOpinion {Assertion} _.
Arguments op_deps {Assertion} _.

Definition admissible {Fact Assertion : Type}
    (bspec : BoundarySpec Fact Assertion) (E : EqbSpec Fact)
    (independently_admitted : Assertion -> Prop)
    (ctx : list Fact) (a : Assertion) : Prop :=
  classify bspec E ctx a = Verified /\ independently_admitted a.

Definition OpinionAdmissible {Fact Assertion : Type}
    (bspec : BoundarySpec Fact Assertion) (E : EqbSpec Fact)
    (material : Assertion -> bool)
    (independently_admitted : Assertion -> Prop)
    (ctx : list Fact) (o : Opinion Assertion) : Prop :=
  forall a, In a (op_deps o) -> material a = true ->
    admissible bspec E independently_admitted ctx a.

Theorem default_free_admissibility :
  forall {Fact Assertion : Type}
    (bspec : BoundarySpec Fact Assertion) (E : EqbSpec Fact)
    (material : Assertion -> bool)
    (independently_admitted : Assertion -> Prop)
    (ctx : list Fact) (o : Opinion Assertion),
    OpinionAdmissible bspec E material independently_admitted ctx o ->
    forall a, In a (op_deps o) -> material a = true ->
      classify bspec E ctx a = Verified /\ independently_admitted a.
Proof.
  intros Fact Assertion bspec E material independently_admitted ctx o Hop a Hin Hmat.
  exact (Hop a Hin Hmat).
Qed.

Corollary contrapositive_inadmissible :
  forall {Fact Assertion : Type}
    (bspec : BoundarySpec Fact Assertion) (E : EqbSpec Fact)
    (material : Assertion -> bool)
    (independently_admitted : Assertion -> Prop)
    (ctx : list Fact) (o : Opinion Assertion) (a : Assertion),
    In a (op_deps o) -> material a = true ->
    classify bspec E ctx a = Undefined ->
    ~ OpinionAdmissible bspec E material independently_admitted ctx o.
Proof.
  intros Fact Assertion bspec E material independently_admitted ctx o a Hin Hmat Hundef Hop.
  destruct (Hop a Hin Hmat) as [Hst _].
  rewrite Hst in Hundef; discriminate.
Qed.

(** Composition (Rule / Principle "Composition" in both papers): an
    opinion with two dependencies is admissible only if both are; one
    Undefined dependency is enough to block the conjunction regardless
    of how many others are Verified. This is the "weakest unresolved
    dependency" inheritance direction stated in Section 6 (STTT) /
    Section 5.4 (AIS). *)
Corollary composition_weakest_link :
  forall {Fact Assertion : Type}
    (bspec : BoundarySpec Fact Assertion) (E : EqbSpec Fact)
    (material : Assertion -> bool)
    (independently_admitted : Assertion -> Prop)
    (ctx : list Fact)
    (a_good a_bad : Assertion),
    material a_good = true -> material a_bad = true ->
    classify bspec E ctx a_good = Verified ->
    independently_admitted a_good ->
    classify bspec E ctx a_bad = Undefined ->
    ~ OpinionAdmissible bspec E material independently_admitted ctx
        (mkOpinion [a_good; a_bad]).
Proof.
  intros Fact Assertion bspec E material independently_admitted ctx a_good a_bad
    Hmg Hmb Hgood_state Hgood_adm Hbad_undef.
  eapply contrapositive_inadmissible with (a := a_bad).
  - simpl. right. left. reflexivity.
  - exact Hmb.
  - exact Hbad_undef.
Qed.
