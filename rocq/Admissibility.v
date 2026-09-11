Require Import List.
Import ListNotations.
Require Import PAC.Base.
Require Import PAC.Boundary.

(** Admissibility.v — Definition 2.1 (Admissibility) and Theorem 1
    (Default-Free Admissibility) with its Corollary (Contrapositive),
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
    admissibility, however many other dependencies are Verified. *)

Record Opinion (Assertion : Type) := mkOpinion { op_deps : list Assertion }.
Arguments mkOpinion {Assertion} _.
Arguments op_deps {Assertion} _.

Definition admissible {Fact Assertion : Type}
    (feq : Fact -> Fact -> bool)
    (independently_admitted : Assertion -> Prop)
    (ctx : list Fact) (bspec : BoundarySpec Fact Assertion) (a : Assertion) : Prop :=
  boundary_state feq ctx a bspec = Verified /\ independently_admitted a.

Definition OpinionAdmissible {Fact Assertion : Type}
    (feq : Fact -> Fact -> bool)
    (material : Assertion -> bool)
    (independently_admitted : Assertion -> Prop)
    (ctx : list Fact) (bspec : BoundarySpec Fact Assertion) (o : Opinion Assertion) : Prop :=
  forall a, In a (op_deps o) -> material a = true ->
    admissible feq independently_admitted ctx bspec a.

Theorem default_free_admissibility :
  forall {Fact Assertion : Type}
    (feq : Fact -> Fact -> bool)
    (material : Assertion -> bool)
    (independently_admitted : Assertion -> Prop)
    (ctx : list Fact) (bspec : BoundarySpec Fact Assertion) (o : Opinion Assertion),
    OpinionAdmissible feq material independently_admitted ctx bspec o ->
    forall a, In a (op_deps o) -> material a = true ->
      boundary_state feq ctx a bspec = Verified /\ independently_admitted a.
Proof.
  intros Fact Assertion feq material independently_admitted ctx bspec o Hop a Hin Hmat.
  exact (Hop a Hin Hmat).
Qed.

Corollary contrapositive_inadmissible :
  forall {Fact Assertion : Type}
    (feq : Fact -> Fact -> bool)
    (material : Assertion -> bool)
    (independently_admitted : Assertion -> Prop)
    (ctx : list Fact) (bspec : BoundarySpec Fact Assertion) (o : Opinion Assertion) (a : Assertion),
    In a (op_deps o) -> material a = true ->
    boundary_state feq ctx a bspec = Undefined ->
    ~ OpinionAdmissible feq material independently_admitted ctx bspec o.
Proof.
  intros Fact Assertion feq material independently_admitted ctx bspec o a Hin Hmat Hundef Hop.
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
    (feq : Fact -> Fact -> bool)
    (material : Assertion -> bool)
    (independently_admitted : Assertion -> Prop)
    (ctx : list Fact) (bspec : BoundarySpec Fact Assertion)
    (a_good a_bad : Assertion),
    material a_good = true -> material a_bad = true ->
    boundary_state feq ctx a_good bspec = Verified ->
    independently_admitted a_good ->
    boundary_state feq ctx a_bad bspec = Undefined ->
    ~ OpinionAdmissible feq material independently_admitted ctx bspec
        (mkOpinion [a_good; a_bad]).
Proof.
  intros Fact Assertion feq material independently_admitted ctx bspec a_good a_bad
    Hmg Hmb Hgood_state Hgood_adm Hbad_undef.
  eapply contrapositive_inadmissible with (a := a_bad).
  - simpl. right. left. reflexivity.
  - exact Hmb.
  - exact Hbad_undef.
Qed.
