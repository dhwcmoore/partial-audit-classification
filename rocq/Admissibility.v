Require Import List.
Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import PAC.Base.
Require Import PAC.Boundary.
Require Import PAC.SelfAdmission.

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

(** ** The executable opinion decision

    [OpinionAdmissible] above is the declarative specification: it says
    what "admissible as unqualified" means, but as a [Prop] it is not
    something an extracted program runs. [decide_opinion] is the
    computational decision procedure the papers describe as "the
    extracted decision procedure [that] cannot return Unqualified
    unless..." -- it inspects one [DependencyPacket] per material
    assertion (its classification, its proposal, and its admission
    certificate if one was presented) and computes, rather than merely
    specifies, whether the opinion may be Unqualified.
    [decide_opinion_unqualified_sound] is the theorem that now
    justifies "by construction": it is soundness of an executable
    function, not an unfolding of a Prop defined to already contain the
    desired property. [default_free_admissibility] above remains valid
    as a specification lemma, but this is the central result. *)

Inductive InadmissibilityReason (Assertion : Type) :=
  | NotVerified (a : Assertion) (s : EvidenceState)
  | MissingCertificate (a : Assertion)
  | InvalidCertificate (a : Assertion).
Arguments NotVerified {Assertion} _ _.
Arguments MissingCertificate {Assertion} _.
Arguments InvalidCertificate {Assertion} _.

Inductive OpinionDecision (Assertion : Type) :=
  | Unqualified
  | InadmissibleOpinion (reasons : list (InadmissibilityReason Assertion)).
Arguments Unqualified {Assertion}.
Arguments InadmissibleOpinion {Assertion} _.

(** A dependency packet is everything [decide_opinion] needs about one
    material-or-not assertion: whether it is material, the
    classification computed for it (by [classify], though this record
    does not itself require that provenance), the proposal that
    classification was put forward as, and the admission certificate
    presented for it, if any. *)
Record DependencyPacket (Assertion : Type) := mkDependencyPacket {
  dep_assertion   : Assertion;
  dep_material    : bool;
  dep_state       : EvidenceState;
  dep_proposal    : ClassificationProposal Assertion;
  dep_certificate : option AdmissionCertificate
}.
Arguments mkDependencyPacket {Assertion} _ _ _ _ _.
Arguments dep_assertion {Assertion} _.
Arguments dep_material {Assertion} _.
Arguments dep_state {Assertion} _.
Arguments dep_proposal {Assertion} _.
Arguments dep_certificate {Assertion} _.

Definition dep_valid_admission {Assertion : Type}
    (registry : ProcessRegistry) (d : DependencyPacket Assertion) : bool :=
  match dep_certificate d with
  | None => false
  | Some cert => validate_admission registry (dep_proposal d) cert
  end.

(** A dependency is decision-ready only if it is both classified
    Verified and carries a certificate that validates. Either failing
    makes [dep_ok] false, regardless of the other. *)
Definition dep_ok {Assertion : Type}
    (registry : ProcessRegistry) (d : DependencyPacket Assertion) : bool :=
  eqb_state (dep_state d) Verified && dep_valid_admission registry d.

Definition reason_for {Assertion : Type} (d : DependencyPacket Assertion)
    : InadmissibilityReason Assertion :=
  if negb (eqb_state (dep_state d) Verified)
  then NotVerified (dep_assertion d) (dep_state d)
  else match dep_certificate d with
       | None => MissingCertificate (dep_assertion d)
       | Some _ => InvalidCertificate (dep_assertion d)
       end.

Definition decide_opinion {Assertion : Type}
    (registry : ProcessRegistry) (deps : list (DependencyPacket Assertion))
    : OpinionDecision Assertion :=
  let material_deps := filter dep_material deps in
  if forallb (dep_ok registry) material_deps
  then Unqualified
  else InadmissibleOpinion (map reason_for (filter (fun d => negb (dep_ok registry d)) material_deps)).

Theorem decide_opinion_unqualified_sound :
  forall {Assertion : Type} (registry : ProcessRegistry) (deps : list (DependencyPacket Assertion)),
    decide_opinion registry deps = Unqualified ->
    forall d, In d deps -> dep_material d = true ->
      dep_state d = Verified /\ dep_valid_admission registry d = true.
Proof.
  intros Assertion registry deps Hdec d Hin Hmat.
  unfold decide_opinion in Hdec.
  destruct (forallb (dep_ok registry) (filter dep_material deps)) eqn:Hall; [| discriminate].
  assert (Hd : dep_ok registry d = true).
  { apply forallb_forall with (x := d) in Hall; [exact Hall |].
    apply filter_In. split; assumption. }
  unfold dep_ok in Hd. apply andb_true_iff in Hd as [Hs Hv].
  split; [apply eqb_state_eq; exact Hs | exact Hv].
Qed.

(** ** Every way a dependency can block Unqualified

    One generic blocking lemma, [decide_opinion_blocked], and the eight
    named corollaries the specification calls for: any dependency that
    is material, present, and fails [dep_ok] rules out [Unqualified]
    for the whole decision, regardless of how many other dependencies
    are fine. *)

Theorem decide_opinion_blocked :
  forall {Assertion : Type} (registry : ProcessRegistry) (deps : list (DependencyPacket Assertion))
    (d : DependencyPacket Assertion),
    In d deps -> dep_material d = true -> dep_ok registry d = false ->
    decide_opinion registry deps <> Unqualified.
Proof.
  intros Assertion registry deps d Hin Hmat Hnok Hdec.
  unfold decide_opinion in Hdec.
  destruct (forallb (dep_ok registry) (filter dep_material deps)) eqn:Hall; [| discriminate].
  assert (Hd : dep_ok registry d = true).
  { apply forallb_forall with (x := d) in Hall; [exact Hall |].
    apply filter_In. split; assumption. }
  rewrite Hd in Hnok; discriminate.
Qed.

Lemma dep_ok_false_of_not_verified {Assertion : Type}
    (registry : ProcessRegistry) (d : DependencyPacket Assertion) :
  dep_state d <> Verified -> dep_ok registry d = false.
Proof.
  intro H. unfold dep_ok.
  destruct (eqb_state (dep_state d) Verified) eqn:E; [| reflexivity].
  apply eqb_state_eq in E. contradiction.
Qed.

Corollary undefined_blocks_unqualified :
  forall {Assertion : Type} (registry : ProcessRegistry) (deps : list (DependencyPacket Assertion))
    (d : DependencyPacket Assertion),
    In d deps -> dep_material d = true -> dep_state d = Undefined ->
    decide_opinion registry deps <> Unqualified.
Proof.
  intros. eapply decide_opinion_blocked; eauto.
  apply dep_ok_false_of_not_verified. rewrite H1. discriminate.
Qed.

Corollary refuted_blocks_unqualified :
  forall {Assertion : Type} (registry : ProcessRegistry) (deps : list (DependencyPacket Assertion))
    (d : DependencyPacket Assertion),
    In d deps -> dep_material d = true -> dep_state d = Refuted ->
    decide_opinion registry deps <> Unqualified.
Proof.
  intros. eapply decide_opinion_blocked; eauto.
  apply dep_ok_false_of_not_verified. rewrite H1. discriminate.
Qed.

Corollary presumptive_blocks_unqualified :
  forall {Assertion : Type} (registry : ProcessRegistry) (deps : list (DependencyPacket Assertion))
    (d : DependencyPacket Assertion),
    In d deps -> dep_material d = true ->
    (dep_state d = PresumptivelyVerified \/ dep_state d = PresumptivelyRefuted) ->
    decide_opinion registry deps <> Unqualified.
Proof.
  intros Assertion registry deps d Hin Hmat [H1 | H1];
    eapply decide_opinion_blocked; eauto;
    apply dep_ok_false_of_not_verified; rewrite H1; discriminate.
Qed.

Corollary escalation_blocks_unqualified :
  forall {Assertion : Type} (registry : ProcessRegistry) (deps : list (DependencyPacket Assertion))
    (d : DependencyPacket Assertion),
    In d deps -> dep_material d = true -> dep_state d = EscalationRequired ->
    decide_opinion registry deps <> Unqualified.
Proof.
  intros. eapply decide_opinion_blocked; eauto.
  apply dep_ok_false_of_not_verified. rewrite H1. discriminate.
Qed.

Corollary verified_without_admission_blocks_unqualified :
  forall {Assertion : Type} (registry : ProcessRegistry) (deps : list (DependencyPacket Assertion))
    (d : DependencyPacket Assertion),
    In d deps -> dep_material d = true ->
    dep_state d = Verified -> dep_certificate d = None ->
    decide_opinion registry deps <> Unqualified.
Proof.
  intros. eapply decide_opinion_blocked; eauto.
  unfold dep_ok, dep_valid_admission. rewrite H1, H2. reflexivity.
Qed.

Corollary invalid_admission_blocks_unqualified :
  forall {Assertion : Type} (registry : ProcessRegistry) (deps : list (DependencyPacket Assertion))
    (d : DependencyPacket Assertion) (cert : AdmissionCertificate),
    In d deps -> dep_material d = true -> dep_state d = Verified ->
    dep_certificate d = Some cert ->
    validate_admission registry (dep_proposal d) cert = false ->
    decide_opinion registry deps <> Unqualified.
Proof.
  intros. eapply decide_opinion_blocked; eauto.
  unfold dep_ok, dep_valid_admission. rewrite H1, H2, H3. reflexivity.
Qed.

(** ** Completeness: dependencies that are all fine allow Unqualified

    The converse of the blocking theorems: if every material dependency
    already satisfies [dep_ok], [decide_opinion] does return
    [Unqualified] -- the check is not vacuously impossible to pass. *)
Theorem all_valid_dependencies_allow_unqualified :
  forall {Assertion : Type} (registry : ProcessRegistry) (deps : list (DependencyPacket Assertion)),
    (forall d, In d deps -> dep_material d = true -> dep_ok registry d = true) ->
    decide_opinion registry deps = Unqualified.
Proof.
  intros Assertion registry deps Hall.
  unfold decide_opinion.
  assert (Htrue : forallb (dep_ok registry) (filter dep_material deps) = true).
  { apply forallb_forall. intros d Hin.
    apply filter_In in Hin as [Hin Hmat]. apply Hall; assumption. }
  rewrite Htrue. reflexivity.
Qed.
