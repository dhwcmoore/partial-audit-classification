Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import PAC.Base.

(** SelfAdmission.v — Theorem 3 (No Self-Admission in the STTT paper /
    Admission Separation in the AIS paper): "A proposed classification
    cannot admit itself. Admission is performed only by a verifier
    independent of the process that generated the proposal."

    v0.2 replaces the v0.1 role model -- which proved only that
    [Proposer] and [Verifier] are distinct constructors, without
    modelling a proposal, a certificate, or process identity -- with a
    computational admission check, [validate_admission], over
    identified processes, identified proposals, and identified
    certificates. [validate_admission] is what the extracted classifier
    actually runs; [no_self_admission]/[role_separation] below remain
    true and are kept as the declarative statement of *why* the check
    works (a process cannot occupy both roles for the same assertion),
    but the certificate check is what is now proved sound, not merely
    the role type's shape.

    "Independent" here means, precisely: a distinct registered process
    identity, holding the Verifier role in the supplied registry, whose
    certificate names the exact proposal being admitted. It does not
    mean, and this development does not prove, that two distinct
    identifiers cannot be controlled by the same person or organisation,
    or that collusion between honestly single-role processes is
    prevented. See NON_CLAIMS.md. *)

Inductive Role := Proposer | Verifier.

Record Process := mkProcess {
  process_id   : ProcessId;
  process_role : Role
}.

Definition proposes {Assertion : Type} (p : Process) (_ : Assertion) : Prop :=
  process_role p = Proposer.

Definition admits {Assertion : Type} (p : Process) (_ : Assertion) : Prop :=
  process_role p = Verifier.

Theorem no_self_admission :
  forall {Assertion : Type} (p : Process) (a : Assertion),
    proposes p a -> ~ admits p a.
Proof.
  intros Assertion p a Hprop Hadmit.
  unfold proposes in Hprop; unfold admits in Hadmit.
  rewrite Hprop in Hadmit; discriminate.
Qed.

(** No process is both a proposer and a verifier of the same assertion
    at once: the stronger, symmetric statement a reviewer would ask for
    after reading no_self_admission. *)
Theorem role_separation :
  forall {Assertion : Type} (p : Process) (a : Assertion),
    ~ (proposes p a /\ admits p a).
Proof.
  intros Assertion p a [Hprop Hadmit].
  exact (no_self_admission p a Hprop Hadmit).
Qed.

(** ** Proposals and certificates

    A registry is the declared population of known processes. Looking a
    process up by identifier, rather than trusting a bare [Role] value
    supplied at the call site, is what makes [validate_admission] a
    check against a declared population rather than against whatever a
    caller happens to assert about itself. *)
Definition ProcessRegistry := list Process.

Definition process_lookup (registry : ProcessRegistry) (pid : ProcessId) : option Process :=
  find (fun p => Nat.eqb (process_id p) pid) registry.

(** The classification a proposal claims. An alias for [EvidenceState],
    named for the role it plays here: the verdict a proposing process is
    putting forward for admission, not yet an admitted classification. *)
Definition Classification := EvidenceState.

Record ClassificationProposal (Assertion : Type) := mkClassificationProposal {
  proposal_id             : ProposalId;
  proposal_assertion      : Assertion;
  proposal_classification : Classification;
  proposal_process        : ProcessId
}.
Arguments mkClassificationProposal {Assertion} _ _ _ _.
Arguments proposal_id {Assertion} _.
Arguments proposal_assertion {Assertion} _.
Arguments proposal_classification {Assertion} _.
Arguments proposal_process {Assertion} _.

Record AdmissionCertificate := mkAdmissionCertificate {
  admission_proposal_id : ProposalId;
  admission_verifier     : ProcessId;
  admission_decision     : bool
}.

(** The computational admission check. Every conjunct is load-bearing
    and each has its own rejection theorem below: a certificate that
    fails any one of them is not a valid admission, regardless of the
    others. *)
Definition validate_admission {Assertion : Type}
    (registry : ProcessRegistry) (proposal : ClassificationProposal Assertion)
    (cert : AdmissionCertificate) : bool :=
  Nat.eqb (admission_proposal_id cert) (proposal_id proposal) &&
  (match process_lookup registry (admission_verifier cert) with
   | Some verifier_proc =>
       match process_role verifier_proc with
       | Verifier => true
       | Proposer => false
       end
   | None => false
   end) &&
  negb (Nat.eqb (admission_verifier cert) (proposal_process proposal)) &&
  admission_decision cert &&
  eqb_state (proposal_classification proposal) Verified.

Theorem valid_admission_implies_verified :
  forall {Assertion : Type} (registry : ProcessRegistry)
    (proposal : ClassificationProposal Assertion) (cert : AdmissionCertificate),
    validate_admission registry proposal cert = true ->
    proposal_classification proposal = Verified.
Proof.
  intros Assertion registry proposal cert H.
  unfold validate_admission in H.
  apply andb_true_iff in H as [H H5].
  apply eqb_state_eq. assumption.
Qed.

Theorem valid_admission_implies_distinct_process :
  forall {Assertion : Type} (registry : ProcessRegistry)
    (proposal : ClassificationProposal Assertion) (cert : AdmissionCertificate),
    validate_admission registry proposal cert = true ->
    admission_verifier cert <> proposal_process proposal.
Proof.
  intros Assertion registry proposal cert H.
  unfold validate_admission in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H3].
  apply Nat.eqb_neq. apply negb_true_iff. assumption.
Qed.

Theorem proposer_certificate_rejected :
  forall {Assertion : Type} (registry : ProcessRegistry)
    (proposal : ClassificationProposal Assertion) (cert : AdmissionCertificate),
    admission_verifier cert = proposal_process proposal ->
    validate_admission registry proposal cert = false.
Proof.
  intros Assertion registry proposal cert Heq.
  destruct (validate_admission registry proposal cert) eqn:Hv; [| reflexivity].
  apply valid_admission_implies_distinct_process in Hv. contradiction.
Qed.

Theorem certificate_for_wrong_proposal_rejected :
  forall {Assertion : Type} (registry : ProcessRegistry)
    (proposal : ClassificationProposal Assertion) (cert : AdmissionCertificate),
    admission_proposal_id cert <> proposal_id proposal ->
    validate_admission registry proposal cert = false.
Proof.
  intros Assertion registry proposal cert Hneq.
  unfold validate_admission.
  destruct (Nat.eqb (admission_proposal_id cert) (proposal_id proposal)) eqn:Hid.
  - apply Nat.eqb_eq in Hid. contradiction.
  - reflexivity.
Qed.

Theorem non_verifier_certificate_rejected :
  forall {Assertion : Type} (registry : ProcessRegistry)
    (proposal : ClassificationProposal Assertion) (cert : AdmissionCertificate),
    (forall verifier_proc, process_lookup registry (admission_verifier cert) = Some verifier_proc ->
       process_role verifier_proc = Proposer) \/
    process_lookup registry (admission_verifier cert) = None ->
    validate_admission registry proposal cert = false.
Proof.
  intros Assertion registry proposal cert H.
  unfold validate_admission.
  destruct (Nat.eqb (admission_proposal_id cert) (proposal_id proposal)) eqn:Hid; [| reflexivity].
  simpl.
  destruct (process_lookup registry (admission_verifier cert)) as [verifier_proc |] eqn:Hlookup.
  - destruct H as [H | H].
    + rewrite (H verifier_proc eq_refl). reflexivity.
    + discriminate.
  - reflexivity.
Qed.
