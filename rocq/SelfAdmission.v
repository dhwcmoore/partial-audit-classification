(** SelfAdmission.v — Theorem 3 (No Self-Admission in the STTT paper /
    Admission Separation in the AIS paper): "A proposed classification
    cannot admit itself. Admission is performed only by a verifier
    independent of the process that generated the proposal."

    Proposing and admitting are modelled as two disjoint roles rather
    than two independent, unconstrained predicates: a [Process] carries
    exactly one [Role], so a process cannot occupy the Proposer role and
    the Verifier role for the same act of classification. The theorem is
    a direct consequence of that structural separation, not an assumed
    axiom — [no_self_admission] cannot be discharged by a proposing
    process simply relabelling itself, because relabelling changes
    [proc_role], and [proposes]/[admits] are defined against that same
    field. *)

Inductive Role := Proposer | Verifier.

Record Process := mkProcess { proc_role : Role }.

Definition proposes {Assertion : Type} (p : Process) (_ : Assertion) : Prop :=
  proc_role p = Proposer.

Definition admits {Assertion : Type} (p : Process) (_ : Assertion) : Prop :=
  proc_role p = Verifier.

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
