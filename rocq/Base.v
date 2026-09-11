(** Base.v — the EvidenceState and AuditUse vocabulary.

    This is the six-state classification vocabulary defined in Section 2
    of "A Discipline of Partial Audit Classification" (submitted, STTT)
    and Section 5.2 / Appendix A of "Boundary Discipline for Accounting
    Information Systems" (submitted, IJDAR). It is declared here exactly
    once and used by every other module in this development, so that
    nothing downstream is a re-encoding of it. *)

Inductive EvidenceState : Type :=
  | Verified
  | Refuted
  | Undefined
  | PresumptivelyVerified
  | PresumptivelyRefuted
  | EscalationRequired.

Inductive AuditUse : Type :=
  | Admissible
  | Inadmissible.

Definition eqb_state (a b : EvidenceState) : bool :=
  match a, b with
  | Verified, Verified => true
  | Refuted, Refuted => true
  | Undefined, Undefined => true
  | PresumptivelyVerified, PresumptivelyVerified => true
  | PresumptivelyRefuted, PresumptivelyRefuted => true
  | EscalationRequired, EscalationRequired => true
  | _, _ => false
  end.

Lemma eqb_state_eq : forall a b, eqb_state a b = true <-> a = b.
Proof.
  intros a b; split; intro H.
  - destruct a, b; simpl in H; try congruence.
  - subst; destruct b; reflexivity.
Qed.

Lemma evidence_state_dec : forall a b : EvidenceState, {a = b} + {a <> b}.
Proof.
  decide equality.
Defined.

(** Only [Verified] admits an unqualified conclusion; every other state
    is non-affirmative. This is the single fact the rest of the
    development is built to preserve. *)
Definition affirmative (s : EvidenceState) : bool :=
  match s with
  | Verified => true
  | _ => false
  end.
