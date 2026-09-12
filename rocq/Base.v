(** Base.v — the EvidenceState and AuditUse vocabulary, plus the stable
    identifier types threaded through the v0.2 development.

    This is the six-state classification vocabulary defined in Section 2
    of "A Discipline of Partial Audit Classification" (submitted, STTT)
    and Section 5.2 / Appendix A of "Boundary Discipline for Accounting
    Information Systems" (submitted, IJDAR). It is declared here exactly
    once and used by every other module in this development, so that
    nothing downstream is a re-encoding of it.

    v0.2 scope note (see NON_CLAIMS.md): the six constructors below are
    the declared vocabulary. The mechanical classifier in Boundary.v
    generically produces only [Verified] and [Undefined] from a boundary
    specification and an evidence context; [Refuted], the two presumptive
    states, and [EscalationRequired] remain caller-supplied inputs to the
    residual register and the case studies, not outputs of a generic,
    proved-correct assignment procedure. Declaring all six constructors
    here is not a claim that a six-way classifier is mechanised. *)

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

(** Only [Verified] can support an unqualified conclusion; every other
    state does not. Named for what the function means, not merely for
    which branch of the match it takes: this is the single fact the rest
    of the development is built to preserve. (v0.1 named this
    [affirmative]; v0.2 renames it because "affirmative" described the
    match arm rather than the property callers actually rely on.) *)
Definition supports_unqualified (s : EvidenceState) : bool :=
  match s with
  | Verified => true
  | _ => false
  end.

(** Stable identifiers threaded through the v0.2 development: procedures,
    boundary specifications, evidence contexts, processes, classification
    proposals, and residual entries are all identified by one of these
    rather than by structural (list-position) identity. They are opaque
    tokens with decidable equality; nothing in this development attaches
    meaning to the underlying [nat], and no code should pattern-match on
    one to recover anything beyond equality. *)
Definition ProcedureId := nat.
Definition BoundaryId := nat.
Definition ContextId := nat.
Definition ProcessId := nat.
Definition ProposalId := nat.
Definition ResidualId := nat.
Definition OwnerId := nat.
