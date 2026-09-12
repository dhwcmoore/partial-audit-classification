(* main.ml — a small CLI that runs the three worked cases of the
   accompanying papers (Wirecard, continuous auditing, SQL Unknown)
   against the Coq-extracted classifier in [Audit_kernel]. This is the
   "executable OCaml classifier" referred to in both manuscripts:
   [Audit_kernel.run_pipeline] is not a reimplementation of the Coq
   development, it *is* the Coq development, compiled. The case data
   below mirrors rocq/Cases.v exactly; see NON_CLAIMS.md for what
   running this does and does not establish.

   v0.2: this CLI is a thin presentation layer. Every classification,
   admission check, residual emission, and opinion decision below is
   computed by [Audit_kernel.run_pipeline] (extracted from
   [Pipeline.run_pipeline], whose soundness is
   [pipeline_unqualified_sound]); this file only builds the pipeline
   inputs and prints the result. It does not infer opinion
   admissibility from a classification by itself -- there is no
   [if state = Verified then "yes" else "no"] here, because that is
   exactly the inference the v0.2 development exists to rule out
   (Fixture 2 below is a classification that is Verified and an
   opinion that is nonetheless inadmissible, for want of a
   certificate). *)

open Audit_kernel

let ostring (s : string) : char list = List.of_seq (String.to_seq s)

let string_of_state = function
  | Verified -> "Verified"
  | Refuted -> "Refuted"
  | Undefined -> "Undefined"
  | PresumptivelyVerified -> "PresumptivelyVerified"
  | PresumptivelyRefuted -> "PresumptivelyRefuted"
  | EscalationRequired -> "EscalationRequired"

let string_of_reason = function
  | NotVerified (_, s) -> Printf.sprintf "NotVerified(%s)" (string_of_state s)
  | MissingCertificate _ -> "MissingCertificate"
  | InvalidCertificate _ -> "InvalidCertificate"

let string_of_opinion = function
  | Unqualified -> "Unqualified"
  | InadmissibleOpinion reasons ->
    Printf.sprintf "Inadmissible [%s]" (String.concat "; " (List.map string_of_reason reasons))

let rule width = print_endline (String.make width '-')

(* ---------- Case 1: Wirecard ------------------------------------- *)

type wfact =
  | BankExistsIndependent
  | ConfirmationRouteControlledByAuditor
  | JurisdictionPermitsDirectConfirmation
  | AccountIdentifierSupplied
  | AuthenticatedChannel

type wassertion = CashExistencePhilippineTrustee

let wfeq (x : wfact) (y : wfact) = x = y

let direct_bank_confirmation : (wfact, wassertion) procedure =
  { procedure_id = 0;
    procedure_name = ostring "Direct bank confirmation";
    procedure_preconditions =
      [ BankExistsIndependent; ConfirmationRouteControlledByAuditor;
        JurisdictionPermitsDirectConfirmation; AccountIdentifierSupplied;
        AuthenticatedChannel ];
    procedure_covers = (fun _ -> true) }

let wirecard_boundary : (wfact, wassertion) boundarySpec =
  { boundary_id = 0; boundary_version = 1; boundary_procedures = [ direct_bank_confirmation ] }

let wirecard_observed : wfact list = [ BankExistsIndependent; AccountIdentifierSupplied ]
let wirecard_full : wfact list =
  [ BankExistsIndependent; ConfirmationRouteControlledByAuditor;
    JurisdictionPermitsDirectConfirmation; AccountIdentifierSupplied;
    AuthenticatedChannel ]

(* A minimal registry: one proposing process, one verifying process,
   distinct identities -- the same shape rocq/Cases.v's Wirecard
   module uses. *)
let w_proposer : process = { process_id = 1; process_role = Proposer }
let w_verifier : process = { process_id = 2; process_role = Verifier }
let w_verifier2 : process = { process_id = 3; process_role = Verifier }
let w_registry : processRegistry = [ w_proposer; w_verifier; w_verifier2 ]

let w_valid_cert : admissionCertificate =
  { admission_proposal_id = 100; admission_verifier = w_verifier.process_id; admission_decision = true }
let w_self_cert : admissionCertificate =
  { admission_proposal_id = 100; admission_verifier = w_proposer.process_id; admission_decision = true }

(* No [claimed : evidenceState] parameter (v0.1 of this CLI had one):
   [build_packet] constructs the proposal's classification from the
   real [classify] output for the real assertion, mirroring the
   Pipeline.v fix in rocq/Cases.v -- there is no longer a value here
   that could disagree with the actual classification. *)
let w_input (ctx : wfact list) (proposer_id : processId) (cert : admissionCertificate option)
    : (wfact, wassertion) pipelineInput =
  { pi_bspec = wirecard_boundary; pi_eq = wfeq; pi_context = ctx; pi_context_id = 0;
    pi_assertions = [ CashExistencePhilippineTrustee ]; pi_material = (fun _ -> true);
    pi_proposal_id = (fun _ -> 100); pi_proposer = (fun _ -> proposer_id);
    pi_certificate = (fun _ -> cert); pi_registry = w_registry }

let print_fixture label input =
  let result = run_pipeline input 0 [] in
  Printf.printf "  %s\n" label;
  Printf.printf "    Classification:  %s\n"
    (String.concat ", " (List.map string_of_state result.decision_classifications));
  Printf.printf "    Opinion:         %s\n" (string_of_opinion result.decision_opinion);
  Printf.printf "    Open residuals:  %d\n" (List.length result.decision_residuals)

let run_wirecard () =
  print_endline "Case 1: Wirecard cash-existence assertion (Section 7.1 / Section 7)";
  rule 70;
  Printf.printf "  Assertion: EUR 1.9bn held in Philippine trustee accounts\n\n";
  print_fixture "Fixture 1 -- incomplete evidence:"
    (w_input wirecard_observed w_proposer.process_id None);
  print_fixture "Fixture 2 -- complete evidence, no admission certificate presented:"
    (w_input wirecard_full w_proposer.process_id None);
  print_fixture "Fixture 3 -- complete evidence, admitted by a distinct verifier:"
    (w_input wirecard_full w_proposer.process_id (Some w_valid_cert));
  print_fixture "Fixture 4 -- complete evidence, proposer self-certifies:"
    (w_input wirecard_full w_proposer.process_id (Some w_self_cert));
  print_fixture "Fixture 5 -- unregistered proposer identity:"
    (w_input wirecard_full 999 (Some w_valid_cert));
  print_fixture "Fixture 6 -- proposer identity registered with the wrong role:"
    (w_input wirecard_full w_verifier2.process_id (Some w_valid_cert));
  print_newline ()

(* ---------- Case 2: Continuous auditing --------------------------- *)

type cafact = ReviewedByAnalyst of int
type caassertion = Txn of int

let cafeq (x : cafact) (y : cafact) = x = y

let proc_for (n : int) : (cafact, caassertion) procedure =
  { procedure_id = n;
    procedure_name = ostring "Human review";
    procedure_preconditions = [ ReviewedByAnalyst n ];
    procedure_covers = (fun a -> match a with Txn m -> m = n) }

let ca_boundary : (cafact, caassertion) boundarySpec =
  { boundary_id = 1; boundary_version = 1; boundary_procedures = List.init 10 proc_for }

let ca_observed : cafact list = [ ReviewedByAnalyst 0; ReviewedByAnalyst 1 ]

(* The analyst proposes; a supervisor, a distinct registered identity,
   admits transactions 0 and 1 -- the ones the boundary actually
   classifies Verified. Transactions 2-9 carry no certificate: nothing
   was reviewed for them to admit. *)
let ca_analyst : process = { process_id = 0; process_role = Proposer }
let ca_supervisor : process = { process_id = 1; process_role = Verifier }
let ca_registry : processRegistry = [ ca_analyst; ca_supervisor ]

let ca_certificate (n : int) : admissionCertificate option =
  if n = 0 then Some { admission_proposal_id = 0; admission_verifier = ca_supervisor.process_id; admission_decision = true }
  else if n = 1 then Some { admission_proposal_id = 1; admission_verifier = ca_supervisor.process_id; admission_decision = true }
  else None

let ca_input : (cafact, caassertion) pipelineInput =
  { pi_bspec = ca_boundary; pi_eq = cafeq; pi_context = ca_observed; pi_context_id = 0;
    pi_assertions = List.init 10 (fun n -> Txn n); pi_material = (fun _ -> true);
    pi_proposal_id = (fun a -> match a with Txn n -> n);
    pi_proposer = (fun _ -> ca_analyst.process_id);
    pi_certificate = (fun a -> match a with Txn n -> ca_certificate n);
    pi_registry = ca_registry }

let run_continuous_auditing () =
  print_endline "Case 2: Continuous auditing exception queue (Section 7.2 / Section 8)";
  rule 70;
  let result = run_pipeline ca_input 0 [] in
  Printf.printf "  Transactions:          10 (2 reviewed and admitted, 8 unresolved)\n";
  List.iteri (fun n s -> Printf.printf "  Txn %d: %s\n" n (string_of_state s))
    result.decision_classifications;
  Printf.printf "  Residual register entries after this run: %d\n" (List.length result.decision_residuals);
  Printf.printf "  Opinion: %s\n" (string_of_opinion result.decision_opinion);
  (* Dashboard clearing: a further, permitted workflow transition (any
     [step]) that only appends -- it cannot remove the residuals just
     emitted. There is no distinct "Unreviewed" state here: the
     transactions above are Undefined, exactly as [classify] computed,
     and [residual_preservation] (Residual.v) is what guarantees the
     count below cannot drop. *)
  let cleared = [] @ result.decision_residuals in
  Printf.printf "  Residual register entries after \"clearing\" the dashboard: %d\n" (List.length cleared);
  print_newline ()

(* ---------- Case 3: SQL Unknown ------------------------------------ *)

type sqlfact = ScoreIsPresent
type sqlassertion = RiskScoreAssertion

let sqlfeq (_ : sqlfact) (_ : sqlfact) = true

let score_procedure : (sqlfact, sqlassertion) procedure =
  { procedure_id = 0; procedure_name = ostring "Risk score present";
    procedure_preconditions = [ ScoreIsPresent ]; procedure_covers = (fun _ -> true) }

let sql_boundary : (sqlfact, sqlassertion) boundarySpec =
  { boundary_id = 2; boundary_version = 1; boundary_procedures = [ score_procedure ] }

(* The adapter: an [option int] risk score becomes boundary evidence --
   present in the context iff the score is [Some _] -- and the
   classification is whatever [classify] computes from that, never a
   numeric coercion. *)
let context_for (r : int option) : sqlfact list =
  match r with Some _ -> [ ScoreIsPresent ] | None -> []

let nullable_score_to_classification (r : int option) : evidenceState =
  classify sql_boundary sqlfeq (context_for r) RiskScoreAssertion

(* The pre-existing renderer illustration, a layer above the boundary
   machinery: two ways of turning a classification back into a
   downstream value. *)
type risk_score = Score of int | ScoreUnknown
let silently_converted_render = function Score n -> n | ScoreUnknown -> 0
type rendered_state = RNumeric of int | RUndefined
let disciplined_render = function Score n -> RNumeric n | ScoreUnknown -> RUndefined

let run_sql_unknown () =
  print_endline "Case 3: SQL Unknown collapsing at the reporting layer (Section 7.3 / Section 2.3)";
  rule 70;
  Printf.printf "  nullable_score_to_classification(None)   = %s\n"
    (string_of_state (nullable_score_to_classification None));
  Printf.printf "  nullable_score_to_classification(Some 0) = %s\n"
    (string_of_state (nullable_score_to_classification (Some 0)));
  Printf.printf "  distinguishable: %s\n"
    (if nullable_score_to_classification None <> nullable_score_to_classification (Some 0)
     then "yes" else "no");
  Printf.printf "  silently_converted_render(Unknown) = %d\n" (silently_converted_render ScoreUnknown);
  Printf.printf "  silently_converted_render(Score 0) = %d   (indistinguishable from Unknown)\n"
    (silently_converted_render (Score 0));
  let du = disciplined_render ScoreUnknown and d0 = disciplined_render (Score 0) in
  Printf.printf "  disciplined_render(Unknown) = %s\n"
    (match du with RNumeric n -> Printf.sprintf "RNumeric %d" n | RUndefined -> "RUndefined");
  Printf.printf "  disciplined_render(Score 0) = %s\n"
    (match d0 with RNumeric n -> Printf.sprintf "RNumeric %d" n | RUndefined -> "RUndefined");
  Printf.printf "  distinguishable under the disciplined renderer: %s\n"
    (if du <> d0 then "yes" else "no");
  print_newline ()

let () =
  print_endline "";
  print_endline "Partial Audit Classification -- worked-case runner";
  print_endline "(extracted from rocq/*.v; matches rocq/Cases.v exactly)";
  print_endline "";
  run_wirecard ();
  run_continuous_auditing ();
  run_sql_unknown ()
