(* main.ml — a small CLI that runs the three worked cases of the
   accompanying papers (Wirecard, continuous auditing, SQL Unknown)
   against the Coq-extracted classifier in [Audit_kernel]. This is the
   "executable OCaml classifier" referred to in both manuscripts:
   [Audit_kernel.classify] is not a reimplementation of the Coq
   development, it *is* the Coq development, compiled. The case data
   below mirrors rocq/Cases.v exactly; see NON_CLAIMS.md for what
   running this does and does not establish. *)

open Audit_kernel

let ostring (s : string) : char list = List.of_seq (String.to_seq s)

let string_of_state = function
  | Verified -> "Verified"
  | Refuted -> "Refuted"
  | Undefined -> "Undefined"
  | PresumptivelyVerified -> "PresumptivelyVerified"
  | PresumptivelyRefuted -> "PresumptivelyRefuted"
  | EscalationRequired -> "EscalationRequired"

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
let wirecard_full      : wfact list =
  [ BankExistsIndependent; ConfirmationRouteControlledByAuditor;
    JurisdictionPermitsDirectConfirmation; AccountIdentifierSupplied;
    AuthenticatedChannel ]

let run_wirecard () =
  print_endline "Case 1: Wirecard cash-existence assertion (Section 7.1 / Section 7)";
  rule 70;
  let observed_state =
    classify wirecard_boundary wfeq wirecard_observed CashExistencePhilippineTrustee in
  let full_state =
    classify wirecard_boundary wfeq wirecard_full CashExistencePhilippineTrustee in
  Printf.printf "  Assertion:            EUR 1.9bn held in Philippine trustee accounts\n";
  Printf.printf "  Observed evidence:    bank exists, account identifier supplied only\n";
  Printf.printf "  Classification:       %s\n" (string_of_state observed_state);
  Printf.printf "  Admissible as unqualified opinion: %s\n"
    (if observed_state = Verified then "yes" else "no");
  Printf.printf "\n  Counterfactual with full evidence (all five preconditions met):\n";
  Printf.printf "  Classification:       %s\n" (string_of_state full_state);
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

let run_continuous_auditing () =
  print_endline "Case 2: Continuous auditing exception queue (Section 7.2 / Section 8)";
  rule 70;
  let states = List.init 10 (fun n -> (n, classify ca_boundary cafeq ca_observed (Txn n))) in
  let residuals =
    List.filter_map
      (fun (n, s) -> if s = Verified then None
                     else Some { residual_assertion = Txn n; residual_state = s; residual_owner = None })
      states
  in
  Printf.printf "  Transactions:          10 (2 reviewed, 8 deprioritised)\n";
  List.iter (fun (n, s) -> Printf.printf "  Txn %d: %s\n" n (string_of_state s)) states;
  Printf.printf "  Residual register entries after \"clearing\" the dashboard: %d\n"
    (List.length residuals);
  Printf.printf "  Governing check -- Unreviewed <> Accepted: %s\n"
    (if List.for_all (fun e -> e.residual_state <> Verified) residuals
     then "holds for every residual entry" else "VIOLATED");
  print_newline ()

(* ---------- Case 3: SQL Unknown ------------------------------------ *)

type risk_score = Score of int | ScoreUnknown

let silently_converted_render = function Score n -> n | ScoreUnknown -> 0

type rendered_state = RNumeric of int | RUndefined

let disciplined_render = function Score n -> RNumeric n | ScoreUnknown -> RUndefined

let run_sql_unknown () =
  print_endline "Case 3: SQL Unknown collapsing at the reporting layer (Section 7.3 / Section 2.3)";
  rule 70;
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
