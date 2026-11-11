open Srk
open Syntax
module C=MakeSimplifyingContext ()
let srk=C.context
let () =
  if Array.length Sys.argv<>3 then failwith "usage: replay_formula MODE INPUT.smt2";
  let phi=SrkZ3.load_smtlib2_file srk Sys.argv.(2) in
  FormulaTrace.capture srk "replay-input" phi;
  let start=Sys.time () in
  let mode=Sys.argv.(1) in
  let phi=match mode with
    | "baseline" -> phi
    | "qe" -> Quantifier.eq_guided_elim_loop srk phi
    | "local-mini-qe" -> phi |> FormulaProbe.local srk |> Quantifier.miniscope srk |> Quantifier.eq_guided_qe srk |> FormulaProbe.local srk
    | "local" -> FormulaProbe.local srk phi
    | "local-qe" -> phi |> FormulaProbe.local srk |> Quantifier.eq_guided_elim_loop srk |> FormulaProbe.local srk
    | _ -> failwith "unknown mode" in
  Printf.printf "PREPROCESS cpu=%.6f size=%d\n%!" (Sys.time()-.start) (Syntax.size phi);
  FormulaTrace.capture srk "replay-output" phi;
  if Sys.getenv_opt "AUDIT_STOP_BEFORE_SOLVER"=Some "1" then exit 0;
  let start=Sys.time() in
  let ans=Quantifier.simsat srk phi in
  Printf.printf "SOLVER cpu=%.6f RESULT %s\n%!" (Sys.time()-.start)
    (match ans with `Unsat->"Safe" | `Sat->"UnknownSAT" | `Unknown->"UnknownREAL")
