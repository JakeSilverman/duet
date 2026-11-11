(* Diagnostic driver for the unchanged array termination pipeline. *)
open Srk
open Syntax
module Ctx = MakeSimplifyingContext ()
module Chc = Chc.Make(Ctx)
let srk = Ctx.context
let pd = (module Pmfa.OldPmfa.Array_analysis
    (Iteration.Product(Iteration.LossyTranslation)(Iteration.PolyhedronGuard))
    (Iteration.Product(Iteration.GuardedTranslation)(Iteration.PolyhedronGuard)) : Iteration.PreDomain)

let stage label f =
  let cpu = Sys.time () and wall = Unix.gettimeofday () in
  let value = f () in
  Printf.printf "STAGE %s cpu=%.6f wall=%.6f\n%!" label
    (Sys.time () -. cpu) (Unix.gettimeofday () -. wall);
  value

let size label phi =
  Printf.printf "SIZE %s nodes=%d\n%!" label (Syntax.size phi); phi

let () =
  if Array.length Sys.argv <> 3 then failwith "usage: profile_termination off|on INPUT.smt2";
  Pmfa.OldPmfa.use_termination_equality_opt := false;
  Printf.printf "CONFIG signs=%s equality=false\n%!" Sys.argv.(1);
  let fp = stage "parse" (fun () -> Chc.ChcSrkZ3.parse_file Sys.argv.(2)) in
  let fp = stage "elim_ite" (fun () -> Chc.ShOffsetAnalysis.elim_ite_chc fp) in
  let fp = stage "offset" (fun () -> Chc.ShOffsetAnalysis.offset_analysis fp) in
  let fp = if Sys.argv.(1) = "on" then stage "signs" (fun () ->
    let fp,r = Chc.Fp.ForwardSign.strengthen ~annotation:`Pruned fp in
    Printf.printf "SIGNS validated=%b inference_wall=%.6f pruning_wall=%.6f candidate=%d retained=%d\n%!"
      r.validated r.seconds r.pruning_seconds r.annotation_atoms r.retained_atoms;
    fp) else fp in
  let rules = Chc.Fp.get_rules fp in
  Printf.printf "RULES count=%d total_size=%d\n%!" (List.length rules)
    (List.fold_left (fun total (_,_,phi) -> total + Syntax.size phi) 0 rules);
  let phi = stage "summarize" (fun () -> Chc.Fp.query_vc_terminates fp pd) |> size "summary" in
  let phi = stage "cleanup" (fun () -> RuntimeSimplify.cleanup srk phi) |> size "cleaned" in
  let phi = stage "array_elim" (fun () ->
    phi |> eliminate_ite srk |> Chc.ShOffsetAnalysis.eliminate_stores |> eliminate_ite srk) |> size "array_elim" in
  let lia,_ = stage "pmfa" (fun () -> Pmfa.OldPmfa.pmfa_to_lia srk phi) in
  let lia = stage "cheap" (fun () -> RuntimeSimplify.cheap srk lia) |> size "lia" in
  let answer = stage "final_solver" (fun () -> Quantifier.simsat srk lia) in
  Printf.printf "RESULT %s\n%!" (match answer with `Unsat -> "Safe" | `Sat -> "UnknownSAT" | `Unknown -> "UnknownREAL")
