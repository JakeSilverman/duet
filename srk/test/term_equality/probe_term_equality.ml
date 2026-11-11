open Srk
open Syntax

module C = MakeSimplifyingContext ()
let srk = C.context
let c = mk_const srk
let n = mk_int srk
let eq = mk_eq srk
let arr_eq = mk_arr_eq srk
let and_ = mk_and srk
let pair name typ =
  mk_symbol srk ~name typ, mk_symbol srk ~name:(name ^ "_post") typ
let at a = mk_select srk (c a) (n 0)
let positive x = mk_lt srk (n 0) x
let x, xp = pair "x" `TyInt
let a, ap = pair "a" `TyArr
let b, bp = pair "b" `TyArr
let k, kp = pair "k" `TyInt

let probe name trs phi init =
  let started = Sys.time () in
  try
    let result = Pmfa.OldPmfa.mp srk (TransitionFormula.make phi trs) in
    let posts = List.filter (fun (_, p) -> Symbol.Set.mem p (symbols result)) trs in
    let solver = SrkZ3.mk_solver ~context:(Z3.mk_context [("timeout", "2000")]) srk in
    SrkZ3.Solver.add solver [result; init];
    let answer = match SrkZ3.Solver.check solver [] with
      | `Sat -> "sat" | `Unsat -> "unsat" | `Unknown -> "unknown" in
    Printf.printf "PROBE %s result=%s post_symbols=%d cpu=%.6f\n%s\n%!"
      name answer (List.length posts) (Sys.time () -. started)
      (Format.asprintf "%a" (Formula.pp srk) result)
  with exn -> Printf.printf "PROBE %s ERROR=%s\n%!" name (Printexc.to_string exn)

let () =
  Pmfa.OldPmfa.use_termination_equality_opt := Array.length Sys.argv > 1 && Sys.argv.(1) = "on";
  probe "scalar_exit" [x,xp] (and_ [eq (c xp) (c x); positive (c x)]) (eq (c x) (n 0));
  probe "scalar_infinite" [x,xp] (and_ [eq (c xp) (c x); positive (c x)]) (eq (c x) (n 1));
  probe "array_exit" [a,ap] (and_ [arr_eq (c a) (c ap); positive (at a)]) (eq (at a) (n 0));
  probe "array_infinite" [a,ap] (and_ [arr_eq (c a) (c ap); positive (at a)]) (eq (at a) (n 1));
  probe "array_exit_reverse" [a,ap] (and_ [arr_eq (c ap) (c a); positive (at a)]) (eq (at a) (n 0));
  probe "array_copy" [a,ap;b,bp]
    (and_ [arr_eq (c a) (c ap); arr_eq (c bp) (mk_store srk (c a) (n 0) (n 7)); positive (at a)])
    (eq (at a) (n 0));
  probe "constant_step_terminates" [x,xp;k,kp]
    (and_ [eq (c kp) (c k); eq (c xp) (mk_add srk [c x;c k]); positive (c x)])
    (and_ [eq (c x) (n 3); eq (c k) (n (-1))]);
  probe "constant_step_infinite" [x,xp;k,kp]
    (and_ [eq (c kp) (c k); eq (c xp) (mk_add srk [c x;c k]); positive (c x)])
    (and_ [eq (c x) (n 3); eq (c k) (n 0)])
