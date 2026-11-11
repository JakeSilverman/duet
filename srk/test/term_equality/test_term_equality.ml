open Srk
open Syntax
open OUnit

module C = MakeSimplifyingContext ()
module Chc = Chc.Make(C)
let srk = C.context
let c = mk_const srk
let n = mk_int srk
let eq = mk_eq srk
let ae = mk_arr_eq srk
let and_ = mk_and srk
let pair name typ = mk_symbol srk ~name typ, mk_symbol srk ~name:(name ^ "_post") typ
let x, xp = pair "x" `TyInt
let k, kp = pair "k" `TyInt
let a, ap = pair "a" `TyArr
let b, bp = pair "b" `TyArr
let at a = mk_select srk (c a) (n 0)
let pos term = mk_lt srk (n 0) term
let scalar = and_ [eq (c xp) (c x); pos (c x)]
let array = and_ [ae (c a) (c ap); pos (at a)]
let step = and_ [eq (c kp) (c k); eq (c xp) (mk_add srk [c x;c k]); pos (c x)]

let check expected phi =
  let solver = SrkZ3.mk_solver ~context:(Z3.mk_context [("timeout", "2000")]) srk in
  SrkZ3.Solver.add solver [phi];
  assert_equal expected (SrkZ3.Solver.check solver [])

(* Each SAT case has a concrete infinite execution; each UNSAT case terminates. *)
let cases = [
  "scalar zero-trip", `Unsat, [x,xp], scalar, eq (c x) (n 0), [xp];
  "scalar stutter", `Sat, [x,xp], scalar, eq (c x) (n 1), [xp];
  "array zero-trip", `Unsat, [a,ap], array, eq (at a) (n 0), [ap];
  "array stutter", `Sat, [a,ap], array, eq (at a) (n 1), [ap];
  "reverse array equality", `Unsat, [a,ap], and_ [ae (c ap) (c a); pos (at a)], eq (at a) (n 0), [ap];
  "copy from unchanged array", `Unsat, [a,ap;b,bp],
    and_ [ae (c a) (c ap); ae (c bp) (mk_store srk (c a) (n 0) (n 7)); pos (at a)], eq (at a) (n 0), [ap];
  "fixed negative step", `Unsat, [x,xp;k,kp], step,
    and_ [eq (c x) (n 3); eq (c k) (n (-1))], [kp];
  "fixed zero step", `Sat, [x,xp;k,kp], step,
    and_ [eq (c x) (n 3); eq (c k) (n 0)], [kp];
  "unconditional stutter", `Sat, [x,xp], eq (c xp) (c x), mk_true srk, [xp];
  "different state variables", `Sat, [x,xp;k,kp],
    and_ [eq (c k) (c x); eq (c xp) (mk_add srk [c x;n 1]); eq (c kp) (mk_add srk [c k;n 1])],
    and_ [eq (c x) (n 0); eq (c k) (n 0)], [];
  "branch can stutter forever", `Sat, [x,xp],
    and_ [pos (c x); mk_or srk [eq (c xp) (c x); eq (c xp) (mk_add srk [c x;n (-1)])]],
    eq (c x) (n 1), [];
  "changing step oscillates", `Sat, [x,xp;k,kp],
    and_ [pos (c x); eq (c xp) (mk_add srk [c x;c k]); eq (c kp) (mk_neg srk (c k))],
    and_ [eq (c x) (n 3); eq (c k) (n 1)], []
]

let direct enabled (name,expected,trs,phi,init,eliminated) =
  (name ^ if enabled then " enabled" else " disabled") >:: (fun () ->
    Pmfa.OldPmfa.use_termination_equality_opt := enabled;
    let result = Pmfa.OldPmfa.mp srk (TransitionFormula.make phi trs) in
    if enabled then List.iter (fun sym ->
      assert_bool "Eliminated post-state representative escaped" (not (Symbol.Set.mem sym (symbols result)))) eliminated;
    check expected (and_ [init;result]))

let pd = (module Pmfa.OldPmfa.Array_analysis
    (Iteration.Product(Iteration.LossyTranslation)(Iteration.PolyhedronGuard))
    (Iteration.Product(Iteration.GuardedTranslation)(Iteration.PolyhedronGuard)) : Iteration.PreDomain)

let chc_test enabled signs typ initial =
  let name = Printf.sprintf "CHC %s initial=%d enabled=%b signs=%b"
      (if typ = `TyArr then "array" else "scalar") initial enabled signs in
  name >:: (fun () ->
    Pmfa.OldPmfa.use_termination_equality_opt := enabled;
    let rel = Chc.Proposition.mk_proposition
        (mk_symbol srk ~name:"Loop" (`TyFun ([typ], `TyBool))) ["state"] in
    let value i = let v = mk_var srk i typ in
      if typ = `TyArr then mk_select srk v (n 0) else Expr.arith_term_of srk v in
    let same = if typ = `TyArr then ae (mk_var srk 0 typ) (mk_var srk 1 typ)
      else eq (value 0) (value 1) in
    let fp = Chc.Fp.add_rule Chc.Fp.empty rel [] (eq (value 0) (n initial)) in
    let fp = Chc.Fp.add_rule fp rel [rel] (and_ [same;pos (value 1)]) in
    let fp = if signs then (
      let fp,report = Chc.Fp.ForwardSign.strengthen fp in
      assert_bool "Sign certificate" report.validated; fp) else fp in
    let result = Chc.Fp.query_vc_terminates fp pd in
    check (if initial = 0 then `Unsat else `Sat) result)

let suite = "Termination unchanged-state elimination" >::: (
  List.concat (List.map (fun enabled ->
    List.map (direct enabled) cases @
    List.concat (List.map (fun typ -> List.map (chc_test enabled false typ) [0;1]) [`TyInt;`TyArr])) [false;true]) @
  List.concat (List.map (fun typ -> List.map (chc_test true true typ) [0;1]) [`TyInt;`TyArr]))

let () = ignore (run_test_tt_main suite)
