open Srk
open Syntax
open OUnit

module Ctx = MakeSimplifyingContext ()
let srk = Ctx.context
let c = mk_const srk
let n = mk_int srk
let a = mk_symbol srk ~name:"A" `TyArr
let b = mk_symbol srk ~name:"B" `TyArr
let t = mk_symbol srk ~name:"temporary" `TyArr
let u = mk_symbol srk ~name:"other_temporary" `TyArr
let x = mk_symbol srk ~name:"x" `TyInt
let y = mk_symbol srk ~name:"y" `TyInt
let guard = mk_leq srk (c x) (n 2)
let store value = mk_store srk (c a) (n 0) (n value)
let first value = mk_arr_eq srk (c t) (store value)
let rest = mk_arr_eq srk (c b) (mk_store srk (c t) (n 1) (n 5))
let quantify phi = mk_exists_const srk t phi
let conditional = mk_or srk [mk_and srk [guard; first 2];
                            mk_and srk [mk_not srk guard; first 0]]

let count_arrays phi =
  Formula.eval srk (function
    | `Quantify (_, _, `TyArr, count) -> count + 1
    | `Quantify (_, _, _, count) | `Not count -> count
    | `And counts | `Or counts -> List.fold_left (+) 0 counts
    | `Ite (a, b, c) -> a + b + c
    | _ -> 0) phi

let assert_equivalent a b =
  if not (Expr.equal a b) then
    let differs = mk_or srk [mk_and srk [a; mk_not srk b];
                            mk_and srk [b; mk_not srk a]] in
    match Smt.is_sat srk differs with
    | `Unsat -> ()
    | `Sat -> assert_failure "Formulas are not equivalent"
    | `Unknown -> assert_failure "Equivalence check inconclusive"

let cases = [
  "unconditional", quantify (mk_and srk [first 2; rest]), 0;
  "conditional", quantify (mk_and srk [conditional; rest]), 0;
  "conflicting definitions", quantify (mk_and srk [first 2; first 3; rest]), 0;
  "overlapping branches", quantify (mk_and srk [mk_or srk [first 2; first 0]; rest]), 0;
  "branch without definition", quantify (mk_and srk [mk_or srk [first 2; guard]; rest]), 1;
  "self-reference", quantify (mk_and srk [
    mk_arr_eq srk (c t) (mk_store srk (c t) (n 0) (n 7)); rest]), 1;
  "negated existential", mk_not srk (quantify (mk_and srk [conditional; rest])), 0;
  "read through temporary", quantify (mk_and srk [conditional;
    mk_arr_eq srk (c b) (mk_store srk (c t) (n 1) (mk_select srk (c t) (n 0)))]), 0;
  "same write index", quantify (mk_and srk [conditional;
    mk_arr_eq srk (c b) (mk_store srk (c t) (n 0) (n 9))]), 0;
  "outer universal index", mk_forall_const srk x (quantify (mk_and srk [
    mk_arr_eq srk (c t) (mk_store srk (c a) (c x) (n 7)); rest])), 0;
  "outer existential array", mk_exists_const srk a
    (quantify (mk_and srk [conditional; rest])), 1;
  "two intermediate arrays", quantify (mk_and srk [conditional;
    mk_exists_const srk u (mk_and srk [
      mk_arr_eq srk (c u) (mk_store srk (c t) (n 1) (n 9));
      mk_arr_eq srk (c b) (mk_store srk (c u) (n 2) (n 4))])]), 0;
  "candidate limit", quantify (mk_and srk [mk_or srk (List.init 9 first); rest]), 1;
  "false body", quantify (mk_false srk), 0;
  "universal untouched", mk_forall_const srk t
    (mk_or srk [mk_not srk (first 2); rest]), 1;
]

let read_equal array index =
  mk_eq srk (mk_select srk array index) (mk_select srk (c b) index)

let capture_avoidance () =
  let replacement = mk_store srk (c a) (c x) (n 7) in
  let original = mk_forall_const srk x (quantify (mk_and srk [
    mk_arr_eq srk (c t) replacement;
    mk_forall_const srk y (read_equal (c t) (c y))])) in
  let expected = mk_forall_const srk x
    (mk_forall_const srk y (read_equal replacement (c y))) in
  assert_bool "Outer index captured by inner universal"
    (Expr.equal (TempElim.eliminate srk original) expected)

let conditional_inner_read () =
  let original = quantify (mk_and srk [conditional;
    mk_forall_const srk y (read_equal (c t) (c y))]) in
  (* Independent expected result, using array extensionality. *)
  let expected = mk_or srk [
    mk_and srk [guard; mk_arr_eq srk (store 2) (c b)];
    mk_and srk [mk_not srk guard; mk_arr_eq srk (store 0) (c b)]] in
  assert_equivalent (TempElim.eliminate srk original) expected

let suite = "Conditional array temporaries" >::: (
  List.map (fun (name, original, expected_count) -> name >:: fun () ->
    let transformed = TempElim.eliminate srk original in
    assert_equal ~printer:string_of_int expected_count (count_arrays transformed);
    assert_equivalent original transformed) cases
  @ ["capture avoidance" >:: capture_avoidance;
     "conditional inner read" >:: conditional_inner_read])

let () = ignore (run_test_tt_main suite)
