open Srk
open Syntax
open OUnit
module C = MakeSimplifyingContext ()
let srk=C.context
let n=mk_int srk
let x=mk_symbol srk ~name:"x" `TyInt
let y=mk_symbol srk ~name:"y" `TyInt
let a=mk_symbol srk ~name:"a" `TyArr
let t=mk_symbol srk ~name:"t" `TyArr
let c=mk_const srk
let eq = mk_eq srk
let conj = mk_and srk
let disj = mk_or srk
let truth=mk_true srk
let falsity=mk_false srk
let equivalent p q =
  let different=disj [conj [p;mk_not srk q];conj [mk_not srk p;q]] in
  assert_bool "Equivalence check failed" (Smt.is_sat srk different = `Unsat)
let store = mk_store srk (c a) (c x) (n 7)
let cases = [
 "constant addition", eq (mk_add srk [n 1;n (-1)]) (n 0),truth;
 "symbol plus constants",eq (mk_add srk [c x;n 3;n (-3)]) (c x),truth;
 "duplicates",conj [eq (c x) (n 2);eq (c x) (n 2)],eq (c x) (n 2);
 "disjunction duplicates",disj [eq (c x) (n 2);eq (c x) (n 2)],eq (c x) (n 2);
 "reflexive order",mk_leq srk (c x) (c x),truth;
 "strict reflexive order",mk_lt srk (c x) (c x),falsity;
 "contradictory constants",eq (mk_add srk [n 2;n (-1)]) (n 0),falsity;
 "defined array",mk_exists_const srk t (conj [mk_arr_eq srk (c t) store;eq (mk_select srk (c t) (c x)) (n 7)]),eq (mk_select srk store (c x)) (n 7);
 "capture avoidance",mk_forall_const srk x (mk_exists_const srk t (conj [mk_arr_eq srk (c t) store;mk_forall_const srk y (eq (mk_select srk (c t) (c y)) (mk_select srk store (c y)))])),truth
]
let () = ignore (run_test_tt_main ("Bounded cleanup" >::: (
 List.map (fun (name,p,want) -> name >:: fun () ->
   let q=RuntimeSimplify.cleanup srk p in equivalent p q; equivalent q want) cases
 @ ["multiple definitions are not expanded" >:: (fun () ->
   let p=mk_exists_const srk t (conj [disj [mk_arr_eq srk (c t) store;mk_arr_eq srk (c t) (c a)];eq (mk_select srk (c t) (n 0)) (n 9)]) in
   let q=RuntimeSimplify.cleanup srk p in
   equivalent p q;
   assert_bool "Lost existential array" (match Formula.destruct srk q with `Quantify (`Exists,_,`TyArr,_) -> true | _ -> false));
   "self reference retained" >:: (fun () ->
   let p=mk_exists_const srk t (mk_arr_eq srk (c t) (mk_store srk (c t) (n 0) (n 7))) in
   let q=RuntimeSimplify.cleanup srk p in
   assert_bool "Eliminated recursive definition" (Expr.equal p q))])))
