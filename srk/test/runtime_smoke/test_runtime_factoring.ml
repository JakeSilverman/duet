open Srk
open Syntax
open OUnit
module C=MakeSimplifyingContext ()
let srk=C.context
let p=mk_const srk (mk_symbol srk ~name:"p" `TyBool)
let q=mk_const srk (mk_symbol srk ~name:"q" `TyBool)
let r=mk_const srk (mk_symbol srk ~name:"r" `TyBool)
let disj=mk_or srk
let conj=mk_and srk
let clauses=[disj [p;q];disj [p;r];disj [q;r]]
let rec permutations = function
 | [] -> [[]]
 | xs -> List.concat (List.mapi (fun i x -> List.map (fun rest -> x::rest) (permutations (List.filteri (fun j _ -> i<>j) xs))) xs)
let mode phi=match Formula.destruct srk phi with
 | `And (first::_) -> (match Formula.destruct srk first with `Or (x::_) -> x | _ -> assert false)
 | _ -> assert false
let ()=ignore (run_test_tt_main ("Stable factoring" >::: [
 "permuted equal-score choices" >:: (fun () ->
   let baseline=mode (Quantifier.dumb_factor srk (conj clauses)) in
   List.iter (fun cs ->
     let input=conj cs in
     let result=Quantifier.dumb_factor srk input in
     assert_bool "Different tie selection" (Expr.equal baseline (mode result));
     let difference=disj [conj [input;mk_not srk result];conj [mk_not srk input;result]] in
     assert_bool "Factoring changed meaning" (Smt.is_sat srk difference=`Unsat)) (permutations clauses))
]))
