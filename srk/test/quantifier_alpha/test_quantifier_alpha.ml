open Srk
open Syntax
open OUnit
module C = MakeSimplifyingContext ()
let srk = C.context
let v i = mk_var srk i `TyInt
let body = mk_lt srk (v 0) (mk_int srk 7)
let same a b = assert_equal 0 (Expr.compare a b)
let different a b = assert_bool "distinct formulas must not share an identity" (Expr.compare a b <> 0)
let many_names mk =
  let first = mk "reference" in
  for i = 0 to 63 do same first (mk ("renamed_" ^ string_of_int i)) done
let suite = "Quantifier alpha identity" >::: [
  "existential names" >:: (fun () -> many_names (fun name -> mk_exists srk ~name `TyInt body));
  "universal names" >:: (fun () -> many_names (fun name -> mk_forall srk ~name `TyInt body));
  "array names" >:: (fun () ->
    let a = mk_var srk 0 `TyArr in
    let p = mk_eq srk (mk_select srk a (mk_int srk 0)) (mk_int srk 7) in
    many_names (fun name -> mk_exists srk ~name `TyArr p));
  "nested names" >:: (fun () ->
    let p = mk_lt srk (v 1) (v 0) in
    same (mk_exists srk ~name:"outer_a" `TyInt (mk_forall srk ~name:"inner_a" `TyInt p))
         (mk_exists srk ~name:"outer_b" `TyInt (mk_forall srk ~name:"inner_b" `TyInt p)));
  "quantifier kind preserved" >:: (fun () -> different (mk_exists srk `TyInt body) (mk_forall srk `TyInt body));
  "bound types preserved" >:: (fun () -> different (mk_exists srk `TyInt (mk_true srk)) (mk_exists srk `TyArr (mk_true srk)));
  "bound indices preserved" >:: (fun () ->
    different (mk_exists srk `TyInt (mk_lt srk (v 0) (v 1)))
              (mk_exists srk `TyInt (mk_lt srk (v 1) (v 0))));
  "free symbols preserved" >:: (fun () ->
    let a = mk_const srk (mk_symbol srk ~name:"a" `TyInt) in
    let b = mk_const srk (mk_symbol srk ~name:"b" `TyInt) in
    different (mk_exists srk `TyInt (mk_eq srk (v 0) a)) (mk_exists srk `TyInt (mk_eq srk (v 0) b)));
]
let () = ignore (run_test_tt_main suite)
