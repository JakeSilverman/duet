open Srk
open Syntax
open OUnit
module C = MakeSimplifyingContext ()
let srk = C.context
let n = mk_int srk
let x = mk_const srk (mk_symbol srk ~name:"x" `TyInt)
let y = mk_const srk (mk_symbol srk ~name:"y" `TyInt)
let r = mk_const srk (mk_symbol srk ~name:"r" `TyReal)
let a = mk_const srk (mk_symbol srk ~name:"a" `TyArr)
let eq = mk_eq srk
let le = mk_leq srk
let lt = mk_lt srk
let and_ = mk_and srk
let or_ = mk_or srk
let add x y = mk_add srk [x;y]
let mul k x = mk_mul srk [n k;x]
let simplify = BoundSimplify.simplify srk
let equivalent x y =
  let solver = SrkZ3.mk_solver ~context:(Z3.mk_context [("timeout","3000")]) srk in
  SrkZ3.Solver.add solver [or_ [and_ [x;mk_not srk y];and_ [y;mk_not srk x]]];
  assert_equal `Unsat (SrkZ3.Solver.check solver [])
let case name input expected = name >:: (fun () ->
  let result = simplify input in equivalent input result; equivalent expected result)

let cases = [
  case "opposing variable bounds" (and_ [le x y;le y x]) (eq x y);
  case "opposing zero bounds" (and_ [le (n 0) x;le x (n 0)]) (eq x (n 0));
  case "affine scaling" (and_ [le (add (mul 2 x) (n 2)) (mul 2 y);le y (add x (n 1))]) (eq (add x (n 1)) y);
  case "collect repeated variables" (and_ [le (add x x) (mul 2 y);le y x]) (eq x y);
  case "strict opposite lower" (and_ [lt x y;le y x]) (mk_false srk);
  case "strict opposite upper" (and_ [le x y;lt y x]) (mk_false srk);
  case "both strict" (and_ [lt x y;lt y x]) (mk_false srk);
  case "same direction stronger bound" (and_ [le x y;lt (mul 2 x) (mul 2 y)]) (lt x y);
  case "same direction weaker last" (and_ [lt x y;le (mul 2 x) (mul 2 y)]) (lt x y);
  case "third strict after equality" (and_ [le x y;le y x;lt (mul 2 x) (mul 2 y)]) (mk_false srk);
  case "third weak after equality" (and_ [le x y;le y x;le (mul 3 x) (mul 3 y)]) (eq x y);
  case "different offsets stay different" (and_ [le (n 0) x;le x (n 1)]) (and_ [le (n 0) x;le x (n 1)]);
  case "different branches stay independent" (or_ [le x y;le y x]) (mk_true srk);
  case "real opposing bounds" (and_ [le (n 0) r;le r (n 0)]) (eq r (n 0));
  case "fractional bound on integer" (and_ [le (mk_real srk (QQ.of_frac 1 2)) x;le x (mk_real srk (QQ.of_frac 1 2))]) (mk_false srk);
  case "nonlinear atom is not a variable" (and_ [le (mk_mul srk [x;y]) (n 0);le (n 0) (mk_mul srk [x;y])]) (eq (mk_mul srk [x;y]) (n 0));
  case "array read atom" (and_ [le (mk_select srk a x) y;le y (mk_select srk a x)]) (eq (mk_select srk a x) y);
  case "different array reads remain independent" (and_ [le (mk_select srk a x) y;le y (mk_select srk a (add x (n 1)))]) (and_ [le (mk_select srk a x) y;le y (mk_select srk a (add x (n 1)))]);
  case "negated conjunction" (mk_not srk (and_ [le x y;le y x])) (mk_not srk (eq x y));
  case "nested binders are separate scopes"
    (mk_exists srk `TyInt (and_ [le (n 0) (mk_var srk 0 `TyInt);mk_exists srk `TyInt (lt (mk_var srk 0 `TyInt) (n 0))])) (mk_true srk);
  "bound identity removes existential" >:: (fun () ->
    let v = mk_var srk 0 `TyInt in
    let result = Quantifier.eq_guided_elim_loop srk (mk_exists srk `TyInt (and_ [le (n 0) v;le v (n 0);lt v y])) in
    equivalent result (lt (n 0) y);
    let has_quantifier = Formula.eval srk (function
      | `Quantify _ -> true
      | `And xs | `Or xs -> List.exists (fun x -> x) xs
      | `Not x -> x
      | `Ite (a,b,c) -> a || b || c
      | _ -> false) result in
    assert_bool "Expected the existential to be removed" (not has_quantifier))
]

let family = List.concat (List.map (fun scale ->
  List.concat (List.map (fun offset ->
    List.map (fun strict ->
      let lhs = add (mul scale x) (n (scale*offset)) in
      let rhs = mul scale y in
      let bound = if strict then lt else le in
      let input = and_ [bound lhs rhs;le y (add x (n offset))] in
      case (Printf.sprintf "scaled opposite %d %d %b" scale offset strict) input
        (if strict then mk_false srk else eq (add x (n offset)) y)) [false;true]) [-2;0;3])) [1;2;3])

let () = ignore (run_test_tt_main ("Cheap opposing-bound identities" >::: (cases @ family)))
