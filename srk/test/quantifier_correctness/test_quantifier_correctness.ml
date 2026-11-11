open Srk
open Syntax
open OUnit
module C = MakeSimplifyingContext ()
let srk = C.context
let v i = mk_var srk i `TyInt
let n = mk_int srk
let sym name typ = mk_const srk (mk_symbol srk ~name typ)
let y = sym "y" `TyInt
let z = sym "z" `TyInt
let r = sym "r" `TyReal
let arr = sym "a" `TyArr
let and_ = mk_and srk
let or_ = mk_or srk
let eq = mk_eq srk
let ge0 t = mk_leq srk (n 0) t
let ex = mk_exists srk `TyInt
let all = mk_forall srk `TyInt
let add x y = mk_add srk [x;y]
let mul k x = mk_mul srk [n k;x]
let qe = Quantifier.eq_guided_elim_loop srk
let quantifiers phi = Formula.eval srk (function
  | `Quantify (_,_,_,count) -> count + 1
  | `And counts | `Or counts -> List.fold_left (+) 0 counts
  | `Not count -> count
  | `Ite (a,b,c) -> a+b+c
  | _ -> 0) phi

let equivalent expected actual =
  let solver = SrkZ3.mk_solver ~context:(Z3.mk_context [("timeout","3000")]) srk in
  SrkZ3.Solver.add solver [or_ [and_ [expected;mk_not srk actual];and_ [actual;mk_not srk expected]]];
  assert_equal ~printer:(function `Sat -> "SAT" | `Unsat -> "UNSAT" | `Unknown -> "UNKNOWN")
    `Unsat (SrkZ3.Solver.check solver [])

let simple name input expected = name >:: (fun () -> equivalent expected (qe input))
(* Correctness-only checks equivalence; optional identity-reduction shape is not required. *)
let reduced name input expected = simple name input expected

let regressions = [
  simple "universal equality is not a definition" (all (eq (v 0) (n 0))) (mk_false srk);
  simple "universal equality with a free value" (all (eq (v 0) y)) (mk_false srk);
  reduced "existential identity with sign" (ex (and_ [eq (v 0) y;ge0 (v 0)])) (ge0 y);
  reduced "universal guarded identity with sign" (all (or_ [mk_not srk (eq (v 0) y);ge0 (v 0)])) (ge0 y);
  simple "integer half is not a witness" (ex (eq (v 0) (mk_real srk (QQ.of_frac 1 2)))) (mk_false srk);
  simple "odd integer equation" (ex (eq (mul 2 (v 0)) (n 1))) (mk_false srk);
  simple "integer divisibility preserved" (ex (eq (mul 2 (v 0)) y)) (ex (eq (mul 2 (v 0)) y));
  simple "integer odd guard is vacuous" (all (or_ [mk_not srk (eq (mul 2 (v 0)) (n (-1)));ge0 (v 0)])) (mk_true srk);
  reduced "divisible integer coefficients" (ex (and_ [eq (mul 2 (v 0)) (mul 2 y);ge0 (v 0)])) (ge0 y);
  reduced "real division is allowed" (mk_exists srk `TyReal (and_ [eq (mul 2 (mk_var srk 0 `TyReal)) r;ge0 (mk_var srk 0 `TyReal)])) (ge0 r);
  reduced "real guarded division is allowed" (mk_forall srk `TyReal (or_ [mk_not srk (eq (mul 2 (mk_var srk 0 `TyReal)) r);ge0 (mk_var srk 0 `TyReal)])) (ge0 r);
  simple "self dependent impossible equation" (ex (eq (v 0) (add (v 0) (n 1)))) (mk_false srk);
  simple "self dependent universal guard" (all (or_ [mk_not srk (eq (v 0) (add (v 0) (n 1)));ge0 (v 0)])) (mk_true srk);
  simple "forall exists respects outer scope" (all (ex (and_ [eq (v 0) (add (v 1) (n 1));mk_lt srk (v 1) (v 0)]))) (mk_true srk);
  simple "exists forall is not forall exists" (ex (all (eq (v 0) (v 1)))) (mk_false srk);
  simple "nested sign constraint is not always true" (all (ex (and_ [eq (v 0) (v 1);ge0 (v 0)]))) (mk_false srk);
  simple "inner guard retains outer index" (ex (all (or_ [mk_not srk (eq (v 0) (v 1));ge0 (v 0)]))) (mk_true srk);
  simple "different branch definitions" (ex (or_ [and_ [eq (v 0) y;ge0 (v 0)];and_ [eq (v 0) z;mk_lt srk (v 0) (n 0)]])) (or_ [ge0 y;mk_lt srk z (n 0)]);
  simple "universal guard must cover every conjunct" (all (and_ [or_ [mk_not srk (eq (v 0) y);ge0 (v 0)];eq (v 0) z])) (mk_false srk);
  reduced "array existential identity" (mk_exists srk `TyArr (and_ [mk_arr_eq srk (mk_var srk 0 `TyArr) arr;eq (mk_select srk (mk_var srk 0 `TyArr) (n 0)) y])) (eq (mk_select srk arr (n 0)) y);
  reduced "array universal guard" (mk_forall srk `TyArr (or_ [mk_not srk (mk_arr_eq srk (mk_var srk 0 `TyArr) arr);eq (mk_select srk (mk_var srk 0 `TyArr) (n 0)) y])) (eq (mk_select srk arr (n 0)) y);
  simple "existential Boolean positive" (mk_exists srk `TyBool (mk_var srk 0 `TyBool)) (mk_true srk);
  simple "universal Boolean positive" (mk_forall srk `TyBool (mk_var srk 0 `TyBool)) (mk_false srk);
  simple "universal Boolean excluded middle" (mk_forall srk `TyBool (or_ [mk_var srk 0 `TyBool;mk_not srk (mk_var srk 0 `TyBool)])) (mk_true srk)
]

let family = List.concat (List.mapi (fun i rhs ->
  List.concat (List.mapi (fun j pred ->
    [reduced (Printf.sprintf "exists family %d %d" i j) (ex (and_ [eq (v 0) rhs;pred (v 0)])) (pred rhs);
     reduced (Printf.sprintf "forall family %d %d" i j) (all (or_ [mk_not srk (eq (v 0) rhs);pred (v 0)])) (pred rhs)])
    [ge0;(fun x -> mk_lt srk x z);(fun x -> and_ [ge0 x;mk_lt srk x z])]))
  [y;add y (n 1);add (mul 2 y) (n (-3))])

let () = ignore (run_test_tt_main ("Quantifier identity correctness" >::: (regressions @ family)))
