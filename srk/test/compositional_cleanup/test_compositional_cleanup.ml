open Srk
open Syntax
open OUnit
module C = MakeSimplifyingContext ()
let srk = C.context
let symbol name typ = mk_const srk (mk_symbol srk ~name typ)
let x = symbol "x" `TyInt
let y = symbol "y" `TyInt
let z = symbol "z" `TyInt
let r = symbol "r" `TyReal
let a = symbol "a" `TyArr
let b = symbol "b" `TyArr
let p = symbol "p" `TyBool
let q = symbol "q" `TyBool
let u = symbol "u" `TyBool
let f = mk_symbol srk ~name:"f" (`TyFun ([`TyInt], `TyInt))
let fr = mk_symbol srk ~name:"fr" (`TyFun ([`TyReal], `TyReal))
let n = mk_int srk
let frac i j = mk_real srk (QQ.of_frac i j)
let v i = mk_var srk i `TyInt
let add xs = mk_add srk xs
let mul xs = mk_mul srk xs
let sub = mk_sub srk
let neg = mk_neg srk
let eq = mk_eq srk
let le = mk_leq srk
let lt = mk_lt srk
let and_ = mk_and srk
let or_ = mk_or srk
let not_ = mk_not srk
let all = mk_forall srk `TyInt
let ex = mk_exists srk `TyInt
let truth = mk_true srk
let falsehood = mk_false srk
let clean = RuntimeSimplify.cheap srk
let equivalent before after =
  let solver = SrkZ3.mk_solver ~context:(Z3.mk_context [("timeout","3000")]) srk in
  let parameter=Memo.memo (fun (_,typ)->mk_const srk (mk_symbol srk (typ :> typ))) in
  let differs=or_ [and_ [before;not_ after];and_ [after;not_ before]] |> substitute srk parameter in
  SrkZ3.Solver.add solver [differs];
  assert_equal ~printer:(function `Sat->"SAT" | `Unsat->"UNSAT" | `Unknown->"UNKNOWN")
    `Unsat (SrkZ3.Solver.check solver [])
let check input =
  let _,symbols_before,named_before = context_stats srk in
  let output = clean input in
  let _,symbols_after,named_after = context_stats srk in
  assert_equal (symbols_before,named_before) (symbols_after,named_after);
  equivalent input output;
  assert_bool "Cleanup must be idempotent" (Expr.equal output (clean output));
  output
let case name input expected = name >:: (fun () ->
  let output = check input in equivalent expected output)
let canonical name lhs rhs = name >:: (fun () ->
  let lhs=check lhs and rhs=check rhs in
  assert_bool "Expected the same canonical formula" (Expr.equal lhs rhs))
let retained_branch name input expected branch = name >:: (fun () ->
  let output = check input in
  equivalent expected output;
  let children = match Formula.destruct srk output with
    | `And children | `Or children -> children
    | _ -> assert_failure "Expected the outer Boolean connective to remain" in
  assert_bool "Redundant alternative must remain without absorption"
    (List.exists (Expr.equal (clean branch)) children);
  assert_bool "Absorption must not collapse the formula"
    (not (Expr.equal output (clean expected))))
let cases = [
  case "real division keeps a real numerator" (eq (mk_div srk (add [r;neg r;n 1]) y) (frac 1 2)) (eq (mk_div srk (add [r;neg r;n 1]) y) (frac 1 2));
  case "real division keeps a real denominator" (eq (mk_div srk x (add [r;neg r;n 2])) (frac 1 2)) (eq (mk_div srk x (add [r;neg r;n 2])) (frac 1 2));
  case "floor keeps a real operand" (eq (mk_floor srk (add [r;neg r;n 1])) x) (eq x (n 1));
  canonical "open transition parameters" (eq (v 0) (add [v 2;n 1])) (eq (v 2) (add [v 0;n (-1)]));
  canonical "nested conjunction duplicates" (and_ [p;and_ [q;p];q]) (and_ [q;p]);
  canonical "nested disjunction duplicates" (or_ [p;or_ [q;p];q]) (or_ [q;p]);
  canonical "commutative conjunctions" (or_ [and_ [p;q];and_ [q;p]]) (and_ [q;p]);
  canonical "commutative disjunctions" (and_ [or_ [p;q];or_ [q;p]]) (or_ [q;p]);
  retained_branch "conjunction retains redundant disjunction"
    (and_ [p;or_ [p;q]]) p (or_ [p;q]);
  retained_branch "disjunction retains redundant conjunction"
    (or_ [p;and_ [p;q]]) p (and_ [p;q]);
  retained_branch "strict bound retains redundant disequality"
    (and_ [lt x y;or_ [lt x y;lt y x]]) (lt x y) (or_ [lt x y;lt y x]);
  case "absorption does not invent a sibling" (and_ [or_ [p;q];or_ [p;u]]) (and_ [or_ [p;q];or_ [p;u]]);
  case "negation retained" (and_ [p;not_ p]) falsehood;
  case "neutral conjunction" (and_ [p;truth]) p;
  case "neutral disjunction" (or_ [p;falsehood]) p;
  case "absorbing conjunction" (and_ [p;falsehood]) falsehood;
  case "absorbing disjunction" (or_ [p;truth]) truth;
  canonical "nested addition" (eq (add [n 1;add [n (-1);x]]) y) (eq x y);
  canonical "negated difference" (eq (neg (sub x y)) z) (eq (sub y x) z);
  case "arithmetic reflexivity" (eq x (add [n (-1);add [n 1;x]])) truth;
  canonical "opposite equality presentations" (and_ [eq (sub (n 1) x) (n 0);eq (sub x (n 1)) (n 0)]) (eq x (n 1));
  canonical "collected coefficients" (eq (add [x;y;x;neg y]) z) (eq (mul [n 2;x]) z);
  canonical "scaled sum" (eq (mul [n 3;add [x;y]]) z) (eq (add [mul [n 3;x];mul [n 3;y]]) z);
  canonical "constant multiplication" (eq (add [mul [n 2;n 3];x]) y) (eq (add [n 6;x]) y);
  case "strict cancellation true" (lt x (add [x;n 1])) truth;
  case "strict cancellation false" (lt x x) falsehood;
  case "nonstrict cancellation" (le (add [x;n 1]) x) falsehood;
  case "integer parity retained" (ex (eq (mul [n 2;v 0]) (n 1))) falsehood;
  case "integer divisibility parameter retained" (ex (eq (mul [n 2;v 0]) y)) (ex (eq (mul [n 2;v 0]) y));
  canonical "rational constants" (eq (add [frac 1 2;r;frac (-1) 2]) x) (eq r x);
  canonical "real coefficients" (eq (add [mul [frac 1 2;r];mul [frac 3 2;r]]) x) (eq (mul [n 2;r]) x);
  case "real binder stays real" (mk_exists srk `TyReal (eq (mk_var srk 0 `TyReal) (frac 1 2))) truth;
  case "integer binder stays integer" (ex (eq (v 0) (frac 1 2))) falsehood;
  case "real function argument cancellation" (eq (mk_app srk fr [add [r;neg r]]) (mk_app srk fr [n 0])) truth;
  canonical "uninterpreted function argument" (eq (mk_app srk f [add [x;n 1;n (-1)]]) y) (eq (mk_app srk f [x]) y);
  case "different function arguments remain distinct" (eq (mk_app srk f [x]) (mk_app srk f [y])) (eq (mk_app srk f [x]) (mk_app srk f [y]));
  canonical "array index cancellation" (eq (mk_select srk a (add [n 1;add [n (-1);x]])) y) (eq (mk_select srk a x) y);
  case "different array identities remain distinct" (eq (mk_select srk a x) (mk_select srk b x)) (eq (mk_select srk a x) (mk_select srk b x));
  case "array store equivalence" (mk_arr_eq srk (mk_store srk a (add [x;n 1;n (-1)]) y) (mk_store srk a x y)) truth;
  case "nonlinear cancellation" (eq (sub (mul [x;y]) (mul [x;y])) (n 0)) truth;
  case "nonlinear products not linearized" (eq (mul [x;y]) z) (eq (mul [x;y]) z);
  case "symbolic division including zero" (eq (mk_div srk x y) (n 1)) (eq (mk_div srk x y) (n 1));
  case "division by zero not cancelled" (eq (mk_div srk x x) (n 1)) (eq (mk_div srk x x) (n 1));
  case "floor retained" (eq (mk_floor srk (mk_div srk x (n 2))) y) (eq (mk_floor srk (mk_div srk x (n 2))) y);
  case "modulo retained" (eq (mk_mod srk x (n 2)) y) (eq (mk_mod srk x (n 2)) y);
  case "arithmetic ITE" (eq (mk_ite srk p (add [x;n 1;n (-1)]) y) z) (eq (mk_ite srk p x y) z);
  case "nested scopes remain distinct" (ex (and_ [eq (v 0) (n 0);all (eq (v 0) (n 0))])) falsehood;
  case "outer variable reference preserved" (all (ex (eq (add [v 0;n 1;n (-1)]) (v 1)))) truth;
  case "quantifier order preserved" (ex (all (eq (v 0) (v 1)))) falsehood;
  case "universal equality remains false" (all (eq (add [v 0;n 1;n (-1)]) (n 0))) falsehood;
  case "no cross-branch facts" (or_ [eq x (n 0);and_ [eq x (n 1);lt x y]]) (or_ [eq x (n 0);and_ [eq x (n 1);lt (n 1) y]]);
  "bounds cooperate with identities" >:: (fun () ->
    let phi=ex (and_ [le (n 0) (v 0);and_ [le (add [n 1;add [n (-1);v 0]]) (n 0);lt (v 0) y]]) in
    let result=Quantifier.eq_guided_elim_loop srk phi in equivalent phi result;
    assert_bool "Expected quantified variable to disappear" (Hashtbl.length (free_vars result)=0 && match Formula.destruct srk result with `Quantify _->false | _->true);
    equivalent result (lt (n 0) y));
  "temporary array definition exposed" >:: (fun () ->
    let array=mk_var srk 0 `TyArr in
    let store=mk_store srk a x y in
    let phi=mk_exists srk `TyArr (and_ [mk_arr_eq srk array store;and_ [mk_arr_eq srk array store;eq (mk_select srk array x) y]]) in
    let result=RuntimeSimplify.cleanup srk phi in equivalent phi result;equivalent result truth);
  "free symbol identity despite repeated name" >:: (fun () ->
    let x1=symbol "same" `TyInt and x2=symbol "same" `TyInt in
    let phi=eq x1 x2 in let output=check phi in
    assert_bool "Distinct free symbols must not merge" (Symbol.Set.cardinal (symbols output)=2));
]
let generated = "300 generated quantifier-free equivalence checks" >:: (fun () ->
  let random=Random.State.make [|710;2026|] in
  let choose xs=List.nth xs (Random.State.int random (List.length xs)) in
  let rec term depth =
    if depth=0 then choose [x;y;z;n 0;n 1;n (-1)] else
    match Random.State.int random 8 with
    | 0 -> add [term (depth-1);term (depth-1)]
    | 1 -> neg (term (depth-1))
    | 2 -> mul [n (Random.State.int random 5-2);term (depth-1)]
    | 3 -> mk_select srk a (term (depth-1))
    | 4 -> mk_app srk f [term (depth-1)]
    | 5 -> mk_mod srk (term (depth-1)) (n 3)
    | 6 -> mul [term 0;term 0]
    | _ -> term 0 in
  let atom () = (choose [eq;le;lt]) (term 2) (term 2) in
  for _=1 to 300 do
    let a=atom () and b=atom () and c=atom () in
    let phi=choose [and_ [a;and_ [b;a];or_ [a;c]];
      or_ [a;or_ [b;a];and_ [a;c]];
      not_ (and_ [a;or_ [b;c]]);
      and_ [or_ [a;b];or_ [b;a];c]] in
    ignore (check phi)
  done)
let () = ignore (run_test_tt_main ("Compositional equivalence-preserving cleanup" >::: (cases@[generated])))
