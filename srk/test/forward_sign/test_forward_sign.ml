open Srk
open Syntax
open OUnit

module Ctx = MakeSimplifyingContext ()
module Chc = Chc.Make(Ctx)
open Chc
module Sign = Fp.ForwardSign
let srk = Ctx.context
let v i = mk_var srk i `TyInt
let n = mk_int srk
let eq = mk_eq srk
let and_ = mk_and srk
let prop name types =
  Proposition.mk_proposition
    (mk_symbol srk ~name (`TyFun (types, `TyBool)))
    (List.mapi (fun i _ -> "v" ^ string_of_int i) types)
let unary name = prop name [`TyInt]
let inv report p = List.assoc (Proposition.symbol_of p) report.Sign.invariants
let infer fp =
  let r = Sign.infer ~timeout_ms:500 ~max_seconds:30. fp in
  assert_bool r.Sign.reason r.Sign.validated; r
let equivalent a b =
  let ground = Memo.memo (fun (_, typ) -> mk_symbol srk (typ :> typ)) in
  let close = substitute srk (fun x -> mk_const srk (ground x)) in
  assert_equal `Unsat (Smt.is_sat srk
    (close (mk_or srk [and_ [a; mk_not srk b]; and_ [b; mk_not srk a]])))
let loop ?(initial=0) ?(step=1) () =
  let p = unary "loop" and bad = prop "bad" [] in
  let fp = Fp.empty
    |> fun fp -> Fp.add_rule fp p [] (eq (v 0) (n initial))
    |> fun fp -> Fp.add_rule fp p [p] (eq (v 0) (mk_add srk [v 1; n step]))
    |> fun fp -> Fp.add_rule fp bad [p] (mk_lt srk (v 0) (n 0))
    |> fun fp -> Fp.add_query fp (Proposition.symbol_of bad) in
  fp, p, bad

(* Exact copy of the old read abstraction, for demonstrating its scope bug.
   This helper is never linked into the production analysis. *)
let legacy_over_approx_arrays phi =
  let nums = Memo.memo (fun _ -> mk_symbol srk `TyReal) in
  let bools = Memo.memo (fun _ -> mk_symbol srk `TyBool) in
  let mk_op = function `Eq -> mk_eq | `Lt -> mk_lt | `Leq -> mk_leq in
  let arith_alg = function
    | `Select (a, i) -> mk_const srk (nums (`Select (a, i)))
    | t -> ArithTerm.construct srk t in
  let alg = function
    | `Atom (`Arith (op, x, y)) ->
      mk_op op srk (ArithTerm.eval srk arith_alg x) (ArithTerm.eval srk arith_alg y)
    | `Atom (`ArrEq (a, b)) -> mk_const srk (bools (`Atom (`ArrEq (a, b))))
    | f -> Formula.construct srk f in
  Formula.eval srk alg phi

let quantified_read universal =
  let a = mk_const srk (mk_symbol srk `TyArr) in
  let read = mk_select srk a (v 0) in
  if universal then mk_forall srk `TyInt
    (mk_if srk (mk_or srk [eq (v 0) (n 0);eq (v 0) (n 1)]) (eq read (v 0)))
  else and_ [mk_exists srk `TyInt (eq read (n 0));
             mk_exists srk `TyInt (eq read (n 1))]

let scope_case universal =
  let phi = quantified_read universal in
  assert_equal `Sat (Smt.is_sat srk phi);
  assert_equal `Unsat (Smt.is_sat srk (legacy_over_approx_arrays phi));
  let p = unary "negative_witness" and bad = prop "reachable_error" [] in
  let fp = Fp.empty
    |> fun fp -> Fp.add_rule fp p [] (and_ [phi; eq (v 0) (n (-1))])
    |> fun fp -> Fp.add_rule fp bad [p] (mk_lt srk (v 0) (n 0)) in
  let r = infer fp in
  equivalent (inv r p) (mk_lt srk (v 0) (n 0));
  equivalent (inv r bad) (mk_true srk)

let suite = "Checked CHC forward signs" >::: [
  "nonnegative counter" >:: (fun () ->
    let fp,p,bad = loop () in let r = infer fp in
    equivalent (inv r p) (mk_leq srk (n 0) (v 0));
    equivalent (inv r bad) (mk_false srk));
  "unsafe initial state" >:: (fun () ->
    let fp,_,bad = loop ~initial:(-1) () in
    equivalent (inv (infer fp) bad) (mk_true srk));
  "unsafe decrement" >:: (fun () ->
    let fp,p,bad = loop ~step:(-1) () in let r = infer fp in
    equivalent (inv r p) (mk_leq srk (v 0) (n 0));
    equivalent (inv r bad) (mk_true srk));
  "multiple entries and negative cycle" >:: (fun () ->
    let p = unary "joined" in
    let fp = Fp.empty
      |> fun fp -> Fp.add_rule fp p [] (eq (v 0) (n (-1)))
      |> fun fp -> Fp.add_rule fp p [] (eq (v 0) (n 1))
      |> fun fp -> Fp.add_rule fp p [p] (eq (v 0) (mk_neg srk (v 1))) in
    equivalent (inv (infer fp) p) (mk_not srk (eq (v 0) (n 0))));
  "argument permutation" >:: (fun () ->
    let p = prop "p" [`TyInt;`TyInt] and q = prop "q" [`TyInt;`TyInt] in
    let fp = Fp.empty
      |> fun fp -> Fp.add_rule fp p [] (and_ [eq (v 0) (n 1);eq (v 1) (n (-1))])
      |> fun fp -> Fp.add_rule fp q [p] (and_ [eq (v 0) (v 3);eq (v 1) (v 2)]) in
    equivalent (inv (infer fp) q) (and_ [mk_lt srk (v 0) (n 0);mk_lt srk (n 0) (v 1)]));
  "mixed sorts and different arities" >:: (fun () ->
    let p = prop "mixed" [`TyArr;`TyBool;`TyReal;`TyInt] and q = unary "target" in
    let fp = Fp.empty
      |> fun fp -> Fp.add_rule fp p []
        (and_ [eq (mk_var srk 2 `TyReal) (mk_real srk (QQ.of_string "1/2"));eq (v 3) (n (-1))])
      |> fun fp -> Fp.add_rule fp q [p] (eq (v 0) (v 4)) in
    equivalent (inv (infer fp) q) (mk_lt srk (v 0) (n 0)));
  "unconstrained successor loses sign" >:: (fun () ->
    let p = unary "positive" and q = unary "havoc" in
    let fp = Fp.empty
      |> fun fp -> Fp.add_rule fp p [] (eq (v 0) (n 1))
      |> fun fp -> Fp.add_rule fp q [p] (mk_true srk) in
    equivalent (inv (infer fp) q) (mk_true srk));
  "dead SCC cannot hide live error" >:: (fun () ->
    let fp,_,bad = loop ~initial:(-1) () in let dead = unary "dead" in
    let fp = Fp.add_rule fp dead [dead] (eq (v 0) (v 1)) in
    let r = infer fp in equivalent (inv r dead) (mk_false srk);
    equivalent (inv r bad) (mk_true srk));
  "infeasible guard" >:: (fun () ->
    let p = unary "p" and q = unary "q" in
    let fp = Fp.empty
      |> fun fp -> Fp.add_rule fp p [] (eq (v 0) (n 1))
      |> fun fp -> Fp.add_rule fp q [p] (and_ [eq (v 0) (v 1);mk_lt srk (v 1) (n 0)]) in
    equivalent (inv (infer fp) q) (mk_false srk));
  "all nonlinear predecessors participate" >:: (fun () ->
    let p = unary "p" and q = unary "q" and r = unary "r" in
    let fp = Fp.empty
      |> fun fp -> Fp.add_rule fp p [] (eq (v 0) (n 1))
      |> fun fp -> Fp.add_rule fp q [] (eq (v 0) (n (-1)))
      |> fun fp -> Fp.add_rule fp r [p;q] (eq (v 0) (mk_mul srk [v 1;v 2])) in
    equivalent (inv (infer fp) r) (mk_lt srk (v 0) (n 0)));
  "universal read scope regression" >:: (fun () -> scope_case true);
  "separate existential read scopes regression" >:: (fun () -> scope_case false);
  "array store read is retained" >:: (fun () ->
    let p = prop "store" [`TyArr;`TyInt] in
    let a = mk_var srk 0 `TyArr in
    let read = mk_select srk (mk_store srk a (n 0) (n (-1))) (n 0) in
    let fp = Fp.add_rule Fp.empty p [] (eq (v 1) read) in
    equivalent (inv (infer fp) p) (mk_lt srk (v 1) (n 0)));
  "bound and free index zero stay distinct" >:: (fun () ->
    let p = unary "p" in
    let phi = mk_exists srk `TyInt
      (and_ [eq (v 0) (n 1);eq (v 1) (mk_neg srk (v 0))]) in
    equivalent (inv (infer (Fp.add_rule Fp.empty p [] phi)) p) (mk_lt srk (v 0) (n 0)));
  "validator rejects invalid entry fact" >:: (fun () ->
    let fp,p,_ = loop ~initial:(-1) () in
    assert_bool "reject" (not (Sign.validate fp [Proposition.symbol_of p,mk_leq srk (n 0) (v 0)])));
  "validator rejects invalid loop fact" >:: (fun () ->
    let fp,p,_ = loop ~step:(-1) () in
    assert_bool "reject" (not (Sign.validate fp [Proposition.symbol_of p,mk_leq srk (n 0) (v 0)])));
  "budget exhaustion leaves every rule unchanged" >:: (fun () ->
    let fp,_,_ = loop () in let after,r = Sign.strengthen ~max_checks:0 fp in
    assert_bool "not validated" (not r.Sign.validated);
    assert_equal (Fp.get_rules fp) (Fp.get_rules after));
  "budget exhausted during validation discards partial facts" >:: (fun () ->
    let fp,_,_ = loop () in let r = infer fp in
    let after,r = Sign.strengthen ~max_checks:(r.Sign.checks-1) fp in
    assert_bool "not validated" (not r.Sign.validated);
    assert_equal (Fp.get_rules fp) (Fp.get_rules after));
  "annotation placements are equivalent rule by rule" >:: (fun () ->
    let fp,_,_ = loop () in
    let full,_ = Sign.strengthen ~annotation:`All fp in
    List.iter (fun annotation ->
      let small,r = Sign.strengthen ~annotation fp in
      assert_bool r.Sign.reason r.Sign.validated;
      List.iter2 (fun (_,_,a) (_,_,b) -> equivalent a b)
        (Fp.get_rules full) (Fp.get_rules small)) [`Pre;`Pruned]);
  "rule guard already implies the sign" >:: (fun () ->
    let p = unary "p" and q = unary "q" in
    let fp = Fp.empty
      |> fun fp -> Fp.add_rule fp p [] (eq (v 0) (n 1))
      |> fun fp -> Fp.add_rule fp q [p]
        (and_ [eq (v 0) (v 1);mk_lt srk (n 0) (v 1)]) in
    let small,r = Sign.strengthen fp in
    assert_bool r.Sign.reason r.Sign.validated;
    assert_equal 0 r.Sign.retained_atoms;
    List.iter2 (fun (_,_,a) (_,_,b) -> equivalent a b)
      (Fp.get_rules fp) (Fp.get_rules small));
  "useful sign is not pruned" >:: (fun () ->
    let p = unary "p" and q = unary "q" in
    let fp = Fp.empty
      |> fun fp -> Fp.add_rule fp p [] (eq (v 0) (n 1))
      |> fun fp -> Fp.add_rule fp q [p] (eq (v 0) (v 1)) in
    let small,r = Sign.strengthen fp in
    assert_bool r.Sign.reason r.Sign.validated;
    let _,_,phi = List.find (fun (_,body,_) -> body <> []) (Fp.get_rules small) in
    equivalent (substitute srk (fun _ -> n (-1)) phi) (mk_false srk));
  "pruning budget exhaustion retains all input signs" >:: (fun () ->
    let fp,_,_ = loop () in
    let pre,_ = Sign.strengthen ~annotation:`Pre fp in
    let small,r = Sign.strengthen ~prune_checks:0 fp in
    assert_bool r.Sign.reason r.Sign.validated;
    assert_equal 0 r.Sign.pruning_checks;
    List.iter2 (fun (_,_,a) (_,_,b) -> equivalent a b)
      (Fp.get_rules pre) (Fp.get_rules small));
  "exhaustive reachable states of finite systems are preserved" >:: (fun () ->
    (* Enumerate reachability independently on finite graphs; check each actual
       state against the inferred predicate and each actual transition against
       the strengthened rule. No abstract transfer is used as the oracle. *)
    for seed = 0 to 23 do
      let p = unary "finite" in
      let edges = List.init 9 (fun k -> (k/3-1,k mod 3-1,k))
        |> List.filter (fun (_,_,k) -> (seed*73+19) land (1 lsl k) <> 0) in
      let transition = List.map (fun (a,b,_) -> and_ [eq (v 1) (n a);eq (v 0) (n b)]) edges
        |> mk_or srk in
      let initial = seed mod 3 - 1 in
      let fp = Fp.add_rule (Fp.add_rule Fp.empty p [] (eq (v 0) (n initial))) p [p] transition in
      let reached = ref [initial] and changed = ref true in
      while !changed do
        changed := false;
        List.iter (fun (a,b,_) -> if List.mem a !reached && not (List.mem b !reached)
          then (changed := true;reached := b :: !reached)) edges
      done;
      let after,r = Sign.strengthen ~timeout_ms:500 ~max_seconds:30. fp in
      assert_bool r.Sign.reason r.Sign.validated;
      List.iter (fun value -> equivalent
        (substitute srk (fun _ -> n value) (inv r p)) (mk_true srk)) !reached;
      List.iter (fun (head,body,phi) ->
        if body <> [] then List.iter (fun (a,b,_) ->
          if List.mem a !reached then equivalent
            (substitute srk (fun (i,_) -> n (if i=0 then b else a)) phi) (mk_true srk)) edges
        else equivalent (substitute srk (fun _ -> n initial) phi) (mk_true srk);
        ignore head) (Fp.get_rules after)
    done);
]

let () = ignore (run_test_tt_main suite)
