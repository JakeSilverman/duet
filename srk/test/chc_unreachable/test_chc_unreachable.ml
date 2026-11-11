open Srk
open Syntax
open OUnit

module Ctx = MakeSimplifyingContext ()
module Chc = Chc.Make(Ctx)
open Chc

let srk = Ctx.context
let v i = mk_var srk i `TyInt
let n = mk_int srk
let eq a b = mk_eq srk a b
let and_ = mk_and srk
let pd = (module Iteration.Product(Iteration.LossyTranslation)(Iteration.PolyhedronGuard)
          : Iteration.PreDomain)

let binary name =
  let symbol = mk_symbol srk ~name (`TyFun ([`TyInt; `TyInt], `TyBool)) in
  Proposition.mk_proposition symbol ["x"; "y"]

let program ?(false_entry=true) ?(reachable_error=false) () =
  let start = binary "Start" in
  let live = binary "Live" in
  let dead = binary "Dead" in
  let error = Proposition.mk_proposition (mk_symbol srk ~name:"Error" `TyBool) [] in
  let loop = and_ [eq (v 0) (mk_add srk [v 2; n 1]);
                   eq (v 1) (mk_add srk [v 3; n 2])] in
  let fp = Fp.empty in
  let fp = Fp.add_rule fp start [] (and_ [eq (v 0) (n 0); eq (v 1) (n 0)]) in
  let fp = Fp.add_rule fp live [start] (and_ [eq (v 0) (v 2); eq (v 1) (v 3)]) in
  let fp = if false_entry then Fp.add_rule fp dead [start] (mk_false srk) else fp in
  let fp = Fp.add_rule fp dead [dead] loop in
  let fp = Fp.add_rule fp error [dead] (mk_true srk) in
  let fp = if reachable_error then Fp.add_rule fp error [live] (mk_true srk) else fp in
  Fp.add_query fp (Proposition.symbol_of error), dead, loop

let preprocess fp =
  fp |> ShOffsetAnalysis.elim_ite_chc |> ShOffsetAnalysis.offset_analysis

let assert_equivalent a b =
  let differs = mk_or srk [and_ [a; mk_not srk b]; and_ [b; mk_not srk a]] in
  (* Rule parameters are open de Bruijn variables, which Z3 cannot solve
     directly. Give the same parameter the same arbitrary constant on both
     sides, so this checks equivalence for all parameter valuations. *)
  let parameter = Memo.memo (fun (_, typ) -> mk_const srk (mk_symbol srk (typ :> typ))) in
  let differs = substitute srk parameter differs in
  assert_equal `Unsat (Smt.is_sat srk differs)

let assert_query expected fp =
  assert_equal expected (Smt.is_sat srk (Fp.query_vc_condition fp pd))

let assert_dead_preserved dead loop fp =
  let sym = Proposition.symbol_of dead in
  let rules = List.filter (fun (head, _, _) -> Proposition.symbol_of head = sym) (Fp.get_rules fp) in
  match rules with
  | [(head, [body], constraint_)] ->
    assert_equal sym (Proposition.symbol_of body);
    assert_equal 2 (List.length (Proposition.typ_of_params head));
    assert_equal 2 (List.length (Proposition.typ_of_params body));
    assert_equivalent loop constraint_
  | _ -> assert_failure "Expected the original dead self-loop, without its false entry"

let suite = "Unreachable CHC coalescing" >::: [
  "false entry leaves dead loop unchanged" >:: (fun () ->
    let fp, dead, loop = program () in
    let fp = preprocess fp in
    assert_dead_preserved dead loop fp;
    assert_query `Unsat fp);
  "initially disconnected loop stays unchanged" >:: (fun () ->
    let fp, dead, loop = program ~false_entry:false () in
    let fp = preprocess fp in
    assert_dead_preserved dead loop fp;
    assert_query `Unsat fp);
  "reachable error remains reachable alongside dead loop" >:: (fun () ->
    let fp, dead, loop = program ~reachable_error:true () in
    let fp = preprocess fp in
    assert_dead_preserved dead loop fp;
    assert_query `Sat fp);
  "reachable equal parameters still coalesce" >:: (fun () ->
    let fp, dead, loop = program () in
    let fp = preprocess fp in
    assert_dead_preserved dead loop fp;
    let live_heads = List.filter (fun (head, _, _) ->
      show_symbol srk (Proposition.symbol_of head) = "Live") (Fp.get_rules fp) in
    match live_heads with
    | [(head, _, _)] -> assert_equal 1 (List.length (Proposition.typ_of_params head))
    | _ -> assert_failure "Expected one Live rule");
]

let () = ignore (run_test_tt_main suite)
