open Srk
open Syntax
module C = MakeSimplifyingContext ()
let srk = C.context
let x = mk_var srk 0 `TyInt
let y = mk_const srk (mk_symbol srk ~name:"y" `TyInt)
let z = mk_const srk (mk_symbol srk ~name:"z" `TyInt)
let zero = mk_int srk 0
let and_ = mk_and srk
let or_ = mk_or srk
let eq = mk_eq srk
let leq = mk_leq srk
let exists = mk_exists srk `TyInt
let forall = mk_forall srk `TyInt

let probes = [
  "exists_identity", exists (and_ [eq x y;mk_lt srk x z]), mk_lt srk y z;
  "exists_identity_with_sign", exists (and_ [eq x y;leq zero x;mk_lt srk x z]), and_ [leq zero y;mk_lt srk y z];
  "opposite_bounds_with_sign", exists (and_ [leq zero x;leq x zero;mk_lt srk x y]), mk_lt srk zero y;
  "forall_guarded_identity", forall (or_ [mk_not srk (eq x y);leq zero x]), leq zero y;
  "forall_equality_is_not_definition", forall (eq x zero), mk_false srk;
  "forall_guard_with_added_sign", forall (or_ [mk_not srk (eq x y);mk_lt srk x zero;mk_lt srk x z]), or_ [mk_lt srk y zero;mk_lt srk y z]
]

let () = List.iter (fun (label,input,expected) ->
  let result = Quantifier.eq_guided_elim_loop srk input in
  let solver = SrkZ3.mk_solver ~context:(Z3.mk_context [("timeout","2000")]) srk in
  SrkZ3.Solver.add solver [or_ [and_ [result;mk_not srk expected];and_ [expected;mk_not srk result]]];
  let status = match SrkZ3.Solver.check solver [] with `Unsat -> "equivalent" | `Sat -> "NOT_EQUIVALENT" | `Unknown -> "unknown" in
  Printf.printf "PROBE %s %s before=%d after=%d\n%s\n%!" label status (Syntax.size input) (Syntax.size result)
    (Format.asprintf "%a" (Formula.pp srk) result)) probes
