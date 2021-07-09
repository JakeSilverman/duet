open Srk
open OUnit
open Chc
open Syntax
open Test_pervasives
open Pmfa
open Iteration

let ad = (module OldPmfa.Array_analysis(Product(LinearRecurrenceInequation)(PolyhedronGuard)) : PreDomain)


let a4sym = Ctx.mk_symbol ~name:"a4" `TyArr
let a5sym = Ctx.mk_symbol ~name:"a5" `TyArr
let a6sym = Ctx.mk_symbol ~name:"a6" `TyArr
let a4 = mk_const srk a4sym
let a5 = mk_const srk a5sym
let a6 = mk_const srk a6sym



(*let test_offset1 =
  let phi =
    let open Infix in
    a1 == a2 && forall `TyInt (a2.%[var 0 `TyInt] = a3.%[x])
  in
  let classes = Pmfa.offset_partitioning srk phi in
  Log.errorf "Class a1 isi%n\n" (BatUref.uget (BatHashtbl.find classes a1sym)); 
  Log.errorf "Class a2 isi%n\n" (BatUref.uget (BatHashtbl.find classes a2sym));
  Log.errorf "Class a3 isi%n\n" (BatUref.uget (BatHashtbl.find classes a3sym));
  assert false
*)
(*
let countupsuplin () =
  let fp = Fp.create () in
  let r1 = mk_relation fp ~name:"R1" [`TyInt; `TyArr] in
  let r2 = mk_relation fp ~name:"R2" [`TyArr; `TyInt] in
  let r3 = mk_relation fp ~name:"R3" [`TyInt; `TyArr; `TyArr] in
 
  let error = mk_relation fp [] in
  let atom1 = mk_rel_atom srk fp r1 [xsym; a1sym] in
  let atom2 = mk_rel_atom srk fp r2 [a1sym; xsym'] in
  let atom3 = mk_rel_atom srk fp r3 [xsym'; a2sym; a3sym] in
  let error_atom = mk_rel_atom srk fp error [] in
  let () =
    let open Infix in
    Fp.add_rule fp [] (mk_true srk) atom3;
    Fp.add_rule fp [atom1; atom3] (x' = x + (int 1) && a1 == a3 
                                   && (a1.%[(int 5)]) = x) atom2; 
    Fp.add_rule fp [atom2] (x = x' + (int 1)) atom1;
    Fp.add_rule fp [] ((int 0) <= x) atom1;
    Fp.add_rule fp [atom2] (x' <= (int 0)) error_atom;
    Fp.add_query fp error;
  in
  let fp' = Fp.normalize srk fp in
  let classes = Pmfa.pmfa_chc_offset_partitioning srk fp' in
  BatHashtbl.iter (fun (key : chcvar) uref ->
      let chcvar = BatUref.uget uref in
      Log.errorf "The uref for rel %s param %n is (%s, %n)" 
        (name_of fp key.rel) key.param (name_of fp chcvar.rel) chcvar.param)
    classes;

  let r1_rel = Hashtbl.create 97 in
  let r2_rel = Hashtbl.create 97 in

  Hashtbl.add r1_rel r1 qsym;
  Hashtbl.add r1_rel r2 rsym;
  Hashtbl.add r1_rel r3 ssym;
  Hashtbl.add r2_rel r1 ysym;
  Hashtbl.add r2_rel r2 wsym;
  Hashtbl.add r2_rel r3 zsym;

  let classes = BatHashtbl.map (fun _ uref -> BatUref.uget uref) classes in

  let class_map = Hashtbl.create 97 in
  Hashtbl.add class_map {rel=r1; param=1} r1_rel;
  Hashtbl.add class_map {rel=r3; param=1} r2_rel;

  Log.errorf "HERE";
  apply_offset_candidates srk fp classes class_map;
  Log.errorf "Final fp is\n %a" (Chc.Fp.pp srk) fp;
  assert false*)

let test_offset_partitioning () =
    let phi =
    let open Infix in
    mk_ite srk (a1 == a2) (a3 == a4) ((a3.%[a1.%[x]]<-y) == a5) &&
    (forall `TyInt (a5.%[var 0 `TyInt] = a6.%[x])) &&
    (forall `TyInt (a1.%[var 0 `TyInt] = a6.%[var 0 `TyInt]))
  in
  let classes = Pmfa.offset_partitioning srk phi in
  let equiv a b = BatUref.equal (Hashtbl.find classes a) (Hashtbl.find classes b) in
  assert (equiv a1sym a2sym);
  assert (equiv a1sym a6sym);
  assert (equiv a3sym a4sym);
  assert (equiv a3sym a5sym);
  assert (not (equiv a1sym a3sym))


let time _ =
  let t = Unix.gettimeofday () in
  (*Log.errorf "\n%s Curr time: %fs\n" s (t);*) t

let diff t1 t2 s =
  Log.errorf "\n%s Execution time: %fs\n" s (t2 -. t1)



let test_init () =
  let enter = time "ENTER INIT" in
  let fp = Chc.Fp.create () in
  let fp = Chc.ChcSrkZ3.parse_file srk fp "/Users/jakesilverman/Documents/arraycopy2.smt2" in
  let parse = time "INIT PARSED" in
  diff enter parse "PARSED";
  let fp = Fp.normalize srk fp in
  Pmfa.skolemize_chc srk fp;
  let classes, rules_classes = Pmfa.pmfa_chc_offset_partitioning srk fp in
  let cands = propose_offset_candidates_seahorn srk fp classes in
  let rule_classes2 = derive_offset_for_each_rule fp cands in
  apply_offset_candidates srk fp rules_classes rule_classes2;
  let offset_time = time "POST OFFSETS" in
  diff parse offset_time "OFFSETS TIME";
  let _, fp = Chc.Fp.unbooleanize srk fp in
  let phi = Fp.query_vc_condition srk fp ad in
  let vc_cond_time = time "VC COND" in
  diff offset_time vc_cond_time "VC COND TIME";
  to_file srk phi "/Users/jakesilverman/Documents/duet/duet/vccond.smt2";
  let phi = Pmfa.OldPmfa.eliminate_stores srk phi in
  let trs = [] in
  let tf = TransitionFormula.make phi trs in
  let _, _, _, tf_proj = Pmfa.OldPmfa.projection srk tf in
  let lia = TransitionFormula.formula (Pmfa.OldPmfa.pmfa_to_lia srk tf_proj) in
  to_file srk lia "/Users/jakesilverman/Documents/duet/duet/miniscoped.smt2";
  (*let lia = Quantifier.miniscope srk lia in
  to_file srk lia "/Users/jakesilverman/Documents/duet/duet/miniscopedpost.smt2";
  let lia = Quantifier.eq_guided_qe srk lia in
  to_file srk lia "/Users/jakesilverman/Documents/duet/duet/rewritten_liaNEW.smt2";*)
  let res = match Quantifier.simsat srk lia with
    | `Unsat  -> `No
    | `Unknown -> `Unknown
    | `Sat -> `Unknown
  in 
  let exit = time "EXIT INIT" in
  diff enter exit "INIT";
  (if res = `No then Log.errorf "RES IS NO" else if
     res = `Unknown then Log.errorf "RES IS UKNNOWN" else
     Log.errorf "RES IS YES");
  assert (res = `No)

let test_quant () =
  let exp = SrkZ3.load_smtlib2_file srk "/Users/jakesilverman/Documents/duet/duet/VCCONDJEK.smt2" in
  let phi' = Quantifier.miniscope srk exp in
  Log.errorf "phi' is %a" (Formula.pp srk) phi';
  assert true


(*
let test_init2 () =
  let phi = Syntax.mk_not srk (Syntax.mk_var srk 0 `TyBool) in
  let phi = match Syntax.Formula.destruct srk phi with | open_form -> 
    Syntax.Formula.construct srk open_form in
  Log.errorf "just var is %a" (Syntax.Formula.pp srk) phi;
  let phi = Fp.query_vc_condition srk fp ad in
  let phi = Pmfa.OldPmfa.eliminate_stores srk phi in
  let tf = TransitionFormula.make phi trs in
  let _, _, tf_proj = Arraycontent.projection srk tf in
  let lia = TransitionFormula.formula (Arraycontent.pmfa_to_lia srk tf_proj) in
  Log.errorf "lia is %a" (Formula.pp srk) lia;
  let lia = Quantifier.miniscope srk lia in
  let lia = Quantifier.eq_guided_qe srk lia in
  to_file srk lia "/Users/jakesilverman/Documents/duet/duet/rewritten_liaNEW.smt2";
  let res = match Quantifier.simsat srk lia with
    | `Unsat  -> `No
    | `Unknown -> `Unknown
    | `Sat -> `Unknown
  in 
  (if res = `No then Log.errorf "RES IS NO" else if
     res = `Unknown then Log.errorf "RES IS UKNNOWN" else
     Log.errorf "RES IS YES");
  assert (res = `No)
*)


let suite = "Pmfa" >:::
  [

    (*"test_offset1" >:: test_offset1;*)
    (*"contupsuplin" >:: countupsuplin;*)
    (*"test_offset_partitioning" >:: test_offset_partitioning;*) 
    (*"test_init" >:: test_init*)
    "test_quant" >:: test_quant
  ]