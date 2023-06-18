open Srk
open OUnit
open Syntax
open Test_pervasives
open Iteration

let ad = (module Pmfa.OldPmfa.Array_analysis(Product(LossyTranslation)(PolyhedronGuard))
      (Product(GuardedTranslation)(PolyhedronGuard)): PreDomain)




  module AD = Pmfa.OldPmfa.Array_analysis (Iteration.Product(Iteration.LossyTranslation)(Iteration.PolyhedronGuard))
          (Iteration.Product(Iteration.GuardedTranslation)(Iteration.PolyhedronGuard))



let a4sym = Ctx.mk_symbol ~name:"a4" `TyArr
let a5sym = Ctx.mk_symbol ~name:"a5" `TyArr
let a6sym = Ctx.mk_symbol ~name:"a6" `TyArr
let a4 = mk_const srk a4sym
let a5 = mk_const srk a5sym
let a6 = mk_const srk a6sym

let test_mp =
  let phi =
    let open Infix in
    a1 == a2 && (a2.%[x] = (int 5)) && x' = x + (int 1)
  in
  let tf = TransitionFormula.make phi [(xsym, xsym'); (a1sym, a2sym)] in
  let mp = AD.mp srk tf in
  Log.errorf "mp is %a" (Formula.pp srk) mp;
  assert false



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

let time _ =
  let t = Unix.gettimeofday () in
  (*Log.errorf "\n%s Curr time: %fs\n" s (t);*) t

let diff t1 t2 s =
  Log.errorf "\n%s Execution time: %fs\n" s (t2 -. t1)


let suite = "Pmfa" >:::
  [
    "test_mp" >:: test_mp
    (*"test_offset1" >:: test_offset1;*)
    (*"contupsuplin" >:: countupsuplin;*)
    (*"test_offset_partitioning" >:: test_offset_partitioning;*) 
    (*"test_init" >:: test_init*)
    (*"test_quant" >:: test_quant*)
  ]
