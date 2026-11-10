open Srk
open Syntax
module Ctx = MakeSimplifyingContext ()
module Chc = Chc.Make(Ctx)
open Chc
let srk = Ctx.context

let () =
  if Array.length Sys.argv <> 3 then failwith "usage: dump_forward_sign CHC OUTDIR";
  let fp = ChcSrkZ3.parse_file Sys.argv.(1)
    |> ShOffsetAnalysis.elim_ite_chc |> ShOffsetAnalysis.offset_analysis in
  let r = Fp.ForwardSign.infer fp in
  if not r.Fp.ForwardSign.validated then failwith r.Fp.ForwardSign.reason;
  let inv sym = List.assoc sym r.Fp.ForwardSign.invariants in
  let out = open_out (Filename.concat Sys.argv.(2) "invariants.txt") in
  let fmt = Format.formatter_of_out_channel out in
  Format.fprintf fmt "Inductive: checks=%d unknown=%d seconds=%f@." r.Fp.ForwardSign.checks r.Fp.ForwardSign.unknown r.Fp.ForwardSign.seconds;
  List.iter (fun (sym,phi) ->
      let p = Fp.get_rules fp |> List.find_opt (fun (p,_,_) -> Proposition.symbol_of p = sym) in
      let names = match p with Some (p,_,_) -> Proposition.names_of p | None -> [] in
      Format.fprintf fmt "%s (%s): %a@." (show_symbol srk sym) (String.concat ", " names) (Formula.pp srk) phi)
    r.Fp.ForwardSign.invariants;
  Format.pp_print_flush fmt (); close_out out;
  Fp.iteri_rules (fun index (head,body,constraint_) ->
      let next = ref (List.length (Proposition.typ_of_params head)) in
      let assumptions = List.map (fun p ->
          let offset = !next in
          next := !next + List.length (Proposition.typ_of_params p);
          substitute srk (fun (i,t) -> mk_var srk (i+offset) t) (inv (Proposition.symbol_of p))) body in
      let phi = mk_and srk (constraint_ :: mk_not srk (inv (Proposition.symbol_of head)) :: assumptions) in
      let syms = Memo.memo (fun (_,typ) -> mk_symbol srk (typ :> typ)) in
      let phi = substitute srk (fun v -> mk_const srk (syms v)) phi in
      let solver = SrkZ3.mk_solver srk in
      SrkZ3.Solver.add solver [phi];
      let path = Filename.concat Sys.argv.(2) (Printf.sprintf "rule-%03d.smt2" index) in
      let channel = open_out path in
      output_string channel (SrkZ3.Solver.to_string solver);
      output_string channel "\n(check-sat)\n";close_out channel) fp
