open Srk
open Syntax
let check input output =
  let module C = MakeSimplifyingContext () in
  let srk=C.context in
  let before=SrkZ3.load_smtlib2_file srk input in
  let _,symbols_before,named_before=context_stats srk in
  let after=RuntimeSimplify.cheap srk before in
  let _,symbols_after,named_after=context_stats srk in
  assert (symbols_before=symbols_after && named_before=named_after);
  assert (Expr.equal after (RuntimeSimplify.cheap srk after));
  let write suffix phi =
    let out=open_out (output^suffix) in let fmt=Format.formatter_of_out_channel out in
    pp_smtlib2 srk fmt phi;Format.pp_print_flush fmt ();close_out out in
  write ".before.smt2" before;write ".after.smt2" after;
  Printf.printf "%s\t%d\t%d\n%!" (Filename.basename input) (Syntax.size before) (Syntax.size after)
let () =
  if Array.length Sys.argv<>3 then failwith "usage: check_cleanup INPUT_DIR OUTPUT_DIR";
  Sys.readdir Sys.argv.(1) |> Array.to_list |> List.sort String.compare
  |> List.filter (fun name -> Filename.check_suffix name ".smt2")
  |> List.iter (fun name -> check (Filename.concat Sys.argv.(1) name) (Filename.concat Sys.argv.(2) name))
