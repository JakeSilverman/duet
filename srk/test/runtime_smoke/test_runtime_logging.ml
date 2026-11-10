open Srk
open OUnit
let () = ignore (run_test_tt_main ("Optional formula output" >::: [
  "disabled printer is not evaluated" >:: (fun () ->
    let calls = ref 0 in
    let pp fmt () = incr calls; Format.pp_print_string fmt "small test formula" in
    Log.formulaf "probe: %a" pp ();
    assert_equal (if Log.dump_formulas then 1 else 0) !calls)
]))
