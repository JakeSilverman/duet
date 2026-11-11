open Srk
open Syntax
let sequence = ref 0
let typ t = Format.asprintf "%a" pp_typ t
let capture srk label phi =
  match Sys.getenv_opt "AMA_FORMULA_TRACE_DIR" with
  | None -> ()
  | Some dir ->
    incr sequence;
    let base = Printf.sprintf "%s/%04d-%s" dir !sequence label in
    let seen = Expr.HT.create 991 and nodes = ref [] and next = ref 0 in
    let rec visit expr =
      try Expr.HT.find seen expr with Not_found ->
        let id = !next in incr next; Expr.HT.add seen expr id;
        let tag,children = Expr.destruct_sexpr srk expr in
        let op,extra = match tag with
          | True -> "true","" | False -> "false",""
          | And -> "and","" | Or -> "or","" | Not -> "not",""
          | Exists (name,t) -> "exists",Printf.sprintf ",\"name\":%S,\"sort\":%S" name (typ t)
          | Forall (name,t) -> "forall",Printf.sprintf ",\"name\":%S,\"sort\":%S" name (typ t)
          | Eq -> "=","" | Leq -> "<=","" | Lt -> "<","" | ArrEq -> "array=",""
          | App sym -> "app",Printf.sprintf ",\"symbol\":%d,\"name\":%S,\"sort\":%S" (int_of_symbol sym) (show_symbol srk sym) (typ (typ_symbol srk sym))
          | Var (i,t) -> "var",Printf.sprintf ",\"index\":%d,\"sort\":%S" i (typ t)
          | Add -> "+","" | Mul -> "*","" | Div -> "/","" | Mod -> "mod",""
          | Floor -> "floor","" | Neg -> "neg","" | Real q -> "number",Printf.sprintf ",\"value\":%S" (QQ.show q)
          | Ite -> "ite","" | Store -> "store","" | Select -> "select","" | IsInt -> "is_int","" in
        let kids=List.map visit children in
        nodes := (id,Printf.sprintf "{\"id\":%d,\"op\":%S%s,\"args\":[%s]}" id op extra (String.concat "," (List.map string_of_int kids)))::!nodes;
        id in
    let root=visit (phi :> (_,typ_fo) expr) in
    let out=open_out (base^".json") in
    Printf.fprintf out "{\"label\":%S,\"sequence\":%d,\"size\":%d,\"root\":%d,\"nodes\":[%s]}\n" label !sequence (Syntax.size phi) root (String.concat "," (List.map snd (List.sort compare !nodes)));
    close_out out;
    let out=open_out (base^".txt") in
    let fmt=Format.formatter_of_out_channel out in
    Formula.pp srk fmt phi; Format.pp_print_flush fmt ();close_out out;
    if Hashtbl.length (free_vars phi)=0 then (
      let out=open_out (base^".smt2") in
      let fmt=Format.formatter_of_out_channel out in
      pp_smtlib2 srk fmt phi;Format.pp_print_flush fmt ();close_out out);
    Printf.printf "CAPTURE %04d %s tree=%d dag=%d\n%!" !sequence label (Syntax.size phi) !next
