open Syntax

(* Eliminate explicitly defined local arrays without expanding unrelated branches. *)
let eliminate srk phi =
  let limit = 8 in
  let bounded terms =
    let terms = List.sort_uniq Expr.compare terms in
    if List.length terms <= limit then Some terms else None
  in
  let independent term = not (Hashtbl.mem (free_vars term) 0) in
  let is_local term =
    match ArrTerm.destruct srk term with
    | `Var (0, `TyArr) -> true
    | _ -> false
  in
  (* Some terms certifies: body implies the local equals one of these terms. *)
  let rec definitions body =
    match Formula.destruct srk body with
    | `Fls -> Some []
    | `Atom (`ArrEq (a, b)) when is_local a && independent b -> Some [b]
    | `Atom (`ArrEq (a, b)) when is_local b && independent a -> Some [a]
    | `And conjuncts ->
      List.fold_left (fun best conjunct ->
        match best, definitions conjunct with
        | None, found -> found
        | Some _, None -> best
        | Some xs, Some ys ->
          if List.length ys < List.length xs then Some ys else best)
        None conjuncts
    | `Or disjuncts ->
      List.fold_left (fun acc disjunct ->
        match acc, definitions disjunct with
        | Some xs, Some ys -> bounded (xs @ ys)
        | _ -> None) (Some []) disjuncts
    | _ -> None
  in
  let instantiate body replacement =
    let replacement = substitute srk (fun (index, typ) ->
      assert (index <> 0);
      mk_var srk (index - 1) typ) replacement in
    substitute srk (fun (index, typ) ->
      if index = 0 then (replacement :> ('a, typ_fo) expr)
      else mk_var srk (index - 1) typ) body
  in
  let alg = function
    | `Quantify (`Exists, name, `TyArr, body) ->
      begin match definitions body with
      | Some replacements ->
        mk_or srk (List.map (instantiate body) replacements)
      | None -> mk_exists srk ~name `TyArr body
      end
    | node -> Formula.construct srk node
  in
  Formula.eval srk alg phi
