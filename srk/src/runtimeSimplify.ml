open Syntax

(* Exact local rewrites, memoized over the expression DAG. No distribution. *)
let cheap srk phi =
  let memo = Expr.HT.create 991 in
  let rec go expr =
    try Expr.HT.find memo expr with Not_found ->
      let label, children = Expr.destruct_sexpr srk expr in
      let children = List.map go children in
      let rebuild () = Expr.construct_sexpr srk label children in
      let dedup children =
        let seen = Expr.HT.create 17 in
        List.filter (fun child ->
          if Expr.HT.mem seen child then false
          else (Expr.HT.add seen child (); true)) children
      in
      let result = match label, children with
        | Add, terms ->
          let constant, rest = List.fold_right (fun term (constant, rest) ->
            match Expr.destruct_sexpr srk term with
            | Real value, [] -> QQ.add constant value, rest
            | _ -> constant, term :: rest) terms (QQ.zero, []) in
          (mk_add srk ((if QQ.equal constant QQ.zero then [] else [mk_real srk constant]) @ List.map (Expr.arith_term_of srk) rest) :> ('a, typ_fo) expr)
        | And, terms -> (mk_and srk (List.map (Expr.formula_of srk) (dedup terms)) :> ('a, typ_fo) expr)
        | Or, terms -> (mk_or srk (List.map (Expr.formula_of srk) (dedup terms)) :> ('a, typ_fo) expr)
        | (Eq | ArrEq | Leq), [a;b] when Expr.equal a b -> (mk_true srk :> ('a, typ_fo) expr)
        | Lt, [a;b] when Expr.equal a b -> (mk_false srk :> ('a, typ_fo) expr)
        | _ -> rebuild ()
      in
      Expr.HT.add memo expr result;
      result
  in
  Expr.formula_of srk (go (phi :> ('a, typ_fo) expr))

let cleanup srk phi =
  phi |> cheap srk |> TempElim.eliminate ~limit:1 srk |> cheap srk
