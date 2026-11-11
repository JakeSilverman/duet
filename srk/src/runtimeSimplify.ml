open Syntax

(* Exact local rewrites over Int/Real arithmetic and Boolean structure. No
   solver calls, distribution, fresh symbols, or substitution across binders. *)
let cheap srk phi =
  let memo = Expr.HT.create 991 in
  let keys = Expr.HT.create 991 in
  (* Ordering only: hash collisions never equate terms. Ignore binder names,
     but retain every free-symbol identity and de Bruijn index. *)
  let rec key expr =
    try Expr.HT.find keys expr with Not_found ->
      let label, children = Expr.destruct_sexpr srk expr in
      let label = match label with
        | Exists (_, typ) -> Exists ("", typ)
        | Forall (_, typ) -> Forall ("", typ)
        | label -> label in
      let value = Digest.string
          (Marshal.to_string (label, List.map key children) [Marshal.No_sharing]) in
      Expr.HT.add keys expr value;
      value in
  let compare a b =
    let order = String.compare (key a) (key b) in
    if order = 0 then Expr.compare a b else order in
  let affine_cache = Expr.HT.create 991 in
  let affine term =
    try Expr.HT.find affine_cache term with Not_found ->
      let constant = ref QQ.zero and coefficients = Expr.HT.create 17 in
      let atom scale term =
        let old = try Expr.HT.find coefficients term with Not_found -> QQ.zero in
        Expr.HT.replace coefficients term (QQ.add old scale) in
      let rec collect scale term =
        match ArithTerm.destruct srk term with
        | `Real value -> constant := QQ.add !constant (QQ.mul scale value)
        | `Add terms -> List.iter (collect scale) terms
        | `Unop (`Neg, term) -> collect (QQ.negate scale) term
        | `Mul terms ->
          let coefficient, rest = List.fold_left (fun (coefficient, rest) term ->
              match ArithTerm.destruct srk term with
              | `Real value -> QQ.mul coefficient value, rest
              | _ -> coefficient, term :: rest) (QQ.one, []) terms in
          begin match rest with
          | [] -> constant := QQ.add !constant (QQ.mul scale coefficient)
          | [term] -> collect (QQ.mul scale coefficient) term
          (* Do not expand nonlinear products or cancel divisors. *)
          | _ -> atom scale term
          end
        | _ -> atom scale term in
      collect QQ.one term;
      let terms = BatEnum.fold (fun terms (term, coefficient) ->
          if QQ.equal coefficient QQ.zero then terms
          else (term, coefficient) :: terms) [] (Expr.HT.enum coefficients)
        |> List.sort (fun (a, _) (b, _) -> compare (a :> (_, typ_fo) expr) (b :> (_, typ_fo) expr)) in
      let result = !constant, terms in
      Expr.HT.add affine_cache term result;
      result in
  let rebuild_affine constant terms =
    let terms = List.map (fun (term, coefficient) ->
        if QQ.equal coefficient QQ.one then term
        else mk_mul srk [mk_real srk coefficient; term]) terms in
    match (if QQ.equal constant QQ.zero then [] else [mk_real srk constant]) @ terms with
    | [] -> mk_zero srk
    | [term] -> term
    | terms -> mk_add srk terms in
  let negate (constant, terms) =
    QQ.negate constant, List.map (fun (term, coefficient) -> term, QQ.negate coefficient) terms in
  let boolean label terms =
    let seen = Expr.HT.create 17 in
    let rec flatten acc term =
      if Expr.HT.mem seen term then acc
      else (
        Expr.HT.add seen term ();
        let child_label, children = Expr.destruct_sexpr srk term in
        if child_label = label then List.fold_left flatten acc children
        else term :: acc) in
    let terms = List.fold_left flatten [] terms |> List.sort compare in
    (* Omit absorption: although equivalent, removing redundant alternatives
       regressed downstream termination analysis in the diagnostic probes. *)
    let neutral, absorbing = if label = And then True, False else False, True in
    if List.exists (fun term -> fst (Expr.destruct_sexpr srk term) = absorbing) terms then
      Expr.construct_sexpr srk absorbing []
    else
      let terms = List.filter (fun term -> fst (Expr.destruct_sexpr srk term) <> neutral) terms in
      match terms with
      | [] -> Expr.construct_sexpr srk neutral []
      | [term] -> term
      | terms -> Expr.construct_sexpr srk label terms in
  let rec go expr =
    try Expr.HT.find memo expr with Not_found ->
      let label, children = Expr.destruct_sexpr srk expr in
      let children = List.map (fun original ->
          let simplified = go original in
          (* A real expression can simplify numerically to an integer literal.
             Retain its original sort in parent operators: Z3 division is
             overloaded, so replacing a real numerator by an Int changes it
             from real division to integer division. This also preserves
             operand sorts for floor and typed function applications. *)
          if expr_typ srk original = `TyReal && expr_typ srk simplified = `TyInt
          then original else simplified) children in
      let rebuild () = Expr.construct_sexpr srk label children in
      let result = match label, children with
        | (Add | Neg), _ ->
          let constant, terms = affine (Expr.arith_term_of srk (rebuild ())) in
          (rebuild_affine constant terms :> ('a, typ_fo) expr)
        | (Eq | Leq | Lt), [a; b] ->
          let a = Expr.arith_term_of srk a and b = Expr.arith_term_of srk b in
          let constant, terms = affine (mk_sub srk a b) in
          let constant, terms = match label, terms with
            | Eq, (_, coefficient) :: _ when QQ.compare coefficient QQ.zero < 0 ->
              negate (constant, terms)
            | _ -> constant, terms in
          let formula = match label, terms with
            | _, [] ->
              let comparison = QQ.compare constant QQ.zero in
              let holds = match label with Eq -> comparison = 0 | Leq -> comparison <= 0 | _ -> comparison < 0 in
              if holds then mk_true srk else mk_false srk
            (* Keep unit-coefficient definitions visible to identity elimination.
               No division is introduced, including for integer variables. *)
            | Eq, (term, coefficient) :: rest when QQ.equal coefficient QQ.one ->
              let constant, rest = negate (constant, rest) in
              mk_eq srk term (rebuild_affine constant rest)
            | _ ->
              let lhs = rebuild_affine constant terms in
              (match label with Eq -> mk_eq | Leq -> mk_leq | _ -> mk_lt)
                srk lhs (mk_zero srk) in
          (formula :> ('a, typ_fo) expr)
        | (And | Or), terms -> boolean label terms
        | ArrEq, [a; b] when Expr.equal a b -> (mk_true srk :> ('a, typ_fo) expr)
        | _ -> rebuild () in
      Expr.HT.add memo expr result;
      result in
  Expr.formula_of srk (go (phi :> ('a, typ_fo) expr))

let cleanup srk phi =
  phi |> cheap srk |> TempElim.eliminate ~limit:1 srk |> cheap srk
