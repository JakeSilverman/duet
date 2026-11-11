open Syntax

(* Normalize linear combinations of syntactic atoms without allocating fresh
   logical variables. Atom identities are local to this invocation. *)
module Keys = Hashtbl.Make(struct
  type t = QQ.t * (int * QQ.t) list
  let equal (c,xs) (d,ys) =
    QQ.equal c d && List.length xs = List.length ys &&
    List.for_all2 (fun (i,a) (j,b) -> i=j && QQ.equal a b) xs ys
  let hash (c,xs) = Hashtbl.hash (QQ.show c, List.map (fun (i,a) -> i,QQ.show a) xs)
end)

type 'a bound = {
  index : int;
  positive : bool;
  strict : bool;
  lhs : 'a arith_term;
  rhs : 'a arith_term;
}
type 'a fact = Bound of 'a bound | Equality

let simplify srk phi =
  let atoms = Expr.HT.create 97 in
  let next_atom = ref 0 in
  let atom_id term =
    try Expr.HT.find atoms term with Not_found ->
      let id = !next_atom in incr next_atom; Expr.HT.add atoms term id; id in
  let cache = Hashtbl.create 97 in
  let normalize lhs rhs =
    let pair = atom_id lhs, atom_id rhs in
    try Hashtbl.find cache pair with Not_found ->
      let constant = ref QQ.zero and coefficients = Hashtbl.create 7 in
      let atom scale term =
        let id = atom_id term in
        let old = try Hashtbl.find coefficients id with Not_found -> QQ.zero in
        Hashtbl.replace coefficients id (QQ.add old scale) in
      let rec collect scale term =
        match ArithTerm.destruct srk term with
        | `Real c -> constant := QQ.add !constant (QQ.mul scale c)
        | `Add terms -> List.iter (collect scale) terms
        | `Unop (`Neg,t) -> collect (QQ.negate scale) t
        | `Mul terms ->
          let coefficient,rest = List.fold_left (fun (c,rest) t ->
            match ArithTerm.destruct srk t with
            | `Real q -> QQ.mul c q,rest | _ -> c,t::rest) (QQ.one,[]) terms in
          begin match rest with
          | [] -> constant := QQ.add !constant (QQ.mul scale coefficient)
          | [t] -> collect (QQ.mul scale coefficient) t
          | _ -> atom scale term
          end
        | _ -> atom scale term in
      collect QQ.one lhs; collect (QQ.negate QQ.one) rhs;
      let terms = Hashtbl.fold (fun id c terms ->
        if QQ.equal c QQ.zero then terms else (id,c)::terms) coefficients []
        |> List.sort (fun (i,_) (j,_) -> Int.compare i j) in
      let result = match terms with
        | [] -> `Constant !constant
        | (_,pivot)::_ ->
          let inverse = QQ.inverse pivot in
          `Linear ((QQ.mul !constant inverse,
                    List.map (fun (i,c) -> i,QQ.mul c inverse) terms),
                   QQ.compare pivot QQ.zero > 0) in
      Hashtbl.add cache pair result;
      result in
  let conjunction terms =
    let terms = Array.of_list terms in
    let keep = Array.make (Array.length terms) true in
    let facts = Keys.create 17 in
    let contradiction = ref false in
    Array.iteri (fun index term -> match Formula.destruct srk term with
      | `Atom (`Arith ((`Leq | `Lt as op),lhs,rhs)) ->
        let strict = op = `Lt in
        begin match normalize lhs rhs with
        | `Constant c ->
          if (if strict then QQ.compare c QQ.zero < 0 else QQ.compare c QQ.zero <= 0)
          then keep.(index) <- false else contradiction := true
        | `Linear (key,positive) ->
          let bound = {index;positive;strict;lhs;rhs} in
          begin match Keys.find_opt facts key with
          | None -> Keys.add facts key (Bound bound)
          | Some Equality ->
            if strict then contradiction := true else keep.(index) <- false
          | Some (Bound old) when old.positive = positive ->
            if strict && not old.strict then (
              keep.(old.index) <- false; Keys.replace facts key (Bound bound))
            else keep.(index) <- false
          | Some (Bound old) ->
            if strict || old.strict then contradiction := true
            else (
              terms.(old.index) <- mk_eq srk old.lhs old.rhs;
              keep.(index) <- false;
              Keys.replace facts key Equality)
          end
        end
      | _ -> ()) terms;
    if !contradiction then mk_false srk
    else mk_and srk (Array.to_list (Array.mapi (fun i term -> i,term) terms)
      |> List.filter_map (fun (i,term) -> if keep.(i) then Some term else None)) in
  Formula.eval_memo srk (function
    | `And terms -> conjunction terms
    | node -> Formula.construct srk node) phi
