open Srk
open Syntax
(* Diagnostic-only: exact affine collection and associative Boolean cleanup. *)
let local srk phi =
  let cache = Expr.HT.create 991 in
  let affine term =
    let coeffs = Expr.HT.create 17 and constant = ref QQ.zero in
    let rec collect k t =
      match ArithTerm.destruct srk t with
      | `Real c -> constant := QQ.add !constant (QQ.mul k c)
      | `Add xs -> List.iter (collect k) xs
      | `Unop (`Neg,x) -> collect (QQ.negate k) x
      | `Mul xs ->
        let c,rest=List.fold_left (fun (c,rest) x -> match ArithTerm.destruct srk x with
          | `Real q -> QQ.mul c q,rest | _ -> c,x::rest) (QQ.one,[]) xs in
        begin match rest with
        | [] -> constant:=QQ.add !constant (QQ.mul k c)
        | [x] -> collect (QQ.mul k c) x
        | _ -> atom k t end
      | _ -> atom k t
    and atom k t =
      let prior=try Expr.HT.find coeffs t with Not_found -> QQ.zero in
      Expr.HT.replace coeffs t (QQ.add prior k) in
    collect QQ.one term;
    let terms=BatEnum.fold (fun acc (t,c) -> if QQ.equal c QQ.zero then acc else (t,c)::acc) [] (Expr.HT.enum coeffs)
      |> List.sort (fun (a,_) (b,_) -> Expr.compare a b) in
    !constant,terms in
  let rebuild_affine c terms =
    mk_add srk ((if QQ.equal c QQ.zero then [] else [mk_real srk c]) @
      List.map (fun (t,k) -> if QQ.equal k QQ.one then t else mk_mul srk [mk_real srk k;t]) terms) in
  let rec go e =
    try Expr.HT.find cache e with Not_found ->
      let tag,kids=Expr.destruct_sexpr srk e in
      let kids=List.map go kids in
      let rebuilt=Expr.construct_sexpr srk tag kids in
      let result=match tag,kids with
      | (Add | Neg),_ ->
        let c,terms=affine (Expr.arith_term_of srk rebuilt) in
        (rebuild_affine c terms :> (_,typ_fo) expr)
      | (Eq | Leq | Lt),[a;b] ->
        let a=Expr.arith_term_of srk a and b=Expr.arith_term_of srk b in
        let c,terms=affine (mk_sub srk a b) in
        let c,terms=match tag,terms with
          | Eq,(_,k)::_ when QQ.compare k QQ.zero < 0 -> QQ.negate c,List.map (fun (t,k)->t,QQ.negate k) terms
          | _ -> c,terms in
        let t=rebuild_affine c terms in
        let f=match tag with Eq->mk_eq | Leq->mk_leq | _->mk_lt in
        (f srk t (mk_zero srk) :> (_,typ_fo) expr)
      | (And | Or),_ ->
        let rec flatten e = let op,xs=Expr.destruct_sexpr srk e in
          if op=tag then List.concat_map flatten xs else [e] in
        let kids=List.concat_map flatten kids |> List.sort_uniq Expr.compare in
        let members=Expr.HT.create 17 in List.iter (fun e->Expr.HT.add members e ()) kids;
        let opposite=if tag=And then Or else And in
        let kids=List.filter (fun e->let op,xs=Expr.destruct_sexpr srk e in
          not (op=opposite && List.exists (fun x->Expr.HT.mem members x) xs)) kids in
        Expr.construct_sexpr srk tag kids
      | _ -> rebuilt in
      Expr.HT.add cache e result;result in
  Expr.formula_of srk (go (phi :> (_,typ_fo) expr))
