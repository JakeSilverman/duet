open Syntax
module T = TransitionFormula



let time _ =
  let t = Unix.gettimeofday () in
  (*Log.errorf "\n%s Curr time: %fs\n" s (t);*) t

let diff t1 t2 s = 
  Log.errorf "\n%s Execution time: %fs\n" s (t2 -. t1)

let typ_symbol_fo srk sym =
    match typ_symbol srk sym with
    | `TyInt -> `TyInt
    | `TyReal -> `TyReal
    | `TyBool -> `TyBool
    | `TyArr -> `TyArr
    | _ -> assert false

 let eliminate_stores srk phi =
  let mk_op op =
    match op with
    | `Eq -> mk_eq
    | `Lt -> mk_lt
    | `Leq -> mk_leq
  in
  let rec rewrite_store index node =
    match ArrTerm.destruct srk node with
    | `Store (a, i, v) ->
      let i = ArithTerm.eval srk arith_alg i in
      let v = ArithTerm.eval srk arith_alg v in
      mk_ite srk (mk_eq srk i index) v (rewrite_store index a)
    | `Var (ind, `TyArr) -> mk_select srk (mk_var srk ind `TyArr) index
    | `App (a, []) -> mk_select srk (mk_const srk a) index
    | `Ite (phi, a, b) -> 
      mk_ite 
        srk 
        (Formula.eval srk alg phi) 
        (rewrite_store index a)
        (rewrite_store index b)
    | _ -> assert false
  and  arith_alg = function
    | `Select (a, i) -> rewrite_store i a
    | `Ite (phi, x, y) -> mk_ite srk (Formula.eval srk alg phi) x y
    | open_term -> ArithTerm.construct srk open_term
  and alg = function
    | `Atom (`Arith (op, x, y)) ->
      (mk_op op) srk (ArithTerm.eval srk arith_alg x) (ArithTerm.eval srk arith_alg y)
    | `Atom(`ArrEq (a, b)) -> 
      let index = mk_symbol srk ~name:"INDEX" `TyInt in
      let lhs = rewrite_store (mk_const srk index) a in
      let rhs = rewrite_store (mk_const srk index) b in
      mk_forall_const srk index (mk_eq srk lhs rhs)
    | open_formula -> Formula.construct srk open_formula
  in
  Formula.eval srk alg phi



(* Replace this function in unbooleanize then delete *)
let skolemize srk phi =
  let decapture_tbl = BatHashtbl.create 97 in
  let subst = 
    Memo.memo (fun (ind, typ) ->
        let sym = mk_symbol srk ~name:"SKOLEM" (typ :> typ) in
        BatHashtbl.add decapture_tbl sym ind;
        mk_const srk sym)
  in
  let phi = 
    substitute
      srk
      subst phi
  in
  let rec subst_existentials subst_lst expr =
    match Formula.destruct srk expr with
    | `Quantify (`Exists, name, typ, phi) ->
      subst_existentials ((mk_symbol srk ~name (typ :> typ)) :: subst_lst) phi
    | `And conjuncts ->
      mk_and srk (List.map (subst_existentials subst_lst) conjuncts)
    | `Or disjuncts ->
      mk_or srk (List.map (subst_existentials subst_lst) disjuncts)
    | open_form ->
      (* TODO: make substitute more efficient *)
      substitute
        srk
        (fun (i, _) -> 
             mk_const srk (List.nth subst_lst i))
        (Formula.construct srk open_form)
  in
  substitute_sym
    srk
    (fun sym ->
       if Hashtbl.mem decapture_tbl sym then
         mk_var srk (Hashtbl.find decapture_tbl sym) (typ_symbol_fo srk sym)
       else mk_const srk sym)
    (subst_existentials [] phi)





module OldPmfa = struct
  open Syntax
  open Iteration
  module V = Linear.QQVector
  module M = Linear.QQMatrix
  module Z = Linear.ZZVector
  module H = Abstract
  module T = TransitionFormula
  include Log.Make(struct let name = "srk.array:" end)


  let arr_trs srk tf = 
    List.filter (fun (s, _) -> typ_symbol srk s = `TyArr) (T.symbols tf)

  let int_trs srk tf =
    List.filter (fun (s, _) -> (typ_symbol srk s = `TyInt)) (T.symbols tf)

  let flatten syms = List.fold_left (fun acc (sym, sym') -> sym :: sym' :: acc) [] syms 
  

  (* Projects an array transition formula [tf] down to a single symbolic index
   * [j]. The dynamics of element [j] of array transition variables (a, a') 
   * are captured with the integer transition variables ([map] a, [map] a'). *)
  let projection_with_store_elim srk tf eqs extras =
    let map = Hashtbl.create (List.length (arr_trs srk tf) * 8 / 3) in
    let rmap = Hashtbl.create (List.length (arr_trs srk tf) * 8 / 3) in

    let j = mk_symbol srk ~name:"j" `TyInt in

    let f (trs, arr_only_trs, symb_consts, phi) (a, a') =
      if Symbol.Map.mem a eqs then (
        let z = mk_symbol srk ~name:("z"^(show_symbol srk a)) `TyInt in
        let z' = mk_symbol srk ~name:("z'"^(show_symbol srk a')) `TyInt in
        let phi = 
          mk_and 
            srk 
            [
              mk_eq srk (mk_const srk z') (mk_select srk (mk_const srk a') (mk_const srk j));
              phi]
        in
        Hashtbl.add map z a;

        Hashtbl.add map z' a';
        trs,
        arr_only_trs,
        z' :: symb_consts,
        phi
      )
      else (
      let z = mk_symbol srk ~name:("z"^(show_symbol srk a)) `TyInt in
      let z' = mk_symbol srk ~name:("z'"^(show_symbol srk a')) `TyInt in
      let phi = 
        mk_and 
          srk 
          [mk_eq srk (mk_const srk z) (mk_select srk (mk_const srk a) (mk_const srk j));
           mk_eq srk (mk_const srk z') (mk_select srk (mk_const srk a') (mk_const srk j));
           phi]
      in


      Hashtbl.add map z a;
      Hashtbl.add map z' a';
      Hashtbl.add rmap a z;
      Hashtbl.add rmap a' z';
      (z, z') :: trs,
      (z, z') :: arr_only_trs,
      symb_consts,
      phi)
    in
    let integer_trs, arr_only_trs, symb_consts, phi = 
      List.fold_left f (int_trs srk tf, [], [], T.formula tf) (arr_trs srk tf) 
    in
    let rec decon_store node =
      match ArrTerm.destruct srk node with
      | `Store (a, i, v) ->
        begin match decon_store a with
          | Some b -> 
            Some (mk_ite srk (mk_eq srk i (mk_const srk j)) v b)
          | None -> None
        end
      | `Var _ -> None
      | `App (a, []) -> Some (mk_const srk (Hashtbl.find rmap a))
      | `Ite _ -> assert false
      | _ -> assert false
    in
    let alg = function
      | `Atom(`ArrEq (a, b)) -> 
      let lhs = decon_store a in
      let rhs = decon_store b in
      begin match lhs, rhs with
        | Some v1, Some v2 -> mk_eq srk v1 v2
        | _ -> Formula.construct srk (`Atom(`ArrEq (a, b)))
      end
      | open_formula -> Formula.construct srk open_formula
    in
    let phi = Formula.eval srk alg phi in

    (* TODO: Fix assumption that no symbolic constants *)
    let phi = 
      mk_exists_consts srk (fun sym -> List.mem sym (flatten integer_trs) || List.mem sym symb_consts || Symbol.Set.mem sym extras || sym = j) phi 
    in
    j, map, T.make phi integer_trs, arr_only_trs, symb_consts 



  (* Projects an array transition formula [tf] down to a single symbolic index
   * [j]. The dynamics of element [j] of array transition variables (a, a') 
   * are captured with the integer transition variables ([map] a, [map] a'). *)
  let projection srk tf eqs extras =
    let map = Hashtbl.create (List.length (arr_trs srk tf) * 8 / 3) in
    let j = mk_symbol srk ~name:"j" `TyInt in

    let f (trs, arr_only_trs, symb_consts, phi) (a, a') =
      if Symbol.Map.mem a eqs then (
        let z = mk_symbol srk ~name:("z"^(show_symbol srk a)) `TyInt in
        let z' = mk_symbol srk ~name:("z'"^(show_symbol srk a')) `TyInt in
        let phi = 
          mk_and 
            srk 
            [
              mk_eq srk (mk_const srk z') (mk_select srk (mk_const srk a') (mk_const srk j));
              phi]
        in
        Hashtbl.add map z a;

        Hashtbl.add map z' a';
        trs,
        arr_only_trs,
        z' :: symb_consts,
        phi
      )
      else (
      let z = mk_symbol srk ~name:("z"^(show_symbol srk a)) `TyInt in
      let z' = mk_symbol srk ~name:("z'"^(show_symbol srk a')) `TyInt in
      let phi = 
        mk_and 
          srk 
          [mk_eq srk (mk_const srk z) (mk_select srk (mk_const srk a) (mk_const srk j));
           mk_eq srk (mk_const srk z') (mk_select srk (mk_const srk a') (mk_const srk j));
           phi]
      in


      Hashtbl.add map z a;
      Hashtbl.add map z' a';
      (z, z') :: trs,
      (z, z') :: arr_only_trs,
      symb_consts,
      phi)
    in
    let integer_trs, arr_only_trs, symb_consts, phi = 
      List.fold_left f (int_trs srk tf, [], [], T.formula tf) (arr_trs srk tf) 
    in
    (* TODO: Fix assumption that no symbolic constants *)
    let phi = 
      mk_exists_consts srk (fun sym -> List.mem sym (flatten integer_trs) || List.mem sym symb_consts || Symbol.Set.mem sym extras || sym = j) phi 
    in
    j, map, T.make phi integer_trs, arr_only_trs 

  (* Convert from a pmfa formula to an mfa formula.
   * We achieve this by converting the pmfa formula to an equivalent formula
   * in qnf such that there is a single universal quantifier. The key algorithm
   * thus is just a merging of the matrices under potentially many (non-nested) 
   * universal quantifiers. We factor the universal quantifier over disjunction
   * by introducing a new quantified integer sorted variable that acts a boolean
   * that determines which disjunct is "on".*)
  let to_mfa srk phi =
    (* We first subsitute in for each existentially quantified variable
     * a new variable symbol. This results in each universal quantifier 
     * having debruijn index 0 and makes the merging function that follows
     * easier. We undo this substitution prior to the end of this [pmfa_to_lia].*)
    let new_vars = ref (Symbol.Set.empty) in 
    let rec subst_existentials subst_lst expr =
      match Formula.destruct srk expr with
      | `Quantify (`Exists, name, typ, phi) ->
        let new_subst_var = mk_symbol srk ~name (typ :> typ) in
        new_vars := Symbol.Set.add new_subst_var (!new_vars);
        subst_existentials ((mk_const srk new_subst_var) :: subst_lst) phi
      | `And conjuncts -> 
        mk_and srk (List.map (subst_existentials subst_lst) conjuncts)
      | `Or disjuncts ->
        mk_or srk (List.map (subst_existentials subst_lst) disjuncts)
      | open_form ->
        substitute
          srk
          (fun (i, _) -> List.nth subst_lst i)
          (Formula.construct srk open_form)
    in
    let phi = subst_existentials [] phi in
    let rec merge_univ merge_eqs expr =
      match Formula.destruct srk expr with
      | `Quantify (`Forall, _, `TyInt, phi) -> mk_and srk (phi :: merge_eqs)
      | `And conjs -> mk_and srk (List.map (merge_univ merge_eqs) conjs)
      | `Or disjs ->
        let sym = mk_symbol srk ~name:"casesplit" `TyInt in
        new_vars := Symbol.Set.add sym (!new_vars); 
        let s = mk_const srk sym in
        let append_ind_eqlty ind = mk_eq srk (mk_int srk ind) s ::  merge_eqs in
        mk_or srk (List.mapi (fun ind -> merge_univ (append_ind_eqlty ind)) disjs)
      | open_form -> Formula.construct srk open_form
    in
    let body = merge_univ [] phi in
    (* Note that we haven't actually associated free var 0 of body with a 
     * universal quantifier yet. We do this at the end of [mfa_to_lia]*)
    body, !new_vars


  let mfa_to_lia srk body =
    (* We replace the univ. quant variable with a symbol to simplify the rest
     * of [mfa_to_lia].*)
    let uq_sym = mk_symbol srk ~name:"UQSYM"`TyInt in
    let uq_term = mk_const srk uq_sym in
    let body = 
      substitute srk (fun (i, _) -> if i = 0 then uq_term else assert false) body 
    in
    (* [uqr_syms] is the set of symbols that will be existentially quantified
     * in front of the universal quantifier *)
    let uqr_syms = ref Symbol.Set.empty in
    let get_arr a =
      match ArrTerm.destruct srk a with
      | `App (a, _) -> a
      | _ -> assert false
    in
    (* Maps the term a[i] to an integer symbol where i is the universally
     * quantified var *)
    let uq_read =
      Memo.memo (fun a -> 
          let sym = mk_symbol srk ~name:(show_symbol srk (get_arr a)) `TyInt in
          uqr_syms := Symbol.Set.add sym !uqr_syms;
          sym)
    in
    (* [nuqr_syms] is the set of symbols that will be existentially quantified
     * at the head of the lia formula *)
    let nuqr_syms = ref Symbol.Set.empty in
    let func_consist_reqs : ('a arr_term, 'a arith_term) Hashtbl.t = Hashtbl.create 100 in
    let all_reads = Hashtbl.create 100 in
    (* Maps the term a[i] to an integer symbol where i is not the universally
     * quantified var *)
    let non_uq_read : 'c * 'd -> 'a arith_term =
      Memo.memo (fun (arr, read) ->
          BatHashtbl.modify_def Expr.Set.empty read (Expr.Set.add arr) all_reads;
          Hashtbl.add func_consist_reqs arr read;
          let sym = mk_symbol srk ~name:"NON_EQ_RE" `TyInt in
          nuqr_syms := Symbol.Set.add sym !nuqr_syms;
          mk_const srk sym)
    in
    (* TODO: Make sure that array reads normalized for efficiency; don't want
     * seperate symbol for a[x + y] vs a[y + x]*)
    let rec termalg = function
      | `Select (a, i) -> 
        if ArithTerm.equal i uq_term 
        then (mk_const srk (uq_read a))
        else (non_uq_read (a, i) :> ('a, typ_arith) expr)
      | `Ite (cond, bthen, belse) ->
        mk_ite srk (Formula.eval srk formalg cond) bthen belse
      | open_term -> ArithTerm.construct srk open_term 
    and formalg = function
      | `Atom (`Arith (`Eq, x, y)) -> 
        let lhs = (ArithTerm.eval srk termalg x) in
        let rhs = (ArithTerm.eval srk termalg y) in
        mk_eq srk  lhs rhs   
      | `Atom (`Arith (`Leq, x, y)) ->
        mk_leq srk (ArithTerm.eval srk termalg x) (ArithTerm.eval srk termalg y)
      | `Atom (`Arith(`Lt, x, y)) -> 
        mk_lt srk (ArithTerm.eval srk termalg x) (ArithTerm.eval srk termalg y)
      | open_formula -> Formula.construct srk open_formula
    in
    let reads_replaced = Formula.eval srk formalg body in
    (* TODO: verify - is this correct?... esp in case num =1 *)
    let functional_consistency_clauses =
      List.map (fun (arr, read) ->
          mk_if 
            srk 
            (mk_eq srk uq_term read)
            (mk_eq srk (mk_const srk (uq_read arr)) (non_uq_read (arr, read))))
        (BatHashtbl.to_list func_consist_reqs)
    in
    let matrix = mk_and srk (reads_replaced :: functional_consistency_clauses) in
    let phi' = 
      mk_exists_consts srk (fun sym -> not (Symbol.Set.mem sym !uqr_syms)) matrix 
    in
    let phi' = mk_forall_const srk uq_sym phi' in
    let phi' = mk_exists_consts srk (fun sym -> not (Symbol.Set.mem sym !nuqr_syms)) phi' in
    phi', !nuqr_syms


  let pmfa_to_lia srk phi =


    let phi = eliminate_ite srk phi in
    let phi = rewrite srk ~down:(nnf_rewriter srk) phi in

    let mfa, new_vars = to_mfa srk phi in
    let lia, syms = mfa_to_lia srk mfa in
    let lia = 
      mk_exists_consts srk (fun sym -> (not (Symbol.Set.mem sym new_vars))) lia
    in
    lia, Symbol.Set.union syms new_vars


  (* Integer maps with a constant time "decrement all keys by k" operation *)
  module IncMap = struct
    let empty = BatMap.empty,0
    let add k v (map, c) = (BatMap.add (k - c) v map), c
    (*let remove k (map, c) = BatMap.remove (k - c) map, c*)
    let inc k (map, c) = map, c + k
    (*let mem k (map, c) = BatMap.mem (k - c) map*)
    let find k (map, c) = BatMap.find (k - c) map
    (*let pp srk (map, c) = 
      Log.errorf "C is %n\n" c;
      BatMap.iter (fun s k -> Log.errorf "%n maps to something %a" (s - c) (Expr.pp srk) k) map*)
    (*let union dmap1 (m2, c2)= 
      BatMap.foldi (fun k v m -> add (k + c2) v m) m2 dmap*)
    (*let of_enum e = BatMap.of_enum e, 0*)
  end

  (* Returns an formula in which debruijn indices have been replaced by symbols *)
  let symbolize_quantifiers srk phi =
    let counter = ref 0 in
    let inv_syms = Hashtbl.create 97 in
    let uvar_of_name = Hashtbl.create 97 in
    let syms = Memo.memo (fun sym ->
        let sym' = mk_symbol srk ~name:("S"^(string_of_int !counter)^"_"^(show_symbol srk sym)) (typ_symbol srk sym) in
        counter := !counter + 1;
        Hashtbl.add inv_syms sym' sym;
        sym')
    in
    let rec helper map (phi : ('a, 'typ_fo) expr)  : ('a, 'typ_fo) expr =
      match Expr.destruct_sexpr srk phi with
      | App sym, [] -> mk_const srk (syms sym)
      | App _, _ -> assert false
      | Store, _ -> assert false
      | Var (ind, _), [] ->
        mk_const srk (IncMap.find (ind + 1) map)
      | Exists (name, typ), [phi] ->
        let name = "F"^((string_of_int (!counter))^"_"^name) in  
        let sym = 
          mk_symbol 
            srk 
            ~name
            (typ :> typ)
        in
        let map = IncMap.inc 1 (IncMap.add 0 sym map) in
        counter := !counter + 1;
        ((mk_exists srk ~name typ (Expr.formula_of srk (helper map phi))) :> ('a, typ_fo) expr)
      | Forall (name, typ), [phi] ->
        let name = "F"^(string_of_int (!counter))^"_"^name in
        let sym = 
          mk_symbol 
            srk 
            ~name 
            (typ :> typ)
        in
        let map = IncMap.inc 1 (IncMap.add 0 sym map) in
        counter := !counter + 1;
        Hashtbl.add uvar_of_name name (mk_const srk sym);
        (mk_forall srk ~name typ (Expr.formula_of srk (helper map phi)) :> ('a, typ_fo) expr)
      | label, children -> Expr.construct_sexpr srk label (List.map (helper map) children)
    in
    Expr.formula_of srk (helper (IncMap.empty) phi), inv_syms, uvar_of_name


  (* TODO: equivs *)
  let unsymbolize_quantifiers srk phi inv_syms _renamed univ_names =
    (*TODO : Error, renamed only goes one level deep *)
    let get_og_name name = 
      String.sub name (String.index name '_') ((String.length name) - (String.index name '_'))
    in
    let rec helper map counter (phi : ('a, 'typ_fo) expr)  : ('a, 'typ_fo) expr =
      match Expr.destruct_sexpr srk phi with
      | App sym, [] ->
        let name = show_symbol srk sym in
        begin match String.sub name 0 1 with
          | "S" -> mk_const srk (Hashtbl.find inv_syms sym)
          | "F"
          | "N" ->
            (*let name = 
              if BatHashtbl.mem renamed name then
                BatHashtbl.find renamed name
              else name
            in*)
            let name = BatUref.uget (univ_names name) in
            let order, typ = BatMap.String.find name map in
            mk_var srk (counter - order - 1) typ
          | _ -> mk_const srk sym
        end
      | App _, _ -> assert false
      | Store, _ -> assert false
      | Var _, _ -> assert false
      | Exists (name, typ), [phi] ->
        let map' = BatMap.String.add name (counter, typ) map in
        let name' = get_og_name name in
        ((mk_exists srk ~name:name' typ 
            (Expr.formula_of srk (helper map' (counter + 1) phi))) :> ('a, typ_fo) expr)
      | Forall (name, typ), [phi] ->
        let map' = BatMap.String.add name (counter, typ) map in
        let name' = get_og_name name in
        ((mk_forall srk ~name:name' typ 
            (Expr.formula_of srk (helper map' (counter + 1) phi))) :> ('a, typ_fo) expr)
      | label, children -> Expr.construct_sexpr srk label (List.map (helper map counter) children)
    in
    Expr.formula_of srk (helper (BatMap.String.empty) 0 phi)


  let unskolemize_int_arr srk (phi : 'a formula) =
    let counter = ref 0 in
    let get_og_name name = 
      String.sub name (String.index name '_') ((String.length name) - (String.index name '_'))
    in
    let phi', inv_syms, _uvar_of_name = symbolize_quantifiers srk (phi :> ('a, typ_fo) expr) in
    let arr_reads = BatHashtbl.create 97 in
    let rec replace_reads term =
      match ArithTerm.destruct srk term with
      | `Real q -> mk_real srk q
      | `App (sym, []) -> mk_const srk sym
      | `App _ -> assert false
      | `Var _ -> assert false
      | `Add lst -> mk_add srk (List.map replace_reads lst)
      | `Mul lst -> mk_mul srk (List.map replace_reads lst)
      | `Binop (`Div, a, b) -> mk_div srk (replace_reads a) (replace_reads b)
      | `Binop (`Mod, a, b) -> mk_mod srk (replace_reads a) (replace_reads b)
      | `Unop (`Floor, a) -> mk_floor srk (replace_reads a)
      | `Unop (`Neg, a) -> mk_neg srk (replace_reads a)
      | `Ite _ -> assert false
      | `Select (a, i) ->
        let a_name =
          begin match ArrTerm.destruct srk a with
            | `App (sym, []) -> show_symbol srk sym
            | _ -> 
              assert false
          end
        in
        if BatHashtbl.mem arr_reads a_name then ()
        else BatHashtbl.add arr_reads a_name (Hashtbl.create 97); 
        let a_tbl = BatHashtbl.find arr_reads a_name in
        if BatHashtbl.mem a_tbl i then
          mk_const srk (BatHashtbl.find a_tbl i)
        else(
          let name = 
            "R"^(string_of_int !counter)^(get_og_name a_name)^","
          in
          counter := !counter + 1;
          let sym = mk_symbol srk ~name `TyInt in
          BatHashtbl.add a_tbl i sym;
          mk_const srk sym)
    in
    let elim_arr _ _ = assert false (*(univ, eqpf, phi) a_name =
      let univ = Option.get univ in
      let reads = Hashtbl.find arr_reads a_name in
      let i, a_i = assert false in
        (*match Hashtbl.find_opt reads univ with
        | Some m -> univ, m
        | None -> Hashtbl.find uvar_of_name univ, (mk_symbol srk ~name:("JAKEA") `TyInt)
      in*)
      let func_consist =
        (* TODO: check name not unskolem *)
        (* TODO: add exists *)
        List.map (fun (_, (read, subst)) ->
            mk_if 
              srk 
              (mk_eq srk read i)
              (mk_eq srk (mk_const srk a_i) (mk_const srk subst)))
          (BatHashtbl.to_list reads)
      in
      Some univ, eqpf, mk_and srk (phi :: func_consist)*)
   in
   let renamed_univ = Hashtbl.create 97 in
   let univ_names = Memo.memo (fun name -> BatUref.uref name) in
   let merge_two (univ1, eqpf1, phi1) (univ2, eqpf2, phi2) =
     match univ1, univ2 with
     | None, None -> None, eqpf1 @ eqpf2, mk_and srk [phi1; phi2]
     | Some n, None
     | None, Some n -> Some n, eqpf1 @ eqpf2, mk_and srk [phi1; phi2]
     | Some name1, Some name2 ->
       BatUref.unite (univ_names name1) (univ_names name2);
       Hashtbl.add renamed_univ name2 name1;
       Some name1, eqpf1 @ eqpf2, mk_and srk [phi1; phi2]
   in
   let merge_conjs conjuncts =
     List.fold_left (fun acc disjs ->
         if List.length acc = 0 then disjs else
           List.flatten (List.map (fun disj1 -> List.map (fun disj2 -> merge_two disj1 disj2) acc)
             disjs))
       []
       conjuncts
   in
   let quantify (univ, eqpf, phi) =
     let base = 
       if Option.is_some univ
       then mk_forall srk ~name:(Option.get univ) `TyInt phi
       else phi
     in
     List.fold_left (fun phi (name, typ) -> mk_exists srk ~name typ phi) base eqpf
   in
   let alg = function
     | `Tru -> [(None, [], mk_true srk)]
     | `Fls -> [(None, [], mk_false srk)]
     | `And conjuncts -> merge_conjs conjuncts
     | `Or disjuncts -> List.concat disjuncts
     | `Not disjuncts ->
       [None, [],
       mk_and
         srk
         (List.map (fun disj ->
              match disj with
              | None, [], phi -> mk_not srk phi
              | _ -> assert false)
             disjuncts)]
     | `Quantify (`Exists, name, typ, disjuncts) ->
       begin match typ with
         | `TyArr ->
           List.map (fun disj -> elim_arr disj name) disjuncts
         | _ ->
           List.map (fun (univ, eqpf, phi) -> univ, (name, typ) :: eqpf, phi)
             disjuncts
       end
     | `Quantify (`Forall, name, typ, disjuncts) ->
       List.map (fun disj -> 
           if typ = `TyInt then Some name, [], quantify disj
           else None, [], mk_forall srk ~name typ (quantify disj)) 
         disjuncts
     | `Ite _ -> failwith "unskolemize_int_arr: Unexpected Ite"
     | `Atom (`Arith (op, a, b)) -> 
       [(None, [], 
         Formula.construct 
           srk 
           (`Atom(`Arith(op,
           (replace_reads a),
           (replace_reads b)))))]
     | `Atom _ -> assert false 
     | `Proposition _ -> failwith "Unskolemize_int_arr: Unexpected Prop"
   in
   let phi' =  
   mk_and
     srk
     (List.map 
        (fun disj -> quantify disj)
        (Formula.eval srk alg phi'))
   in
   let res = unsymbolize_quantifiers srk (phi' :> ('a, typ_fo) expr) inv_syms renamed_univ univ_names in
   res



 (* Changes bool syms to int syms... when I wrote this some of the other functions
  * in this module failed with presence of booleans. Need to check if this is still the
  * case if not just fix this. This function messes with types of tr_symbols are that
  * worries me*)
 let unbooleanize srk phi =
      let phi = skolemize srk phi in 
      let symbols = symbols phi in
      let map = Hashtbl.create 97 in
      Symbol.Set.iter (fun ele ->
          let int_sym = mk_symbol srk ~name:(show_symbol srk ele) `TyInt in
          Hashtbl.add map ele int_sym)
        (Symbol.Set.filter (fun ele -> typ_symbol srk ele = `TyBool) symbols);
      let phi_subst = 
        substitute_const 
          srk
          (fun s -> 
             if BatHashtbl.mem map s then
               mk_eq srk (mk_one srk) (mk_const srk (BatHashtbl.find map s))
             else
               mk_const srk s)
          phi
      in
      let bool_constrs =
        BatHashtbl.fold (fun _ sym acc -> 
            mk_or 
              srk 
              [mk_eq srk (mk_const srk sym) (mk_one srk);
               mk_eq srk (mk_const srk sym) (mk_zero srk)] :: acc)
          map
          []
      in
      mk_and srk (phi_subst :: bool_constrs) 


  module Array_analysis (Iter : PreDomain) (Iter2 : PreDomain) = struct

    type 'a t = 
      { 
        proj_ind : Symbol.t;
        arr_map : (Symbol.t, Symbol.t) Hashtbl.t;
        eqs_trs : symbol Symbol.Map.t;
        eqs_ints_trs : symbol Symbol.Map.t;
        iter_trs : (Symbol.t * Symbol.t) list;
        ground_lia : 'a formula;
        arr_only_trs : (symbol * symbol) list;
        skolems : Symbol.Set.t;
        symb_consts : Symbol.t list }


    let arr_eqs srk tf = 
      let alg = function
        | `Atom (`ArrEq (a, b)) ->
          begin match ArrTerm.destruct srk a, ArrTerm.destruct srk b with
            | `App (a, []), `App (b, []) -> [(a, b)]
            | _ -> []
          end
        | `And conjuncts -> List.fold_left List.append [] conjuncts
        | `Quantify (_, _, _, eqs) -> eqs
        | _ -> []
      in
      Formula.eval srk alg (T.formula tf)

    let int_eqs srk tf = 
      let alg = function
        | `Atom (`Arith (`Eq, a, b)) ->
          begin match ArithTerm.destruct srk a, ArithTerm.destruct srk b with
            | `App (a, []), `App (b, []) -> [(a, b)]
            | `Real z, `Add [ele1; ele2]
            | `Add [ele1; ele2], `Real z  ->
              if z = QQ.zero then
                begin match ArithTerm.destruct srk ele1, ArithTerm.destruct srk ele2 with
                  | `Unop (`Neg, a), `App (b, [])
                  | `App (b, []), `Unop (`Neg, a) ->
                    begin match ArithTerm.destruct srk a with
                      | `App (a, []) -> [(a, b)]
                      | _ -> []
                    end
                  | _ -> []
                end
              else []
            | _ -> []
          end
        | `And conjuncts -> List.fold_left List.append [] conjuncts
        | `Quantify (_, _, _, eqs) -> eqs
        | _ -> []
      in
      Formula.eval srk alg (T.formula tf)



    let skolemize_eh_alt srk phi =
      let rec subst_existentials subst_lst syms expr =
        match Formula.destruct srk expr with
        | `Quantify (`Exists, name, typ, phi) ->
          let sym = mk_symbol srk ~name (typ :> typ) in
          let syms' = Symbol.Set.add sym syms in
          subst_existentials (sym :: subst_lst) syms' phi
        | `And conjuncts ->
          let phis, symss =  
            (List.map (subst_existentials subst_lst Symbol.Set.empty) conjuncts)
            |> BatList.split
          in
          mk_and srk phis,
          List.fold_left Symbol.Set.union syms symss
        | `Or disjuncts ->
          let phis, symss =  
            (List.map (subst_existentials subst_lst Symbol.Set.empty) disjuncts)
            |> BatList.split
          in
          mk_or srk phis,
          List.fold_left Symbol.Set.union syms symss
        | open_form ->
          (* TODO: make substitute more efficient *)
          substitute
            srk
            (fun (i, typ) ->
               if List.length subst_lst > i 
               then mk_const srk (List.nth subst_lst i)
               else mk_var srk (i - List.length subst_lst) typ)
            (Formula.construct srk open_form),
          syms
      in
      let phi', syms = subst_existentials [] Symbol.Set.empty phi in
      phi', syms



    let squash_eq_adds srk phi =
      let arith_alg = function
        | `Add terms ->
          let terms' = 
            List.fold_left (fun terms summand ->
                match ArithTerm.destruct srk summand with
                | `Add t -> t @ terms
                | _ -> summand :: terms)
              []
              terms
          in

          let terms_map = 
            List.fold_left (fun map term ->
                match ArithTerm.destruct srk term with
                | `Unop (`Neg, t) -> 
                  BatMap.PMap.modify_def
                    0
                    t
                    (fun c -> c - 1)
                    map
                | _ -> 
                  BatMap.PMap.modify_def
                    0
                    term
                    (fun c -> c + 1)
                    map)
              BatMap.PMap.empty
              terms'
          in
          let terms' =
          BatMap.PMap.foldi (fun term count terms -> 
              if count = 0 then terms
              else if count = 1 then term :: terms
              else if count = (-1) then (mk_neg srk term) :: terms
              else (mk_mul srk [(mk_int srk count); term]) :: terms)
            terms_map
            []
          in
          let res = mk_add srk terms' in
          res
        | term -> ArithTerm.construct srk term
      in
      let mk_op op =
        match op with
        | `Eq -> mk_eq
        | `Lt -> mk_lt
        | `Leq -> mk_leq
      in
      let arr_alg = function 
        | `Store (a, b, c) -> 
          mk_store srk a (ArithTerm.eval srk arith_alg b) (ArithTerm.eval srk arith_alg c)
        | term -> ArrTerm.construct srk term
      in
      let alg = function
        | `Atom (`Arith (op, a, b)) -> 
          (mk_op op) srk (ArithTerm.eval srk arith_alg a) (ArithTerm.eval srk arith_alg b)
        | `Atom (`ArrEq (a, b)) -> mk_arr_eq srk (ArrTerm.eval srk arr_alg a) (ArrTerm.eval srk arr_alg b) 
        | open_phi -> Formula.construct srk open_phi
      in
      Formula.eval srk alg phi



    let abstract srk tf =
      let t1 = time "In abstract" in


      let eqs = arr_eqs srk tf in

      let trs = ref (T.symbols tf) in

      (* this was changed to use pre for map instead of post for term... what
does this affect *)
      let eqs_trs =
        List.fold_left (fun eqs_trs (a, b) ->
            if List.mem (a, b) (T.symbols tf) then (
              Symbol.Map.add b a eqs_trs)
            else if List.mem (b, a) (T.symbols tf) then (
              Symbol.Map.add a b eqs_trs)
            else eqs_trs)
          Symbol.Map.empty
          eqs
    in

    let eqs_ints_trs =
      List.fold_left (fun eqs_trs (a, b) ->
          if List.mem (a, b) (T.symbols tf) then (
            trs := BatList.remove !trs (a, b);
            Symbol.Map.add b a eqs_trs)
          else if List.mem (b, a) (T.symbols tf) then (
            trs := BatList.remove !trs (b, a);
            Symbol.Map.add a b eqs_trs)
          else eqs_trs)
        Symbol.Map.empty
        (int_eqs srk tf)
    in

    (*let eqs_ints_trs = Symbol.Map.empty in*)

    let new_eqs_consts =
      BatEnum.fold (fun set ele ->
          Symbol.Set.add ele set)
        Symbol.Set.empty
        (Symbol.Map.values eqs_ints_trs)
    in

    let phi =
      substitute_sym 
        srk
        (fun s ->
           if Symbol.Map.mem s eqs_trs then (
             mk_const srk (Symbol.Map.find s eqs_trs))
           else if Symbol.Map.mem s eqs_ints_trs then (
             mk_const srk (Symbol.Map.find s eqs_ints_trs))
           else mk_const srk s)
        (T.formula tf)
    in

    let phi = squash_eq_adds srk phi in
    



    let phi = Quantifier.miniscope srk phi in





    let phi = eliminate_ite srk phi in
    let phi = unbooleanize srk phi in


    let tf_pmfa = T.update_formula tf phi in
    let tf_pmfa = T.update_symbols tf_pmfa !trs in
    let proj_ind, arr_map, tf_proj, arr_only_trs, symb_consts = projection_with_store_elim srk tf_pmfa eqs_trs new_eqs_consts in

    Log.errorf "Formula with new proj is %a" (Formula.pp srk) (T.formula tf_proj);

    List.iter (fun (a, b) -> Log.errorf "Symbol is %a and %a" (pp_symbol srk) a (pp_symbol srk) b) (TransitionFormula.symbols tf_proj);
    let tf_proj = T.update_formula tf_proj (eliminate_ite srk (T.formula tf_proj)) in

    let tf_proj = T.update_formula tf_proj (eliminate_stores srk (T.formula tf_proj)) in

    Log.errorf "PRIOR TO LIA is %a" (Formula.pp srk) (T.formula tf_proj);
    let lia, _ = pmfa_to_lia srk (T.formula tf_proj) in


    let lia = 
      Quantifier.eq_guided_qe 
        srk
        (Quantifier.miniscope srk lia)
    in

    let lia = Quantifier.eq_guided_elim_loop srk lia in

    Log.errorf "Phi in abstract is %a" (Formula.pp srk) lia;

    let lia, skolems = skolemize_eh_alt srk lia in 
    let lia = Quantifier.miniscope srk lia in
    let ground_lia = Quantifier.mbp_qe_inplace srk lia in

    Log.errorf "Ground is is %a" (Formula.pp srk) ground_lia;



      let exit_abst = time "Exit ABSTRACT" in
      diff t1 exit_abst "Exit Abstract";
      {
       proj_ind;
       arr_map;
       eqs_trs;
       eqs_ints_trs;
       iter_trs=(T.symbols tf_proj);
       ground_lia;
       arr_only_trs;
       skolems;
       symb_consts
      }

    let at_most_single_write srk write noop trs =

      Log.errorf "NOOP IS %a" (Formula.pp srk) (T.formula noop);
      let exp = mk_symbol srk ~name:"exp" `TyInt in

      let noop_star =
        T.make
          (Iter.exp
             srk 
             trs 
             (mk_const 
                srk 
                exp)
             (Iter.abstract 
                srk 
                noop))
          trs
      in

      let wnstarw = 
        T.mul srk write (T.mul srk noop_star write)
      in
      match Smt.is_sat srk (T.formula wnstarw) with
      | `Sat -> false
      | `Unsat -> true
      | `Unknown -> failwith "at most single unknown"

 
    (*let at_most_single_write _ _ _ _ =
      true*)


    let exp srk _ _lc obj =
      let t1 = time "EXP IN" in

      let arr_vars_eq = 
        mk_and
          srk
          (List.map (fun (z, z') -> mk_eq srk (mk_const srk z) (mk_const srk z')) obj.arr_only_trs)
      in

      let write = mk_and srk [obj.ground_lia; mk_not srk arr_vars_eq] in
      let polka = Polka.manager_alloc_loose () in
      let write =
       rewrite srk ~down:(nnf_rewriter srk) write
      in
      let rewrite_time = time "EXP IN" in
      diff t1 rewrite_time "REWRITE"; 

      let conv = 
        SrkApron.formula_of_property 
          (Abstract.abstract 
             srk 
             ~exists:(fun s -> Symbol.Set.mem s (symbols write) && not (Symbol.Set.mem s obj.skolems))
             polka 
             write) 
      in
      let _write = conv in

      let noop = mk_and srk [obj.ground_lia; arr_vars_eq] in 


      let noop =
        rewrite srk ~down:(nnf_rewriter srk) noop
      in
      
      Log.errorf "write is %a" (Formula.pp srk) write;
      let exists s = not (Symbol.Set.mem s obj.skolems) in
      let write = T.make ~exists write obj.iter_trs in
      let noop = T.make ~exists noop obj.iter_trs in
      let indiff = T.make ~exists obj.ground_lia obj.iter_trs in
 
      let exp1 = mk_symbol srk ~name:"exp1" `TyInt in
      let exp2 = mk_symbol srk ~name:"exp2" `TyInt in


      let prenstar = time "prenstar" in

      diff rewrite_time prenstar "prenstar";
      
      let nstarwnstar = 
        if at_most_single_write srk write noop obj.iter_trs 
        then (
          let noop_star1 =
            T.make
              (Iter.exp
                 srk 
                 obj.iter_trs 
                 (mk_const 
                    srk 
                    exp1)
                 (Iter.abstract 
                    srk 
                    noop))
              obj.iter_trs
          in
          let noop_star1 = T.map_formula (mk_exists_const srk exp1) noop_star1 in
          let noop_star2 =
            T.make
              (Iter.exp
                 srk 
                 obj.iter_trs 
                 (mk_const 
                    srk 
                    exp2)
                 (Iter.abstract 
                    srk 
                    noop))
              obj.iter_trs
          in
          let noop_star2 = T.map_formula (mk_exists_const srk exp2) noop_star2 in
 
          let write_once = 
            T.mul srk noop_star1 (T.mul srk write noop_star2)
          in
          (*let lc_constr = 
            mk_and srk 
              [mk_eq
                 srk
                 lc
                 (mk_add srk [mk_const srk exp1;
                              mk_const srk exp2;
                              mk_int srk 1]);
                 mk_leq srk (mk_zero srk) (mk_const srk exp1);
               mk_leq srk (mk_zero srk) (mk_const srk exp2)]
          in*)
          mk_and 
            srk 
            [mk_exists_consts 
               srk
               (fun s -> (T.exists write_once s))
               (T.formula write_once)]
        )
        else (
          let iter =
             T.make
              (Iter.exp
                 srk 
                 obj.iter_trs 
                 (mk_const 
                    srk 
                    exp1)
                 (Iter.abstract 
                    srk 
          indiff))
              obj.iter_trs
          in
            mk_exists_consts 
               srk
               (fun s -> (exists s) && not (s = exp1))
               (T.formula iter)
              )
      in

      let nstar = time "nstar" in

      diff prenstar nstar "nstar";


      let noop_eqs = 
        List.map 
          (fun (x, x') -> mk_eq srk (mk_const srk x) (mk_const srk x'))
          obj.iter_trs
      in



      let nstarwnstar =
        mk_exists_const srk exp1 nstarwnstar
      in
      let nstarwnstar =
        mk_exists_const srk exp2 nstarwnstar
      in
      let nstarwnstar = 
        Quantifier.eq_guided_qe 
          srk
          (Quantifier.miniscope srk nstarwnstar)
      in


      let nstarwnstar = Quantifier.eq_guided_elim_loop srk nstarwnstar in


      let nstarwnstar = Quantifier.mbp_qe_inplace srk nstarwnstar in





     let nstarmbp = time "nstar" in

     diff nstar nstarmbp "nstarmbp";

     let loop_c = mk_symbol srk `TyInt in


      let nstar =
        Iter2.exp
           srk 
           obj.iter_trs 
           (mk_const srk loop_c)
           (Iter2.abstract
              srk 
              noop)
      in



      let nstar2 =
        Iter.exp
          srk 
          obj.iter_trs 
          (mk_const srk loop_c)
          (Iter.abstract
             srk 
             noop)
      in

      let nstar = mk_and srk [nstar; nstar2] in
      let nstar = mk_exists_const srk loop_c nstar in


      let nstar = Quantifier.mbp_qe_inplace srk nstar in


      let nstarreal = time "nstarreal" in

      diff nstarmbp nstarreal "nstar real";




      let exp_res_pre = 
        mk_or 
          srk 
          [mk_and srk noop_eqs;
            nstar;
           nstarwnstar] 
      in




      (*
       * In exp_res_pre, create equivalence classes of the array
       * projected symbols. If two projections belong to same class,
       * just use one of the two projections and then make arrs eq
       * via arr_eq symbol as a conjunct
       *
       * Big issue: is computing these equiv classes hugely 
       * computationally expensive - solution: heuristics, only
       * compare pre array with post array
       *)
      (* prob still good to do replace before mbp *)
      let eqs_2 = 
        Symbol.Map.fold (fun a b acc ->
            mk_arr_eq srk (mk_const srk a) (mk_const srk b) ::
            acc)
          obj.eqs_trs
          []
      in


    let eqs3 = 
        Symbol.Map.fold (fun a b acc ->
            mk_eq srk (mk_const srk a) (mk_const srk b) ::
            acc)
          obj.eqs_ints_trs
          []
      in



      let map sym =  
        if sym = obj.proj_ind
        then mk_var srk 0 `TyInt
        else if Hashtbl.mem obj.arr_map sym 
        then mk_select srk (mk_const srk (Hashtbl.find obj.arr_map sym)) 
            (mk_var srk 0 `TyInt) 
        else mk_const srk sym
      in
      let substed = substitute_const srk map exp_res_pre in
      let res = (mk_forall srk `TyInt substed) in
      let t2 = time "EXP OUT" in
      diff t1 t2 "EXP";
      let res = mk_and srk (res ::  (eqs_2 @ eqs3)) in
      res


    let pp _ _ _= failwith "todo 10"



  end





    module TLLRF = TerminationLLRF
    module TDTA = TerminationDTA

    let termination_llrf = ref true
    let termination_dta = ref true
    let termination_attractor = ref true
    let termination_phase_analysis = ref true

    (* Attractor region analysis *)
    let attractor_regions srk tf =
      let open Syntax in
      let formula = T.formula tf in
      let attractors =
        BatList.fold_left (fun xs (x, x') ->
            let (x, x') = mk_const srk x, mk_const srk x' in
            let lo =
              let nonincreasing = mk_and srk [formula; mk_leq srk x' x] in
              match SrkZ3.optimize_box srk (mk_and srk [formula; nonincreasing]) [x'] with
              | `Sat [ivl] ->
                (match Interval.lower ivl with
                 | Some lo -> [mk_leq srk (mk_real srk lo) x]
                 | None -> [])
              | _ -> []
            in
            let hi =
              let nondecreasing = mk_and srk [formula; mk_leq srk x x'] in
              match SrkZ3.optimize_box srk (mk_and srk [formula; nondecreasing]) [x'] with
              | `Sat [ivl] ->
                (match Interval.upper ivl with
                 | Some hi -> [mk_leq srk x (mk_real srk hi)]
                 | None -> [])
              | _ -> []
            in
            (lo@hi@xs))
          []
          (T.symbols tf)
      in
      T.map_formula (fun _ -> mk_and srk (formula::attractors)) tf



    module AD = Array_analysis (Iteration.Product(Iteration.LossyTranslation)(Iteration.PolyhedronGuard))
          (Iteration.Product(Iteration.GuardedTranslation)(Iteration.PolyhedronGuard))



    let mp srk tf =
      Log.errorf "FORMULA entry tf is %a" (Formula.pp srk) (T.formula tf);
      (*let sym_to_var = Hashtbl.create 991 in

      let of_symbol sym =
        if Hashtbl.mem sym_to_var sym then
          Some (Hashtbl.find sym_to_var sym)
        else
          None
      in*)
      let abs = AD.abstract srk tf in
      let exists s = not (Symbol.Set.mem s abs.skolems) in
      let tf_iter = T.make ~exists abs.ground_lia abs.iter_trs in
      let flatten_trs =
          List.fold_left (fun flat (x, x') ->
            Log.errorf "Symbol is %a" (pp_symbol srk) x;
            x :: x' :: flat)
            (abs.proj_ind :: abs.symb_consts)
            (abs.iter_trs @ (Symbol.Map.bindings abs.eqs_ints_trs))
      in
      Log.errorf "Formula reduc is %a" (Formula.pp srk) (T.formula tf_iter);
      let mp_lia = 
        (** over-approximate possibly non-terminating conditions for a transition *)
        begin
          let open Syntax in
          let nonterm tf =
            Log.errorf "entry nonterm tf is %a" (Formula.pp srk) (T.formula tf);
            let pre =
              let fresh_skolem =
                Memo.memo (fun sym -> Log.errorf "Dupping sym %a" (pp_symbol srk) sym;
                    mk_const srk (dup_symbol srk sym))
              in
              let subst sym =
                match List.mem sym flatten_trs with
                | true -> mk_const srk sym
                | false -> fresh_skolem sym
              in
              substitute_const srk subst (T.formula tf)
            in
            Log.errorf "pre is %a" (Formula.pp srk) pre;
            let llrf, has_llrf =
              if !termination_llrf then
                if TLLRF.has_llrf srk tf then
                  [Syntax.mk_false srk], true
                else if !termination_attractor
                     && TLLRF.has_llrf srk (attractor_regions srk tf) then
                  [Syntax.mk_false srk], true
                else
                  [pre], false
              else
                (* If LLRF is disabled, default to pre *)
                [pre], false
            in
            let dta =
              (* If LLRF succeeds, then we do not try dta *)
              if (not has_llrf) && !termination_dta then
                [mk_not srk (TDTA.mp srk tf)]
              else []
            in
            let result =
              Syntax.mk_and srk (llrf@dta)
            in
            match Quantifier.simsat srk result with
            | `Unsat -> mk_false srk
            | _ -> result
          in
          if !termination_phase_analysis then begin
    let predicates =
(* Use variable directions & signs as candidate invariants *)
    List.map (fun (x,x') ->
                 let x = mk_const srk x in
                 let x' = mk_const srk x' in

                 Log.errorf "x is %a" (ArithTerm.pp srk) x;
                 [mk_lt srk x x';
                  mk_lt srk x' x;
                  mk_eq srk x x'])
               (T.symbols tf_iter)
             |> List.concat
           in
           Iteration.phase_mp srk predicates tf_iter nonterm
         end else (
          let res = nonterm tf_iter in
          res)
        end
      in

      let mp_lia =  rewrite srk ~down:(nnf_rewriter srk) mp_lia in
      Log.errorf "Formula MP LIA here is %a" (Formula.pp srk) mp_lia;
      let map sym =  
        if sym = abs.proj_ind
        then mk_var srk 0 `TyInt
        else if Hashtbl.mem abs.arr_map sym 
        then mk_select srk (mk_const srk (Hashtbl.find abs.arr_map sym)) 
            (mk_var srk 0 `TyInt) 
        else mk_const srk sym
      in
      let substed = substitute_const srk map mp_lia in
      let res = (mk_forall srk `TyInt substed) in
     Log.errorf "Result after MP is %a" (Formula.pp srk) res;
      res




end
