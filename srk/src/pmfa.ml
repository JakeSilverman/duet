open Syntax
open Chc

(* Replaces existentially bound vars with skolem constants.
 * Return is resulting formula together with set of skolem constants. *)
let skolemize srk phi =
  let new_vars = ref (Symbol.Set.empty) in 
  let rec subst_existentials subst_lst expr =
    match Formula.destruct srk expr with
    | `Quantify (`Exists, name, typ, phi) ->
      let new_subst_var = mk_symbol srk ~name (typ :> typ) in
      new_vars := Symbol.Set.add new_subst_var (!new_vars);
      subst_existentials ((new_subst_var) :: subst_lst) phi
    | `And conjuncts ->
      mk_and srk (List.map (subst_existentials subst_lst) conjuncts)
    | `Or disjuncts ->
      mk_or srk (List.map (subst_existentials subst_lst) disjuncts)
    | open_form ->
      (* TODO: make substitute more efficient *)
      substitute
        srk
        (fun (i, _) -> mk_const srk (List.nth subst_lst i))
        (Formula.construct srk open_form)
  in
  let phi' = subst_existentials [] phi in
  phi', !new_vars

(* Assumes formula has already been skolemized *)
let offset_partitioning srk phi =
  (* We start out by assigning each array sym in phi to its own equiv class. 
   * We evaluate a formula bottom up and merge the equivalence of two arrays
   * if they are related by an array equality or if they both read from the
   * same universally quantified var.*)
  Log.errorf "phi is %a\n" (Formula.pp srk) phi;
  let arrs = 
    Symbol.Set.filter (fun sym -> (typ_symbol srk sym) = `TyArr)  (symbols phi)
  in
  (* A map from arr var syms to BatUref objects. Two arr var syms belong
   * to the same cell if their BatUref holds the same value *)
  let class_map = BatHashtbl.create 97 in
  Symbol.Set.iter (fun sym ->
      BatHashtbl.add class_map sym (BatUref.uref sym))
    arrs;
  (* Merge cells merges unifies the input equivalence classes "cells"
   * into a single cell and then returns a representative var sym for
   * the merged cell *)
  let merge_cells cells =
    List.fold_left (fun acc_cell cell ->
        match acc_cell, cell with
        | None, v -> v
        | v, None -> v
        | Some sym1, Some sym2 ->
          Log.errorf "MERGING %s with %s\n" (show_symbol srk sym1) (show_symbol srk sym2);
          BatUref.unite 
            (BatHashtbl.find class_map sym1) 
            (BatHashtbl.find class_map sym2);
          Some sym1)
      None
      cells
  in
  (* The algebra acts over the universe (base : symbol list, cell : symbol option) 
   * where "base" is the list of base arrays symbols (plural in case of ite)
   * of this array term and "cell" is a representative of the cell of arrays that
   * read from a (not bound within this term) univ quant var.*)
  let rec arr_term_alg = function
    | `App (sym, lst) -> if lst = [] then [Some sym], None 
      else invalid_arg "offset_partitioning: Uninterp func not in pmfa"
    | `Var _ -> invalid_arg "offset_partitioning: must skolemize first"
    | `Ite (phi, (base1, cell1), (base2, cell2)) -> 
      let cell_phi = Formula.eval srk formula_alg phi in
      base1 @ base2, merge_cells [cell_phi; cell1; cell2]
    | `Store ((base_arr, base_cell), i, v) -> 
      let celli, _ = ArithTerm.eval srk arith_term_alg i in
      let cellv, _ = ArithTerm.eval srk arith_term_alg v in
      base_arr, merge_cells [base_cell; celli; cellv]
  (* This algebra has return type (cell : symbol option, var0 : bool) where
   * cell denotes the same thing as in arr_term_alg and var0 denotes whether a
   * term is "var 0 `TyInt"*)
  and arith_term_alg = function
    | `Select (arr, (_, var0)) ->
      let base_arrs, cell = ArrTerm.eval srk arr_term_alg arr in
      if var0 then merge_cells (cell :: base_arrs), false
      else cell, false
    | `Var (i, _) -> if i = 0 then None, true else assert false
    | `Add lst
    | `Mul lst ->
      let cells = List.map (fun (cell, _) -> cell) lst in
      merge_cells cells, false
    | `Binop (_, (cell1, _), (cell2, _)) ->
      merge_cells [cell1; cell2], false
    | `Unop (_, (cell, _)) -> cell, false
    | `Real _ -> None, false
    | `App _ -> None, false
    | `Ite (phi, (cell1, _), (cell2, _)) ->
      let cell_phi = Formula.eval srk formula_alg phi in
      merge_cells [cell_phi; cell1; cell2], false
  and formula_alg = function
    | `Tru
    | `Fls 
    | `Quantify(`Forall, _, _, _) 
    | `Proposition _ -> None
    | `Atom (`Arith (_, x, y)) ->
      let cellx, _ = ArithTerm.eval srk arith_term_alg x in
      let celly, _ = ArithTerm.eval srk arith_term_alg y in
      merge_cells [cellx; celly]
    | `Atom(`ArrEq (a, b)) ->
       let base_arrs1, cell1 = ArrTerm.eval srk arr_term_alg a in
       let base_arrs2, cell2= ArrTerm.eval srk arr_term_alg b in
       (* The univ quant var may not appear in ArrEq atoms *)
       if Option.is_some cell1 || Option.is_some cell2
       then invalid_arg "offset_partitioning: univ quant in ArrEq"
       else (
         let _ = merge_cells (base_arrs1 @ base_arrs2) in
         None)
    | `And cells
    | `Or cells -> merge_cells cells
    | `Not cell -> cell
    | `Ite (cell1, cell2, cell3) -> merge_cells [cell1; cell2; cell3]
    | `Quantify (`Exists, _, _, _) -> assert false 
  in
  let _ = Formula.eval srk formula_alg phi in
  class_map


type chcvar = { rel : Relation.t; param : int} 
[@@deriving ord]

module CHCVar = struct
  type t = chcvar [@@deriving ord]
end

module CHCVarSet = BatSet.Make(CHCVar)

let pmfa_chc_offset_partitioning srk fp =
  let rels = Fp.get_active_relations fp in
  let chc_arr_vars = 
    Relation.Set.fold (fun rel chcvarset ->
        BatList.fold_lefti (fun chcvarset ind typ ->
            if typ = `TyArr then CHCVarSet.add {rel;param=ind} chcvarset
            else chcvarset)
          chcvarset
          (type_of fp rel))
      rels
      CHCVarSet.empty
  in
  let class_map = BatHashtbl.create 97 in
  CHCVarSet.iter (fun chcvar ->
      BatHashtbl.add class_map chcvar (BatUref.uref chcvar))
    chc_arr_vars;
  let merge a b =
    BatUref.unite 
      (BatHashtbl.find class_map a) 
      (BatHashtbl.find class_map b)
  in
  List.iter (fun (hypos, constr, conc) ->
      let skolemized_constr, _ = skolemize srk constr in
      let constr_partitioning = offset_partitioning srk skolemized_constr in
      let cell_reps = BatHashtbl.create 97 in
      List.iter (fun atom ->
          List.iteri (fun ind sym ->
              if (typ_symbol srk sym) = `TyArr &&
                 BatHashtbl.mem constr_partitioning sym 
              then (
                let chcvar = {rel=(rel_of_atom atom);param=ind} in
                let cell = 
                  BatUref.uget (BatHashtbl.find constr_partitioning sym) 
                in 
                if BatHashtbl.mem cell_reps cell then
                  merge (BatHashtbl.find cell_reps cell) chcvar
                else
                  BatHashtbl.add cell_reps cell chcvar)
              else ())
            (params_of_atom atom))
        (conc :: hypos))
    fp.rules;
  let classes = BatHashtbl.map (fun _ uref -> BatUref.uget uref) class_map in
  classes


let verify_offset_candidates srk fp candidates =
  let atom_has_cand atom = Hashtbl.mem candidates (rel_of_atom atom) in
  let atom_candidate atom = 
    List.nth
      (params_of_atom atom) 
      (Hashtbl.find candidates (rel_of_atom atom))
  in
  List.fold_left (fun suitable (hypos, constr, conc) ->
      if not suitable then suitable
      else if not (atom_has_cand conc) then suitable
      else (
        let c_var = atom_candidate conc in 
        let eqs =
          List.fold_left (fun eqs hypo ->
              if not (atom_has_cand hypo) then eqs
              else (
                let h_var = atom_candidate hypo in
                mk_eq srk (mk_const srk c_var) (mk_const srk h_var) :: eqs))
            []
            hypos
        in
        (* TODO: Need to turn constr to LIA *)
        match Smt.entails srk constr (mk_and srk eqs) with
        | `Yes -> true
        | _ -> false))
    true
    fp.rules

let apply_offset_formula srk cell_offsets (free_var_cell : (symbol, chcvar) Hashtbl.t) phi =
  (* We need to assign the existentially quant array vars to a class *)
  let phi = eliminate_stores srk phi in
  let skolemized, consts = skolemize srk phi in
  let arr_consts = Symbol.Set.filter (fun sym -> typ_symbol srk sym = `TyArr) consts in
  let constr_partitioning = offset_partitioning srk skolemized in
  let constr_partitioning = BatHashtbl.map (fun _ uref -> BatUref.uget uref) constr_partitioning in
 
  let cp_fv_reps = BatHashtbl.create 0 in
  let arrs = 
    Symbol.Set.filter (fun sym -> (typ_symbol srk sym) = `TyArr)  (symbols phi)
  in

  Symbol.Set.iter (fun fv ->
      if BatHashtbl.mem constr_partitioning fv then (
        let cp_cell = BatHashtbl.find constr_partitioning fv in
        if BatHashtbl.mem cp_fv_reps cp_cell then ()
        else BatHashtbl.add cp_fv_reps cp_cell fv)
      else ())
    arrs;
  let consts_cell = BatHashtbl.create 0 in
  Symbol.Set.iter (fun const ->
      let cp_cell = BatHashtbl.find constr_partitioning const in
      if BatHashtbl.mem cp_fv_reps cp_cell 
      then (
        BatHashtbl.add 
          consts_cell
          const
          (Some (Hashtbl.find free_var_cell (Hashtbl.find cp_fv_reps cp_cell))))
      else (BatHashtbl.add consts_cell const None))
    arr_consts;
  let offset_cell var =
    if Hashtbl.mem free_var_cell var then
      Some (Hashtbl.find free_var_cell var)
    else Hashtbl.find consts_cell var
  in
  let offset_val var =
    match offset_cell var with
    | None -> None
    | Some cell -> Some (mk_const srk (Hashtbl.find cell_offsets cell))
  in
  let opt_merge lst : 'a option =
    List.fold_left (fun acc opt ->
        match acc, opt with
        | v, None -> v
        | None, v -> v
        | Some v1, Some v2 -> if v1 = v2 then acc 
          else(
            assert false)
      )
      None
      lst
  in
  let rec deduce_cell_formula = function
    | `Tru
    | `Fls -> None
    | `Not cell -> cell
    | `And cells
    | `Or cells -> opt_merge cells
    | `Atom (`Arith (_, s, t)) ->
      let cell term = fst (ArithTerm.eval srk deduce_cell_arith term) in
      opt_merge [cell s; cell t]
    | _ -> assert false
  and deduce_cell_arith = function
    | `Real _
    | `App _ -> None, false
    | `Var _ -> None, true
    | `Add cells_bools
    | `Mul cells_bools -> 
      let cells = List.map fst cells_bools in
      opt_merge cells, false
    | `Binop (_, (cell1, _), (cell2, _)) -> opt_merge [cell1; cell2], false
    | `Unop (_, (cell, _)) -> cell, false
    | `Select (a, (_, var0)) ->
      if var0 then
        deduce_cell_arr a, false
      else None, false
    | `Ite _ -> assert false
  and deduce_cell_arr term =
    match ArrTerm.destruct srk term with
    | `App (sym, []) -> Some (offset_cell sym)
    | _ -> assert false
  in
let rec offset_formula cell phi =
    match Formula.destruct srk phi with
    | `Quantify (`Exists, _, _, _) 
    | `Ite _ -> assert false
    | `Proposition (`App (sym, [])) -> mk_const srk sym
    | `Proposition _ -> assert false
    | `Tru -> mk_true srk
    | `Fls -> mk_false srk
    | `Not phi -> mk_not srk (offset_formula cell phi)
    | `And conjuncts -> 
      mk_and srk (List.map (offset_formula cell) conjuncts)
    | `Or disjuncts ->
      mk_or srk (List.map (offset_formula cell) disjuncts)
    | `Atom (`Arith (_, a, b)) -> 
      (* TODO: mk_compare *)mk_eq srk (offset_arith cell a) (offset_arith cell b)
    | `Atom (`ArrEq _) -> assert false
    | `Quantify (`Forall, name, _, phi) ->
      let cell_opt = Formula.eval srk deduce_cell_formula phi in
      let cell = match cell_opt with | None -> None | Some v -> v in
      let cell_val = match cell with | None -> None | Some cell -> Some (mk_const srk (Hashtbl.find cell_offsets cell)) in
      mk_forall srk ~name `TyInt (offset_formula cell_val phi)
  and offset_arith equiv_class term =
    let map = offset_arith equiv_class in
    match ArithTerm.destruct srk term with
    | `Real _ -> term
    | `Var (i, `TyInt) ->
      if i = 0 then match equiv_class with
        | None -> term
        | Some v -> mk_add srk [term; v]
      else assert false
    | `Var _ -> assert false
    | `App (_, []) -> term
    | `App _ -> assert false
    | `Add terms -> mk_add srk (List.map map terms)
    | `Mul terms -> mk_mul srk (List.map map terms)
    | `Binop (`Div, s, t) -> mk_div srk (map s) (map t)
    | `Binop (`Mod, s, t) -> mk_mod srk (map s) (map t)
    | `Unop (`Floor, s) -> mk_floor srk (map s)
    | `Unop (`Neg, s) -> mk_neg srk (map s)
    | `Select (a, i) ->
      if i = mk_var srk 0 `TyInt 
      then mk_select srk a i
      else (
        let arr_sym = offset_arr a in
        match offset_val arr_sym with
        | None -> mk_select srk a i
        | Some v -> mk_select srk a (mk_sub srk i v))
    | `Ite _ -> assert false
  and offset_arr term =
    match ArrTerm.destruct srk term with
    | `App (sym, []) -> sym
    | _ -> assert false
  in
  let skolemized_w_offsets = offset_formula None skolemized in
  skolemized_w_offsets

(* Need class -> var; var -> class *)
let apply_offset_candidates srk fp (chcvar_to_class :  (chcvar, chcvar) Hashtbl.t)  class_candidates =
  let rules' = 
    List.map (fun (hypos, constr, conc) ->
        let var_to_class = Hashtbl.create 97 in
        let class_to_candidate = Hashtbl.create 97 in
        BatList.iter (fun atom ->
            BatList.iteri (fun i param ->
                if (typ_symbol srk param) = `TyArr 
                then
                  (
                  let param_class = 
                    Hashtbl.find chcvar_to_class {rel = rel_of_atom atom; param=i} 
                  in
                  Hashtbl.add var_to_class param param_class)
                else ())
              (params_of_atom atom);
            BatHashtbl.iter (fun class_cell class_cands ->
                if Hashtbl.mem class_cands (rel_of_atom atom) then
                  (
                  Hashtbl.add class_to_candidate class_cell (List.nth (params_of_atom atom) (Hashtbl.find class_cands (rel_of_atom atom))))
                else ())
              class_candidates)
          (conc :: hypos);
        let constr' = apply_offset_formula srk class_to_candidate var_to_class constr in
        hypos, constr', conc)
      fp.rules
  in
  fp.rules <- rules'

let propose_offset_candidates_seahorn srk fp classes =
  let names_selected = Hashtbl.create 97 in
  let candidates = Hashtbl.create 97 in
  let param_reps = Hashtbl.create 97 in
  List.iter (fun (hypos, _, conc) ->
      List.iter (fun atom ->
          if Hashtbl.mem param_reps (rel_of_atom atom) then ()
          else Hashtbl.add param_reps (rel_of_atom atom) (params_of_atom atom))
        (conc :: hypos))
    fp.rules;
  BatHashtbl.iter (fun chcvarin chcvarclass ->
      if not (Hashtbl.mem candidates chcvarclass)
      then Hashtbl.add candidates chcvarclass (BatHashtbl.create 97)
      else ();
      if Hashtbl.mem (Hashtbl.find candidates chcvarclass) chcvarin.rel
      then ()
      else (
        let params = Hashtbl.find param_reps chcvarin.rel in
        if Hashtbl.mem names_selected chcvarclass then (
          let name = Hashtbl.find names_selected chcvarclass in
          let ind, _ = BatList.findi (fun _ var -> (show_symbol srk var) = name) params in
          Hashtbl.add (Hashtbl.find candidates chcvarclass) chcvarin.rel ind
        )
        else (
          let var, ind = 
            BatList.hd 
              (BatList.rev ((BatList.filteri_map (fun ind var -> 
                   if BatString.starts_with (show_symbol srk var) 
                       "main@%_" && ind <= chcvarclass.param 
                   then(Log.errorf "name is %s\n" (show_symbol srk var);
                     Some (var, ind))
                   else None)
                   params)))
          in
          Hashtbl.add names_selected chcvarclass (show_symbol srk var);
          Hashtbl.add (Hashtbl.find candidates chcvarclass) chcvarin.rel ind
        )
      ))
  classes;
  candidates
