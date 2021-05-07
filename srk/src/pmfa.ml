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

let skolemize_chc srk fp =
  let rules' = List.map (fun (hypo, rule, conc) -> 
      hypo, fst (skolemize srk rule), conc) fp.rules in
  fp.rules<-rules'

(* Assumes formula has already been skolemized *)
let offset_partitioning srk phi =
  (* We start out by assigning each array sym in phi to its own equiv class. 
   * We evaluate a formula bottom up and merge the equivalence of two arrays
   * if they are related by an array equality or if they both read from the
   * same universally quantified var.*)
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
  let rules_fv_cells = BatHashtbl.create 97 in
  List.iteri (fun ind (hypos, constr, conc) ->
      let constr_partitioning = offset_partitioning srk constr in
      let fv_to_cells = BatHashtbl.create 97 in
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
        (conc :: hypos);
      BatHashtbl.iter (fun fv cell ->
          let cell = BatUref.uget cell in
          if BatHashtbl.mem cell_reps cell then
            BatHashtbl.add fv_to_cells fv (Some (BatHashtbl.find class_map (BatHashtbl.find cell_reps cell)))
          else BatHashtbl.add fv_to_cells fv None)
        constr_partitioning;
      BatHashtbl.add rules_fv_cells ind fv_to_cells
    )
    fp.rules;
  let classes = BatHashtbl.map (fun _ uref -> BatUref.uget uref) class_map in
  let rules_fv_cells = BatHashtbl.map (fun _ fv_to_cells -> 
      BatHashtbl.map (fun _ uref_opt -> 
          match uref_opt with
          | None -> None
          | Some uref -> Some (BatUref.uget uref))
        fv_to_cells)
      rules_fv_cells
  in
  classes, rules_fv_cells


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
(* In the function apply_offset_formula we label each expression with an 
 * associated element of type offset. The offset is the value by which we
 * value by which we must increment the free var "0" where it does not occur
 * in an select term. DNA, does not apply, means that the expression cannot
 * contain the free var "0". Cell is the case where the increment must be by 
 * by a fixed term and unrestricted is the case where the offset has not yet
 * been locked to a specific term. *)
type cell = Symbol of symbol | Zero
type offset = DNA | Cell of cell | Unrestricted

let apply_offset_formula srk arr_var_offsets phi =
  Log.errorf "phi is %a\n" (Formula.pp srk) phi;
  let merge_cells cells =
    List.fold_left (fun acc cell ->
        match acc, cell with
        | v, Unrestricted -> v
        | Unrestricted, v -> v
        | Cell c1, Cell c2 -> if c1 = c2 then Cell c1 else assert false
        | DNA, DNA -> DNA
        | _ -> assert false)
      Unrestricted
      cells
  in
  let offset = mk_symbol ~name:"offset" srk `TyInt in
  let rec apply_offset_formula = function
    | `Tru -> mk_true srk, Unrestricted
    | `Fls -> mk_false srk, Unrestricted
    | `Not (phi, cell) -> mk_not srk phi, cell
    | `And objs -> 
      let phis, cells = List.split objs in
      mk_and srk phis, merge_cells cells
    | `Or objs ->
      let phis, cells = List.split objs in
      mk_or srk phis, merge_cells cells 
    | `Atom (`Arith (op, s, t)) ->
      let op = match op with | `Eq -> mk_eq | `Lt -> mk_lt | `Leq -> mk_leq in
      let (s, (cells, _)) = ArithTerm.eval srk apply_offset_arith s in
      let (t, (cellt, _)) = ArithTerm.eval srk apply_offset_arith t in
      op srk s t, merge_cells [cells; cellt]
    | `Atom(`ArrEq (a, b)) ->
      let a, _, cella = ArrTerm.eval srk apply_offset_arr a in
      let b, _, cellb = ArrTerm.eval srk apply_offset_arr b in
      let cell = merge_cells [cella; cellb] in
      if cell = Unrestricted || cell = DNA then
        mk_arr_eq srk a b, DNA
      else assert false
    | `Quantify (`Forall, name, `TyInt, (phi, cell)) ->
      let subst offset_term = 
        substitute_const 
          srk 
          (fun sym -> if sym = offset then offset_term else mk_const srk sym)
          phi
      in
      begin match cell with
        | DNA -> assert false
        | Cell (Symbol sym) ->
          mk_forall srk ~name `TyInt (subst (mk_const srk sym)), DNA
        | Cell (Zero)  
        | Unrestricted -> mk_forall srk ~name `TyInt (subst (mk_zero srk)), DNA
      end
    | `Proposition (`App (sym, [])) -> mk_const srk sym, Unrestricted
    | `Ite ((phi1, cell1), (phi2, cell2), (phi3, cell3)) ->
      mk_ite srk phi1 phi2 phi3, merge_cells [cell1; cell2; cell3]
    | `Proposition _ -> assert false
    | `Quantify _ -> assert false
  and apply_offset_arith = function
    | `Real q -> mk_real srk q, (Unrestricted, false)
    | `App (sym, []) -> mk_const srk sym, (Unrestricted, false)
    | `Var (0, `TyInt)  -> 
      mk_add srk [mk_var srk 0 `TyInt; mk_const srk offset], (Unrestricted, true)
    | `Add objs -> 
      let terms, cells_bools = BatList.split objs in
      let cells, _ = BatList.split cells_bools in
      mk_add srk terms, (merge_cells cells, false)
    | `Mul objs ->
      let terms, cells_bools = BatList.split objs in
      let cells, _ = BatList.split cells_bools in
      mk_mul srk terms, (merge_cells cells, false)
    | `Binop (op, (term1, (cell1, _)), (term2, (cell2, _))) ->
      let op = match op with `Div -> mk_div srk | `Mod -> mk_mod srk in
      op term1 term2, (merge_cells [cell1; cell2], false)
    | `Unop (op, (term, (cell, _))) -> 
      let op = match op with `Floor -> mk_floor srk | `Neg -> mk_neg srk in
      op term, (cell, false)
    | `Select (a, (term, (cell, var0))) ->
      let a, base_arr_cell, cella = ArrTerm.eval srk apply_offset_arr a in
      if var0 then
        mk_select srk a (mk_var srk 0 `TyInt), (merge_cells [base_arr_cell; cella], false)
      else begin match base_arr_cell with
        | Cell (Zero) -> mk_select srk a term, (merge_cells [cell; cella], false)
        | Cell(Symbol(sym)) -> mk_select srk a (mk_sub srk term (mk_const srk sym)), (merge_cells [cell; cella], false) 
        | _ -> assert false
      end
    | `Ite (phi, (term1, (cell1, _)), (term2, (cell2, _))) ->
      let phi, cell_phi = Formula.eval srk apply_offset_formula phi in
      mk_ite srk phi term1 term2, (merge_cells [cell_phi; cell1; cell2], false)
    | _ -> assert false 
  and apply_offset_arr = function
    | `App (sym, []) -> mk_const srk sym, Hashtbl.find arr_var_offsets sym, Unrestricted 
    | `Ite (phi, (term1, base_cell1, cell1), (term2, base_cell2, cell2)) ->
      let phi, cell_phi = Formula.eval srk apply_offset_formula phi in
      mk_ite srk phi term1 term2, 
      merge_cells [base_cell1; base_cell2],
      merge_cells [cell1; cell2; cell_phi]
    | `Store ((a, base_cell, cell), i, v) ->
      let i, (celli, _) = ArithTerm.eval srk apply_offset_arith i in
      let i_offset =
        match base_cell with
        | Cell (Zero) -> i
        | Cell(Symbol(sym)) -> (mk_sub srk i (mk_const srk sym)) 
        | _ -> assert false
      in

      let v, (cellv, _) = ArithTerm.eval srk apply_offset_arith v in
      mk_store srk a i_offset v, base_cell, merge_cells [cell; celli; cellv]
    | _ -> assert false
  in
  fst (Formula.eval srk apply_offset_formula phi)

let apply_offset_candidates srk fp rule_cells class_candidates =
  let rules' = 
    List.mapi (fun ind (hypos, constr, conc) ->
        let var_to_cell = Hashtbl.create 97 in
        BatHashtbl.iter (fun var cell -> 
            match cell with
            | None -> BatHashtbl.add var_to_cell var (Cell(Zero))
            | Some cell -> BatHashtbl.add var_to_cell var (BatHashtbl.find class_candidates (ind, cell)))
          (BatHashtbl.find rule_cells ind);
        let constr' = apply_offset_formula srk var_to_cell constr in
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


let derive_offset_for_each_rule fp candidates =
  let offset_for_each_rule = BatHashtbl.create 97 in
  List.iteri (fun ind (hypos, _, conc) ->
        List.iter (fun atom ->
            BatHashtbl.iter (fun chcvar rel_ints ->
                if BatHashtbl.mem rel_ints (rel_of_atom atom) then
                  BatHashtbl.add offset_for_each_rule (ind, chcvar) 
                    (Cell (Symbol (List.nth (params_of_atom atom) (BatHashtbl.find rel_ints (rel_of_atom atom)))))
                else ())
              candidates)
          (conc :: hypos))
    fp.rules;
  offset_for_each_rule
