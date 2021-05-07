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


module OldPmfa = struct
  open Syntax
  open BatPervasives
  open Iteration
  module V = Linear.QQVector
  module M = Linear.QQMatrix
  module Z = Linear.ZZVector
  module H = Abstract
  module T = TransitionFormula
  include Log.Make(struct let name = "srk.array:" end)

  let time s =
    let t = Unix.gettimeofday () in
    Log.errorf "\n%s Curr time: %fs\n" s (t); t

  let diff t1 t2 s =
    Log.errorf "\n%s Execution time: %fs\n" s (t2 -. t1)

  let arr_trs srk tf = 
    List.filter (fun (s, _) -> typ_symbol srk s = `TyArr) (T.symbols tf)

  let int_trs srk tf =
    List.filter (fun (s, _) -> (typ_symbol srk s = `TyInt)) (T.symbols tf)

  let flatten syms = List.fold_left (fun acc (sym, sym') -> sym :: sym' :: acc) [] syms 

  (** Subsitute tbl[sym] for sym in phi for any sym that appears in tbl *)
  let tbl_subst srk phi tbl = 
    substitute_const 
      srk 
      (fun sym -> BatHashtbl.find_default tbl sym (mk_const srk sym))
      phi

  (* Projects an array transition formula [tf] down to a single symbolic index
   * [j]. The dynamics of element [j]  of array transition variables (a, a') 
   * are captured with the integer transition variables ([map] a, [map] a'). *)
  let projection srk tf =
    let map = Hashtbl.create (List.length (arr_trs srk tf) * 8 / 3) in
    let j = mk_symbol srk ~name:"j" `TyInt in
    let f (trs, phi) (a, a') = 
      let z = mk_symbol srk ~name:("z"^(show_symbol srk a)) `TyInt in
      let z' = mk_symbol srk ~name:("z'"^(show_symbol srk a')) `TyInt in
      Hashtbl.add map z a;
      Hashtbl.add map z' a';
      (z, z') :: trs,
      mk_and 
        srk 
        [mk_eq srk (mk_const srk z) (mk_select srk (mk_const srk a) (mk_const srk j));
         mk_eq srk (mk_const srk z') (mk_select srk (mk_const srk a') (mk_const srk j));
         phi]
    in
    let integer_trs, phi = 
      List.fold_left f ((j, j) :: int_trs srk tf, T.formula tf) (arr_trs srk tf) 
    in
    (* TODO: This quantifies symbolic constants - is that an issue? *)
    let phi = 
      mk_exists_consts srk (fun sym -> List.mem sym (flatten integer_trs)) phi 
    in
    j, map, T.make phi integer_trs 

  (* Convert from a pmfa formula to an mfa formula.
   * We achieve this by converting the pmfa formula to an equivalent formula
   * in qnf such that there is a single universal quantifier. The key algorithm
   * thus is just a merging of the matrices under potentially many (non-nested) 
   * universal quantifiers. We factor the universal quantifier over disjunction
   * by introducing a new quantified integer sorted variable that acts a boolean
   * and determines which disjunct is "on".*)
  let to_mfa srk tf =
    (* We first subsitute in for each existentially quantified variable
     * a new variable symbol. This allows us to focus solely on the universal
     * quantifiers during the merging function that follows. We undo this
     * substitution prior to the end of this function.*)
    (* TODO: Quantifier elim via equality checking becomes much more difficult 
     * after this step. Make sure a go at it happens prior to this step *)
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
        (* TODO: make substitute more efficient *)
        substitute
          srk
          (fun (i, _) -> List.nth subst_lst i)
          (Formula.construct srk open_form)
    in
    let phi = subst_existentials [] (T.formula tf) in
    (*TODO: If we convert to DNF first, we can likely limit ourselves to introducing
     * only a single new quantifier. This should have payoffs when in comes to
     * eliminating the quantifiers later on *)
    let rec merge_univ merge_eqs expr =
      match Formula.destruct srk expr with
      | `Quantify (`Forall, _, `TyInt, phi) -> mk_and srk (phi :: merge_eqs)
      | `And conjs -> mk_and srk (List.map (merge_univ merge_eqs) conjs)
      | `Or disjs ->
        let sym = mk_symbol srk `TyInt in
        new_vars := Symbol.Set.add sym (!new_vars); 
        let s = mk_const srk sym in
        let append_ind_eqlty ind = mk_eq srk (mk_int srk ind) s ::  merge_eqs in
        mk_or srk (List.mapi (fun ind -> merge_univ (append_ind_eqlty ind)) disjs)
      | open_form -> Formula.construct srk open_form
    in
    let body = merge_univ [] phi in
    mk_forall srk `TyInt body, !new_vars


  let mfa_to_lia srk phi = assert false
    (*let body = 
      match destruct srk phi with
      | `Quantify (`Forall, _, `TyInt, body) -> body
      | _ -> failwith "mfa formula needs to start with leading univ quant"
    in
    (* We are going to introduce a bunch of new quantifiers later on. We set
     * the univ quant var to a symbol to cut down on number of substs performed*)
    let uq_sym = mk_symbol srk `TyInt in
    let uq_term = mk_const srk uq_sym in
    let body = 
      substitute srk (fun (i, _) -> if i = 0 then uq_term else assert false) body 
    in
    let uqr_syms = ref Symbol.Set.empty in
    (* Maps the term a[i] to an integer symbol where i is the universally
     * quantified var *)
    let uq_read =
      Memo.memo (fun _ -> 
          let sym = mk_symbol srk ~name:"SYMREAD"`TyInt in
          uqr_syms := Symbol.Set.add sym !uqr_syms;
          sym)
    in
    let nuqr_syms = ref Symbol.Set.empty in
    let func_consist_reqs : ('a term, 'a term) Hashtbl.t = Hashtbl.create 100 in
    (* Maps the term a[i] to an integer symbol where i is not the universally
     * quantified var *)
    let non_uq_read : 'c * 'd -> 'a term =
      Memo.memo (fun (arr, read) -> 
          Hashtbl.add func_consist_reqs arr read;
          let sym = mk_symbol srk `TyInt in
          nuqr_syms := Symbol.Set.add sym !nuqr_syms;
          mk_const srk sym)
    in
    (* TODO: Make sure that array reads normalized for efficiency *)
    let rec termalg = function
      | `Binop(`Select, a, i) -> 
        if Term.equal i uq_term 
        then (mk_const srk (uq_read a))
        else (non_uq_read (a, i) :> ('a, typ_term) expr)
      | `Ite (cond, bthen, belse) ->
        mk_ite srk (Formula.eval srk formalg cond) bthen belse
      | open_term -> Term.construct srk open_term 
    and formalg = function
      | `Atom (`Eq, x, y) -> 
        let lhs = (Term.eval srk termalg x) in
        let rhs = (Term.eval srk termalg y) in
        mk_eq srk  lhs rhs   
      | `Atom (`Leq, x, y) ->
        mk_leq srk (Term.eval srk termalg x) (Term.eval srk termalg y)
      | `Atom (`Lt, x, y) -> 
        mk_lt srk (Term.eval srk termalg x) (Term.eval srk termalg y)
      | open_formula -> Formula.construct srk open_formula
    in
    let reads_replaced = Formula.eval srk formalg body in
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
    mk_exists_consts srk (fun sym -> not (Symbol.Set.mem sym !nuqr_syms)) phi'
*)
  let pmfa_to_lia srk tf =
    let mfa, new_vars = to_mfa srk tf in
    let lia = mfa_to_lia srk mfa in
    let phi = 
      mk_exists_consts srk (fun sym -> (not (Symbol.Set.mem sym new_vars))) lia
    in
    T.make ~exists:(T.exists tf) phi (T.symbols tf)



  let eliminate_stores srk phi = assert false
  (*  let rec rewrite_store index node =
      match Term.destruct srk node with
      | `Store (a, i, v) ->
        let i = Term.eval srk term_alg i in
        let v = Term.eval srk term_alg v in
        mk_ite srk (mk_eq srk i index) v (rewrite_store index a)
      | `Var (ind, `TyArr) -> mk_select srk (mk_var srk ind `TyArr) index
      | `App (a, []) -> mk_select srk (mk_const srk a) index
      | _ -> assert false (*invalid_arg "ill-formed array store"*)
    and  term_alg = function 
      | `Binop(`Select, a, i) -> rewrite_store i a
      | open_term -> Term.construct srk open_term
    in
    let alg = function
      | `Atom (`Eq, x, y) ->
        begin match expr_typ srk x with
          | `TyArr ->
            let index = mk_symbol srk `TyInt in
            let lhs = rewrite_store (mk_const srk index) x in
            let rhs = rewrite_store (mk_const srk index) y in
            mk_forall_const srk index (mk_eq srk lhs rhs)
          | _ -> mk_eq srk (Term.eval srk term_alg x) (Term.eval srk term_alg y)
        end
      | `Atom (`Lt, x, y) -> 
        mk_lt srk (Term.eval srk term_alg x) (Term.eval srk term_alg y)
      | `Atom (`Leq, x, y) ->
        mk_leq srk (Term.eval srk term_alg x) (Term.eval srk term_alg y)
      | open_formula -> Formula.construct srk open_formula
    in
    Formula.eval srk alg phi

*)


  module Array_analysis (Iter : PreDomain) = struct

    type 'a t = 
      { iter_obj : 'a Iter.t; 
        proj_ind : Symbol.t; 
        arr_map : (Symbol.t, Symbol.t) Hashtbl.t;
        new_trs : (Symbol.t * Symbol.t) list;
        iter_trs : (Symbol.t * Symbol.t) list;
        projed_form : 'a formula;
        flag : bool}

    (* TODO:Clean up and actually use tf*)
    let abstract srk tf =
      let t1 = time "In abstract" in
      let exists = TransitionFormula.exists tf in
      let tr_symbols = TransitionFormula.symbols tf in
      let flag = ref false in
      let tr_symbols = match typ_symbol srk (fst (List.hd tr_symbols)) with
        | `TyBool -> flag := true; List.tl tr_symbols
        | _ -> tr_symbols 
      in
      let tf = T.make ~exists:(T.exists tf) (eliminate_stores srk (T.formula tf)) tr_symbols in
      let proj_ind, arr_map, tf_proj = projection srk tf in
      let lia = pmfa_to_lia srk tf_proj in
      let phi = Quantifier.miniscope srk (T.formula lia) in
      let phi = Quantifier.eq_guided_qe srk phi in
      to_file srk phi "/Users/jakesilverman/Documents/duet/duet/REWRITE.smt2";
      let new_trs = List.filter (fun a -> not (List.mem a tr_symbols)) (T.symbols lia) in
      let ground  = Quantifier.mbp_qe_inplace srk phi in
      let ground_tf = TransitionFormula.make ~exists ground (T.symbols lia) in
      let iter_obj = Iter.abstract srk ground_tf in
      to_file srk ground "/Users/jakesilverman/Documents/duet/duet/GROUND2.smt2";
      let t2 = time "EXIT abstract" in
      diff t1 t2 "ABSTRACT";
      {iter_obj;
       proj_ind;
       arr_map;
       new_trs;
       iter_trs=(T.symbols lia);
       projed_form=ground;
       flag=(!flag)}


    (*let equal _ _ _ _= failwith "todo 5"
      let widen _ _ _ _= failwith "todo 6"
      let join _ _ _ _ = failwith "todo 7"
    *)
    let split_append lst = 
      let a, b = List.split lst in
      a @ b

    let special_step srk fo_trs proj_phi proj_phi_exp temp_lc_sym lc arr_projs proj_ind =
      let step_focus = mk_symbol srk ~name:"s" `TyInt in
      let step_noop = mk_symbol srk ~name:"p" `TyInt in
      let pre_tbl = Hashtbl.create (List.length fo_trs) in
      let post_tbl = Hashtbl.create (List.length fo_trs) in
      let intermediate_tbl = Hashtbl.create (2*(List.length fo_trs)) in
      let inter_syms = ref [] in
      List.iter
        (fun (sym, sym') ->
           if sym = proj_ind then (
             Hashtbl.add pre_tbl sym (mk_const srk sym);
             Hashtbl.add intermediate_tbl sym (mk_const srk sym);
             Hashtbl.add intermediate_tbl sym (mk_const srk sym);
             Hashtbl.add post_tbl sym (mk_const srk sym))
           else (

             let fresh_copy sym = mk_symbol srk ~name:((show_symbol srk sym)^"''") `TyInt in
             let sym'' = fresh_copy sym in
             let sym''' = fresh_copy sym' in
             inter_syms := sym'' :: sym''' :: !inter_syms;
             Hashtbl.add pre_tbl sym' (mk_const srk sym'');
             Hashtbl.add intermediate_tbl sym (mk_const srk sym'');
             Hashtbl.add intermediate_tbl sym' (mk_const srk sym''');
             Hashtbl.add post_tbl sym (mk_const srk sym''')))
        fo_trs;
      let inter_syms = !inter_syms in
      let equalities = 
        List.fold_left 
          (fun eqs (x, x') -> 
             mk_eq srk (mk_const srk x) (Hashtbl.find intermediate_tbl x) ::
             mk_eq srk (mk_const srk x') (Hashtbl.find intermediate_tbl x') ::
             eqs)
          []
          arr_projs
      in
      let neutralize_step_at step =
        Hashtbl.add 
          post_tbl 
          temp_lc_sym 
          (mk_sub srk lc (mk_add srk [mk_int srk 1; mk_const srk step]));
        Hashtbl.add pre_tbl temp_lc_sym (mk_const srk step);
        let res = 
          mk_and
            srk
            [tbl_subst srk proj_phi_exp pre_tbl;
             tbl_subst srk proj_phi intermediate_tbl;
             tbl_subst srk proj_phi_exp post_tbl]
        in
        Hashtbl.remove post_tbl temp_lc_sym;
        Hashtbl.remove pre_tbl temp_lc_sym;
        res
      in
      mk_forall_const
        srk 
        step_focus
        (mk_if
           srk
           (mk_and
              srk
              [mk_leq srk (mk_int srk 0) (mk_const srk step_focus);
               mk_lt srk (mk_const srk step_focus) lc;
               mk_forall_consts
                 srk
                 (fun sym -> not (List.mem sym (step_noop :: inter_syms)))
                 (mk_if
                    srk
                    (mk_and
                       srk
                       [mk_leq srk (mk_int srk 0) (mk_const srk step_noop);
                        mk_lt srk (mk_const srk step_noop) lc;
                        mk_not srk (mk_eq srk (mk_const srk step_focus) (mk_const srk step_noop));
                        neutralize_step_at step_noop])
                    (tbl_subst
                       srk
                       (mk_and 
                          srk 
                          (List.map 
                             (fun (z, z') -> mk_eq srk (mk_const srk z) (mk_const srk z'))
                             arr_projs))
                       intermediate_tbl))])
           (mk_exists_consts
              srk
              (fun sym -> not (List.mem sym inter_syms))
              (mk_and
                 srk
                 (neutralize_step_at step_focus ::
                  tbl_subst srk proj_phi intermediate_tbl ::
                  equalities))))

    let exp srk _ lc obj =
      let t1 = time "EXP IN" in
      let fresh_lc = mk_symbol srk `TyInt in (*this erases relation between lc and syms in iteration... not good*)
      let iter_proj = Iter.exp srk obj.iter_trs (mk_const srk fresh_lc) obj.iter_obj in
      let t3 = time "EXP first" in
      diff t1 t3 "EXP FIRST";
      to_file srk iter_proj "/Users/jakesilverman/Documents/duet/duet/ITER_PROJ2.smt2";
      let lc_syms = Symbol.Set.to_list (symbols lc) in
      let projed = Quantifier.mbp 
          srk 
          (fun sym -> List.mem sym (obj.proj_ind :: fresh_lc :: lc_syms @ (split_append obj.iter_trs)))
          iter_proj
      in
      to_file srk projed "/Users/jakesilverman/Documents/duet/duet/PROJED.smt2";
      to_file srk obj.projed_form "/Users/jakesilverman/Documents/duet/duet/PROJED2.smt2";
      let t4 = time "EXP SPEC PROJ" in
      diff t3 t4 "EXP SPEC PROJ";
      (* Clean up later to make use of transitionformula obj*)
      let noop_all_but_one = special_step srk obj.iter_trs (obj.projed_form) projed fresh_lc lc obj.new_trs obj.proj_ind in
      (*let noop_ground, _ = mbp_qe srk noop_all_but_one false in*)
      let noop_ground = noop_all_but_one in
      to_file srk noop_ground "/Users/jakesilverman/Documents/duet/duet/ITERPRENEW.smt2";  
      let noop_ground = Quantifier.miniscope srk noop_ground in
      let noop_ground = Quantifier.eq_guided_qe srk noop_ground in
      to_file srk noop_ground "/Users/jakesilverman/Documents/duet/duet/REWRITEGROUND.smt2";
      let noop_ground = Quantifier.mbp_qe_inplace srk noop_ground in
      to_file srk noop_ground "/Users/jakesilverman/Documents/duet/duet/GROUNDELIM.smt2";
      let t5 = time "EXP SEC" in
      diff t4 t5 "EXP SEC";
      let projed_right_lc = substitute_const srk (fun sym -> if compare_symbol sym fresh_lc = 0 then lc else mk_const srk sym) projed in
      let noop_eqs = 
        List.map 
          (fun (x, x') -> mk_eq srk (mk_const srk x) (mk_const srk x'))
          obj.iter_trs
      in
      let exp_res_pre = 
        mk_or 
          srk 
          [mk_and srk ((mk_eq srk lc (mk_int srk 0)) :: noop_eqs);
           mk_and srk [noop_ground; projed_right_lc]] 
      in
      let t6 = time "EXP TH" in
      diff t5 t6 "EXP TH";
      let map sym =  
        if sym = obj.proj_ind 
        then mk_var srk 0 `TyInt
        else if Hashtbl.mem obj.arr_map sym 
        then mk_select srk (mk_const srk (Hashtbl.find obj.arr_map sym)) 
            (mk_var srk 0 `TyInt) 
        else mk_const srk sym
      in
      let t7 = time "EXP SIX" in
      diff t6 t7 "EXP SIX";

      let substed = substitute_const srk map exp_res_pre in
      (*SrkSimplify.simplify_terms srk*) let res = (mk_forall srk `TyInt substed) in
      to_file srk res "/Users/jakesilverman/Documents/duet/duet/exp_phi.smt2";
      let t2 = time "EXP OUT" in
      diff t1 t2 "EXP";
      res



    let pp _ _ _= failwith "todo 10"

  end
end
