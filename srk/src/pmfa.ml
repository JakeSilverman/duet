open Syntax
open Chc


let typ_symbol_fo srk sym =
    match typ_symbol srk sym with
    | `TyInt -> `TyInt
    | `TyReal -> `TyReal
    | `TyBool -> `TyBool
    | `TyArr -> `TyArr
    | _ -> assert false
 
type 'a collapse_juncts_typ = Phi of 'a formula | Disj of 'a formula list | Conj of 'a formula list
let collapse_juncts srk phi =
  let phiize dumb_factor =
    match dumb_factor with
    | Phi phi -> phi
    | Disj phis -> mk_or srk phis
    | Conj phis -> mk_and srk phis
  in
  let alg = function
    | `And conjs ->
      let nested_conjs, others = 
        BatList.partition_map (fun conj ->
            match conj with
            | Conj phis -> Left phis
            | Phi phi -> Right phi
            | Disj phis -> Right (mk_or srk phis))
          conjs 
      in
      let nested_conjs = List.flatten nested_conjs in
      Conj (nested_conjs @ others)
    | `Or disjs ->
      let nested_disjs, others = 
        BatList.partition_map (fun disj ->
            match disj with
            | Conj phis -> Right (mk_and srk phis)
            | Phi phi -> Right phi
            | Disj phis -> Left phis)
          disjs
      in
      let nested_disjs = List.flatten nested_disjs in
      Disj (nested_disjs @ others)
    | phi -> Phi (Formula.map_construct srk phiize phi)
  in
  phiize (Formula.eval srk alg phi)

 
let collapse_juncts_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, collapse_juncts srk constr) 
    fp




type 'a dumb_factor_typ = Phi of 'a formula | Disj of 'a formula * 'a formula
let dumb_factor srk _flip phi =
  let phiize dumb_factor =
    match dumb_factor with
    | Phi phi -> phi
    | Disj (phi1, phi2) -> mk_or srk [phi1; phi2]
  in
  let alg = function
    | `And conjs ->
      let mode disjs =
        let term_count = BatHashtbl.create 97 in
        List.iter (fun (disj1, disj2) ->
            BatHashtbl.replace
              term_count
              disj1
               ((BatHashtbl.find_default
                  term_count
                  disj1
                  0) + 1);
            BatHashtbl.replace
              term_count
              disj2
              ((BatHashtbl.find_default
                 term_count
                 disj2
                 0) + 1))
          disjs;
        fst 
          (BatHashtbl.fold (fun term amnt (max_term, max_amnt) ->
               if amnt > max_amnt then (term, amnt) else (max_term, max_amnt))
              term_count
              (fst (List.hd disjs), -1))
      in
      let phis, disjs =
        BatList.partition_map (fun fact_typ ->
            match fact_typ with
            | Phi phi -> Left phi
            | Disj (phi1, phi2) -> Right (phi1, phi2))
          conjs
      in
      let rec factor_disjs disjs =
        match disjs with
        | [] -> []
        | _ ->
          let mode_term = mode disjs in
          let disjs', disjs_w_mode_term =
            BatList.partition_map (fun (disj1, disj2) ->
                if disj1 = mode_term then Right disj2
                else if disj2 = mode_term then Right disj1
                else Left (disj1, disj2))
              disjs
          in
         (mk_or srk [mode_term; mk_and srk disjs_w_mode_term]) ::
         (factor_disjs disjs')
      in
      let disjs_factored = factor_disjs disjs in
      Phi (mk_and srk (phis @ disjs_factored))
(*


      let disj_buckets = BatHashtbl.create 97 in
      let phis = 
        List.fold_left (fun (phis : 'a formula list) conj ->
            match conj with
            | Phi phi -> phi :: phis
            | Disj (phi1, phi2) ->
              Log.errorf "in DISJ and phi is %a" (Formula.pp srk) phi1;
              Log.errorf "phis2 is %a" (Formula.pp srk) phi2;
              let phi1, phi2 = if flip then phi1, phi2 else phi1, phi2 in
              BatHashtbl.replace
                disj_buckets
                phi1
                (phi2 ::
                 (BatHashtbl.find_default
                    disj_buckets
                    phi1
                    []));
              phis)
          []
          conjs
      in
      Log.errorf "DONE CONSTRUCT TABLE\n\n\n";
      let phis = 
        BatHashtbl.fold (fun disj1 disj2s phis ->
            if List.length disj2s > 1 then
              (mk_or srk [disj1; mk_and srk disj2s]) :: phis
            else (mk_or srk (disj1 :: disj2s)) :: phis)
          disj_buckets
          phis
      in
      let phi = mk_and srk phis in
      Log.errorf "output is %a\n\n\n" (Formula.pp srk) phi;
      Phi (mk_and srk phis)*)
    | `Or disjs ->
      let disjs = List.map phiize disjs in
      begin match disjs with
        | [dis1; dis2] -> Disj (dis1, dis2) 
        | tl -> Phi (mk_or srk tl)
      end
    | phi -> Phi (Formula.map_construct srk phiize phi)
  in
  phiize (Formula.eval srk alg phi)

(* Replaces existentially bound vars with skolem constants. *)
let skolemize srk phi =
  let decapture_tbl = BatHashtbl.create 97 in
  let subst = 
    Memo.memo (fun (ind, typ) ->
        let sym = mk_symbol srk (typ :> typ) in
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

let skolemize_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, skolemize srk constr) 
    fp


let prenex_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, Formula.prenex srk constr) 
    fp

let dumb_factor_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, dumb_factor srk true constr) 
    fp


let rec check_q_array srk phi =
  match Formula.destruct srk phi with
  | `Quantify (`Exists, _, typ, phi) ->
    if typ = `TyArr then assert false
    else check_q_array srk phi
  | open_phi -> Formula.construct srk open_phi

let check_q_array_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, check_q_array srk constr) 
    fp


let eq_guided_qe srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo,
      (Quantifier.eq_guided_qe srk 

      (dumb_factor srk true 
      (Quantifier.eq_guided_qe srk 
        (Quantifier.miniscope srk
           (dumb_factor srk false 
           (     Quantifier.eq_guided_qe srk 
                   (Quantifier.miniscope srk 
           (
      Quantifier.eq_guided_qe srk 
        (Quantifier.miniscope srk 
           (Quantifier.eq_guided_qe srk (Quantifier.miniscope srk constr)))) ))))))))
    fp



let remove_skol_consts srk phi =
  let alg = function
    | `Tru -> []
    | `Fls -> []
    | `Not _ -> []
    | `And lsts -> List.flatten lsts
    | `Or _ -> []
    | `Atom (`Arith (`Eq, s, t)) ->
      begin match ArithTerm.destruct srk s with
        | `App (sym, []) -> [(sym, (t :> 'a term))]
        | _ -> []
      end
    | `Atom(`ArrEq (a, b)) ->
      begin match ArrTerm.destruct srk a with
        | `App (sym, []) -> [(sym, (b :> 'a term))]
        | _ -> []
      end
    | `Atom _ -> []
    | `Ite _ -> []
    | `Proposition _ -> []
    | `Quantify _ -> assert false
  in
  let rec perform_substs eq_lst phi =
      match eq_lst with
      | [] -> phi
      | (sym, term) :: tl ->
        let subst phi = 
          substitute_const 
            srk 
            (fun s -> if s = sym then term else mk_const srk s)
            phi
        in
        let tl' = 
          List.filter_map (fun (sym2, term2) ->
              if sym = sym2 then None
              else Some (sym2, subst term2))
            tl
        in
        perform_substs tl' (subst phi)
  in
  perform_substs (Formula.eval srk alg phi) phi  


let remove_skol_consts_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, remove_skol_consts srk constr) 
    fp


type arrvar = Sym of symbol | Fv of int

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
      BatHashtbl.add class_map (Sym sym) (BatUref.uref (Sym sym)))
    arrs;
  let vars_to_fv = BatHashtbl.create 97 in
  let subst = 
    Memo.memo (fun (ind, typ) ->
        if typ = `TyArr then (
          BatHashtbl.add class_map (Fv ind) (BatUref.uref (Fv ind));
          let sym = mk_symbol srk (typ :> typ) in
          BatHashtbl.add vars_to_fv sym ind;
          mk_const srk sym
        )
        else (
          let sym = mk_symbol srk (typ :> typ) in
          mk_const srk sym
        ))
  in

  let phi = 
    substitute
      srk
      subst phi
  in
  let sel a1 a2 = 
    match a1, a2 with
    | Fv i, _ -> Fv i
    | _, b -> b
  in
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
            ~sel
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
    | `App (sym, lst) -> if lst = [] then (
        if BatHashtbl.mem vars_to_fv sym then
          [Some (Fv (BatHashtbl.find vars_to_fv sym))], None
        else [Some (Sym sym)], None)
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


type chcvar = { rel : symbol; param : int} 
[@@deriving ord]

module CHCVar = struct
  type t = chcvar [@@deriving ord]
end

module CHCVarSet = BatSet.Make(CHCVar)
(* TODO: CHC with skolem consts *)
let pmfa_chc_offset_partitioning srk fp =
  let rels = Fp.prop_symbols fp in
  let chc_arr_vars = 
    Symbol.Set.fold (fun rel chcvarset ->
        match typ_symbol srk rel with
        | `TyFun (lst, `TyBool) ->
          BatList.fold_lefti (fun chcvarset ind typ ->
              if typ = `TyArr then CHCVarSet.add {rel;param=ind} chcvarset
              else chcvarset)
            chcvarset
            lst
        | _ -> chcvarset)
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
  List.iteri (fun ind (conc, hypos, constr) ->
      Log.errorf "constr is %a" (Formula.pp srk) constr;
      let constr_partitioning = offset_partitioning srk constr in
      let fv_to_cells = BatHashtbl.create 97 in
      let cell_reps = BatHashtbl.create 97 in
      let pcounter = ref 0 in
      List.iter (fun atom ->
          List.iteri (fun ind typ ->
              if typ = `TyArr &&
                 BatHashtbl.mem constr_partitioning (Fv (ind + !pcounter)) 
              then (
                let chcvar = {rel=(Proposition.symbol_of atom);param=ind} in
                let cell = 
                  BatUref.uget (BatHashtbl.find constr_partitioning (Fv (ind + !pcounter))) 
                in
                if BatHashtbl.mem cell_reps cell then
                  merge (BatHashtbl.find cell_reps cell) chcvar
                else
                  BatHashtbl.add cell_reps cell chcvar)
              else ())
            (Proposition.typ_of_params srk atom);
          pcounter := (List.length  (Proposition.typ_of_params srk atom)) + !pcounter
        )
        (conc :: hypos);
      BatHashtbl.iter (fun fv cell ->
          let cell = BatUref.uget cell in
          if BatHashtbl.mem cell_reps cell then
            BatHashtbl.add fv_to_cells fv (Some (BatHashtbl.find class_map (BatHashtbl.find cell_reps cell)))
          else BatHashtbl.add fv_to_cells fv None)
        constr_partitioning;
      BatHashtbl.add rules_fv_cells ind fv_to_cells;
      BatHashtbl.iter (fun chcvarin chcvarclass -> 
          Log.errorf "rel %s param %n belongs to class rel %s param %n"
            (show_symbol srk chcvarin.rel) chcvarin.param (show_symbol srk (BatUref.uget chcvarclass).rel)
            (BatUref.uget chcvarclass).param)
        class_map;
      Log.errorf "\n\n\n\n"
    )
    (Fp.get_rules fp);
  let classes = BatHashtbl.map (fun _ uref -> BatUref.uget uref) class_map in
  let rules_fv_cells = BatHashtbl.map (fun _ fv_to_cells -> 
      BatHashtbl.map (fun _ uref_opt -> 
          match uref_opt with
          | None -> None
          | Some uref -> Some (BatUref.uget uref))
        fv_to_cells)
      rules_fv_cells
  in
  Log.errorf "Therw are a total of %n classes" (BatHashtbl.length classes);
  BatHashtbl.iter (fun chcvarin chcvarclass -> 
      Log.errorf "rel %s param %n belongs to class rel %s param %n"
        (show_symbol srk chcvarin.rel) chcvarin.param (show_symbol srk chcvarclass.rel)
        chcvarclass.param)
    classes;

  classes, rules_fv_cells

(*
let verify_offset_candidates srk fp candidates =
  let atom_has_cand atom = Hashtbl.mem candidates (Proposition.symbol_of atom) in
  let atom_candidate atom = 
    List.nth
      (params_of_atom atom) 
      (Hashtbl.find candidates (Proposition.symbol_of atom))
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
    fp.rules*)
(* In the function apply_offset_formula we label each expression with an 
 * associated element of type offset. The offset is the value by which we
 * value by which we must increment the free var "0" where it does not occur
 * in an select term. DNA, does not apply, means that the expression cannot
 * contain the free var "0". Cell is the case where the increment must be by 
 * by a fixed term and unrestricted is the case where the offset has not yet
 * been locked to a specific term. *)
type cell = Symbol of int | Zero
type offset = DNA | Cell of cell | Unrestricted

let apply_offset_formula srk arr_var_offsets phi props =
  let fv_to_vars = BatHashtbl.create 97 in
  let vars_to_fv = BatHashtbl.create 97 in

  let param_counter = ref 0 in
  List.iter (fun prop ->
      param_counter := !param_counter + List.length (Proposition.typ_of_params srk prop);
    )
    props;

  let subst = 
    Memo.memo (fun (ind, typ) ->
        let sym = mk_symbol srk (typ :> typ) in
        BatHashtbl.add vars_to_fv sym ind;
        BatHashtbl.add fv_to_vars ind sym;
        mk_const srk sym)
  in

  let phi = 
    substitute
      srk
      subst phi
  in

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
          mk_forall srk ~name `TyInt (subst (mk_const srk (Hashtbl.find fv_to_vars sym))), DNA
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
        | Cell (Zero) -> mk_select srk a (mk_floor srk (mk_div srk term (mk_int srk 4))), (merge_cells [cell; cella], false)
        | Cell(Symbol(sym)) -> 
          mk_select srk a (mk_floor srk (mk_div srk (mk_sub srk term (mk_const srk (Hashtbl.find fv_to_vars sym))) (mk_int srk 4))), (merge_cells [cell; cella], false) 
        | _ -> assert false
      end
    | `Ite (phi, (term1, (cell1, _)), (term2, (cell2, _))) ->
      let phi, cell_phi = Formula.eval srk apply_offset_formula phi in
      mk_ite srk phi term1 term2, (merge_cells [cell_phi; cell1; cell2], false)
    | _ -> assert false 
  and apply_offset_arr = function
    | `App (sym, []) -> 
     begin match BatHashtbl.find_option vars_to_fv sym with
      | Some i ->
        mk_const srk sym, Hashtbl.find arr_var_offsets (Fv i), Unrestricted
      | None -> 
        mk_const srk sym, Hashtbl.find arr_var_offsets (Sym sym), Unrestricted 
     end
    | `Ite (phi, (term1, base_cell1, cell1), (term2, base_cell2, cell2)) ->
      let phi, cell_phi = Formula.eval srk apply_offset_formula phi in
      mk_ite srk phi term1 term2, 
      merge_cells [base_cell1; base_cell2],
      merge_cells [cell1; cell2; cell_phi]
    | `Store ((a, base_cell, cell), i, v) ->
      let i, (celli, _) = ArithTerm.eval srk apply_offset_arith i in
      let i_offset =
        match base_cell with
        | Cell (Zero) -> mk_floor srk (mk_div srk i (mk_int srk 4))
        | Cell(Symbol(sym)) -> 
          let res = mk_floor srk (mk_div srk (mk_sub srk i (mk_const srk (Hashtbl.find fv_to_vars sym))) (mk_int srk 4)) in
          res
        | _ -> assert false
      in

      let v, (cellv, _) = ArithTerm.eval srk apply_offset_arith v in
      mk_store srk a i_offset v, base_cell, merge_cells [cell; celli; cellv]
    | _ -> assert false
  in
  
  let phi = fst (Formula.eval srk apply_offset_formula phi) in
  substitute_sym
    srk
    (fun sym ->
       if Hashtbl.mem vars_to_fv sym then
         mk_var srk (Hashtbl.find vars_to_fv sym) (typ_symbol_fo srk sym)
       else mk_const srk sym)
    phi

let apply_offset_candidates srk fp rule_cells class_candidates =
  let map ind (conc, hypos, constr) =  
        let var_to_cell = Hashtbl.create 97 in
        BatHashtbl.iter (fun var cell -> 
            match cell with
            | None -> BatHashtbl.add var_to_cell var (Cell(Zero))
            | Some cell -> 
              Log.errorf "Looking for rule %n cell %s param %n" ind (show_symbol srk cell.rel) cell.param;
              Log.errorf "%a" (Formula.pp srk) constr;
              try 
                BatHashtbl.add var_to_cell var (BatHashtbl.find class_candidates (ind, cell))
              with _ -> BatHashtbl.add var_to_cell var (Cell(Zero))
          )
          (BatHashtbl.find rule_cells ind);
        Log.errorf "no failure";
        let constr' = apply_offset_formula srk var_to_cell constr (conc :: hypos) in
        conc, hypos, constr'
  in
  Fp.mapi_rules map fp



(*let propose_offset_candidates_seahorn _srk fp classes =
  let names_selected = Hashtbl.create 97 in
  let candidates = Hashtbl.create 97 in
  let param_reps = Hashtbl.create 97 in
  List.iter (fun (conc, hypos, _) ->
      List.iter (fun atom ->
          if Hashtbl.mem param_reps (Proposition.symbol_of atom) then ()
          else Hashtbl.add param_reps (Proposition.symbol_of atom) (Proposition.names_of atom))
        (conc :: hypos))
    (Fp.get_rules fp);

  BatHashtbl.iter (fun chcvarin chcvarclass ->
      if not (Hashtbl.mem candidates chcvarclass)
      then Hashtbl.add candidates chcvarclass (BatHashtbl.create 97)
      else ();
      let params = Hashtbl.find param_reps chcvarin.rel in
      if Hashtbl.mem names_selected chcvarclass then ()
      else (
        try
          let var = List.nth params (chcvarin.param - 1) in
          if BatString.starts_with var "main@%_"
          then (
            Hashtbl.add names_selected chcvarclass var
          )
          else (
            let var = List.nth params (chcvarin.param - 2) in
            if BatString.starts_with var "main@%_"
            then (
              Log.errorf "var is %s" var
              (*Hashtbl.add names_selected chcvarclass var*)
            )
            else ()) 
 
        with _ -> ())
    )
    classes;
 *)

let propose_offset_candidates_seahorn srk fp classes =
  let names_selected = Hashtbl.create 97 in
  let candidates = Hashtbl.create 97 in
  let param_reps = Hashtbl.create 97 in
  let extract_pot_offsets constr =
    let alg = function
      | `Tru -> []
      | `Fls -> []
      | `Quantify(_, _, _, lst) -> lst 
      | `Proposition _ -> []
      | `Atom (`Arith (`Eq, x, y)) ->
        begin match ArithTerm.destruct srk x, ArithTerm.destruct srk y with
          | `App (sym, []), `Add [offset; _] -> 
            begin match ArithTerm.destruct srk offset with
              | `Var (ind, `TyInt) -> Log.errorf "sym %s to %n" (show_symbol srk sym) ind; [sym, Fv ind]
              | `App (sym2, []) -> [sym, Sym sym2]
              | _ -> []
            end
          | `App (sym, []), `Var (ind, `TyInt) -> Log.errorf "sym %s to %n" (show_symbol srk sym) ind; [sym, Fv ind]
          | `App (sym, []), `App (sym2, []) -> [sym, Sym sym2]
          | _ -> []
        end
      | `Atom _ -> []
      | `And cells
      | `Or cells -> List.flatten cells
      | `Not cell -> cell
      | `Ite (cell1, cell2, cell3) -> List.flatten [cell1; cell2; cell3]
    in
    Formula.eval srk alg constr
  in
  let extract_stor_and_sels constr =
    let rec ext_terms_formula = function
      | `Tru -> []
      | `Fls -> []
      | `Not lst -> lst
      | `And cells 
      | `Or cells -> List.flatten cells
      | `Atom (`Arith (_, s, t)) ->
        let sterms, _ = ArithTerm.eval srk ext_terms_arith s in
        let tterms, _ = ArithTerm.eval srk ext_terms_arith t in
        sterms @ tterms
      | `Atom(`ArrEq (a, b)) ->
        let _, aterms = ArrTerm.eval srk ext_terms_arr a in
        let _, bterms = ArrTerm.eval srk ext_terms_arr b in
        aterms @ bterms
      | `Quantify (_, _, _, lst) -> lst
      | `Proposition _ -> []
      | `Ite (lst1, lst2, lst3) -> lst1 @ lst2 @ lst3
    and ext_terms_arith = function
      | `Real _ -> [], None
      | `App (sym, []) -> [], Some (Sym sym)
      | `Var (ind, `TyInt)  -> [], Some (Fv ind)
      | `Add objs 
      | `Mul objs ->
        let pairs, _ = BatList.split objs in
        List.flatten pairs, None
      | `Binop (_, (pairs1, _), (pairs2, _)) ->
        pairs1 @ pairs2, None
      | `Unop (_, (pairs, _)) -> 
        pairs, None
      | `Select (a, (pairs, sym)) ->
        let a, apairs = ArrTerm.eval srk ext_terms_arr a in
        begin match a, sym with
        | Some i, Some v -> (i, v) :: pairs @ apairs, None
        | _ -> apairs @ pairs, None
        end
      | `Ite (phi, (pairs2, _), (pairs3, _)) ->
        let phipairs = Formula.eval srk ext_terms_formula phi in
        phipairs @ pairs2 @ pairs3, None
      | _ -> assert false 
    and ext_terms_arr = function
      | `App _ -> None, []
      | `Ite _ -> (* TODO *) None, []
      | `Store ((var, pairs), i, _) ->
        begin match var, ArithTerm.destruct srk i with
          | Some ind, `App (sym, []) -> None, (ind, Sym sym) :: pairs
          | Some ind, `Var (ind2, `TyInt) -> None, (ind, Fv ind2) :: pairs
          | _ -> None, pairs
        end
      | `Var (i, `TyArr) -> Some i, []
    in
    Formula.eval srk ext_terms_formula constr
  in
  let rec rel_param_of ind props = 
    Log.errorf "jere?";
    match props with
    | [] -> assert false
    | hd :: tl ->
      let params = List.length (Chc.Proposition.typ_of_params srk hd) in
      if ind >= params
      then rel_param_of (ind - params) tl
      else hd, ind
  in
  List.iter (fun (conc, hypos, constr) ->
      Log.errorf "constr is %a" (Formula.pp srk) constr;
      let pot_offsets = extract_pot_offsets constr in
      let stor_and_sels = extract_stor_and_sels constr in
      List.iter (fun (arr_ind, sym) ->
          let rel, param = rel_param_of arr_ind (conc :: hypos) in
          let chcvar = {rel=(Chc.Proposition.symbol_of rel); param} in
          Log.errorf "foundbug1?";
          let chcvarclass = BatHashtbl.find classes chcvar in
          Log.errorf "foundbug1 no";
          if not (Hashtbl.mem candidates chcvarclass)
          then Hashtbl.add candidates chcvarclass (BatHashtbl.create 97)
          else ();
          let rec offsetfv sym =
            match sym with
            | Sym sym -> Log.errorf "offseterr %s" (show_symbol srk sym); offsetfv (BatList.assoc sym pot_offsets)
            | Fv fv -> fv
          in
          Log.errorf "YES1234";
          try 
            let reloffset,paramoffset = rel_param_of (offsetfv sym) (conc :: hypos) in
            Log.errorf "ERROR IS HERE";
            let name = List.nth (Chc.Proposition.names_of reloffset) paramoffset in
            Log.errorf "SELECTED %s for %s param number %n" name (show_symbol srk chcvar.rel) param;
            Hashtbl.add names_selected chcvarclass name
          with _ -> ()
        )
        stor_and_sels;
      List.iter (fun atom ->
          if Hashtbl.mem param_reps (Proposition.symbol_of atom) then ()
          else Hashtbl.add param_reps (Proposition.symbol_of atom) (Proposition.names_of atom))
        (conc :: hypos))
    (Fp.get_rules fp);
(*
  BatHashtbl.iter (fun chcvarin chcvarclass ->
      if not (hashtbl.mem candidates chcvarclass)
      then hashtbl.add candidates chcvarclass (bathashtbl.create 97)
      else ();
      let params = Hashtbl.find param_reps chcvarin.rel in
      if Hashtbl.mem names_selected chcvarclass then ()
      else (
        try
          let var = List.nth params (chcvarin.param - 1) in
          if BatString.starts_with var "main@%_"
          then (
            Hashtbl.add names_selected chcvarclass var
          )
          else (
            let var = List.nth params (chcvarin.param - 2) in
            if BatString.starts_with var "main@%_"
            then (
              Log.errorf "var is %s" var
              (*Hashtbl.add names_selected chcvarclass var*)
            )
            else ()) 
 
        with _ -> ())
    )
    classes;
 *)

  BatHashtbl.iter (fun chcvarin chcvarclass ->
      if not (Hashtbl.mem candidates chcvarclass)
      then Hashtbl.add candidates chcvarclass (BatHashtbl.create 97)
      else ();
      Log.errorf "foundbug2?";
      if Hashtbl.mem (Hashtbl.find candidates chcvarclass) chcvarin.rel
      then ()
      else (
        Log.errorf "error here looking for %s" (show_symbol srk chcvarin.rel);
        let params = Hashtbl.find param_reps chcvarin.rel in
        Log.errorf "jkjk";
        if Hashtbl.mem names_selected chcvarclass then (
          try ( 
            Log.errorf "error here?";
            let name = Hashtbl.find names_selected chcvarclass in
            Log.errorf "jkjk2 Looking for %s" name;
            let ind, _ = BatList.findi (fun _ var -> Log.errorf "found %s" var;var = name) params in
            Log.errorf "really here";
            Hashtbl.add (Hashtbl.find candidates chcvarclass) chcvarin.rel (Some ind))
          with
            _ -> Log.errorf "foundbug3";Hashtbl.add (Hashtbl.find candidates chcvarclass) chcvarin.rel None
        )
        else ( 
          Log.errorf "Looking for chcvar %s param %n" (show_symbol srk chcvarin.rel) (chcvarin.param);
          (*failwith "NAME NOT ADDED"*) ())
      ))
  classes;
  candidates


let derive_offset_for_each_rule srk fp candidates =
  let offset_for_each_rule = BatHashtbl.create 97 in
  List.iteri (fun ind (conc, hypos, _) ->
      let param_counter = ref 0 in
      List.iter (fun atom ->
          BatHashtbl.iter (fun chcvar rel_ints ->
                if BatHashtbl.mem rel_ints (Proposition.symbol_of atom) then (
                 match (BatHashtbl.find rel_ints (Proposition.symbol_of atom)) with
                   | Some ind_fv ->
                     if not (BatHashtbl.mem offset_for_each_rule (ind, chcvar))
                        || (BatHashtbl.find offset_for_each_rule (ind, chcvar)) = Cell (Zero) then (
                       Log.errorf "ADDED REAL OFFSET rule %n class %s %n" ind (show_symbol srk chcvar.rel) chcvar.param;
                       BatHashtbl.add offset_for_each_rule (ind, chcvar) 
                         (Cell (Symbol (!param_counter + ind_fv))))
                     else ()
                   | None ->
                     if not (BatHashtbl.mem offset_for_each_rule (ind, chcvar))
                     then (
                       Log.errorf "ADDED ZERO for rule %n class %s %n" ind (show_symbol srk chcvar.rel) chcvar.param;
                       BatHashtbl.add offset_for_each_rule (ind, chcvar) (Cell (Zero)))
                     else ()) 


                else ()
            )
            candidates;
            param_counter := !param_counter + List.length (Proposition.typ_of_params srk atom)
        )
          (conc :: hypos))
    (Fp.get_rules fp);
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

  let time _ =
    let t = Unix.gettimeofday () in
    (*Log.errorf "\n%s Curr time: %fs\n" s (t);*) t

  let diff _ _ _ = ()
    (*Log.errorf "\n%s Execution time: %fs\n" s (t2 -. t1)*)

  let arr_trs srk tf = 
    List.filter (fun (s, _) -> typ_symbol srk s = `TyArr) (T.symbols tf)

  let int_trs srk tf =
    List.filter (fun (s, _) -> (typ_symbol srk s = `TyInt)) (T.symbols tf)

  let flatten syms = List.fold_left (fun acc (sym, sym') -> sym :: sym' :: acc) [] syms 

  (** Subsitute tbl[sym] for sym in phi for any sym that appears in tbl *)
  (*let tbl_subst srk phi tbl = 
    substitute_const 
      srk 
      (fun sym -> BatHashtbl.find_default tbl sym (mk_const srk sym))
      phi
*)
  (* Projects an array transition formula [tf] down to a single symbolic index
   * [j]. The dynamics of element [j]  of array transition variables (a, a') 
   * are captured with the integer transition variables ([map] a, [map] a'). *)
  let projection srk tf =
    let map = Hashtbl.create (List.length (arr_trs srk tf) * 8 / 3) in
    let j = mk_symbol srk ~name:"j" `TyInt in
    let j' = mk_symbol srk ~name:"j'" `TyInt in

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
      List.fold_left f ((j, j') :: int_trs srk tf, T.formula tf) (arr_trs srk tf) 
    in
    (* TODO: This quantifies symbolic constants - is that an issue? *)
    let phi = 
      mk_exists_consts srk (fun sym -> List.mem sym (flatten integer_trs)) phi 
    in
    j, j', map, T.make (mk_and srk [phi; mk_eq srk (mk_const srk j) (mk_const srk j')]) integer_trs 

  (* Convert from a pmfa formula to an mfa formula.
   * We achieve this by converting the pmfa formula to an equivalent formula
   * in qnf such that there is a single universal quantifier. The key algorithm
   * thus is just a merging of the matrices under potentially many (non-nested) 
   * universal quantifiers. We factor the universal quantifier over disjunction
   * by introducing a new quantified integer sorted variable that acts a boolean
   * and determines which disjunct is "on".*)
  let to_mfa srk tf =
    let tf = TransitionFormula.map_formula (eliminate_ite srk) tf in
    Syntax.to_file srk (TransitionFormula.formula tf) "/Users/jakesilverman/Documents/duet/duet/INPUTMFA.smt2";
 
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
        let sym = mk_symbol srk ~name:"casesplit" `TyInt in
        new_vars := Symbol.Set.add sym (!new_vars); 
        let s = mk_const srk sym in
        let append_ind_eqlty ind = mk_eq srk (mk_int srk ind) s ::  merge_eqs in
        mk_or srk (List.mapi (fun ind -> merge_univ (append_ind_eqlty ind)) disjs)
      | open_form -> Formula.construct srk open_form
    in
    let body = merge_univ [] phi in
    mk_forall srk `TyInt body, !new_vars


  let mfa_to_lia srk phi =
    let body = 
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
    let nuqr_syms = ref Symbol.Set.empty in
    let func_consist_reqs : ('a arr_term, 'a arith_term) Hashtbl.t = Hashtbl.create 100 in
    (* Maps the term a[i] to an integer symbol where i is not the universally
     * quantified var *)
    let non_uq_read : 'c * 'd -> 'a arith_term =
      Memo.memo (fun (arr, read) -> 
          Hashtbl.add func_consist_reqs arr read;
          let sym = mk_symbol srk `TyInt in
          nuqr_syms := Symbol.Set.add sym !nuqr_syms;
          mk_const srk sym)
    in
    (* TODO: Make sure that array reads normalized for efficiency *)
    let rec termalg = function
      |  `Select (a, i) -> 
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


  let pmfa_to_lia srk tf =
    let mfa, new_vars = to_mfa srk tf in
    let lia = mfa_to_lia srk mfa in
    let phi = 
      mk_exists_consts srk (fun sym -> (not (Symbol.Set.mem sym new_vars))) lia
    in
    T.make ~exists:(T.exists tf) phi (T.symbols tf)



  
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
    | _ -> assert false (*todo: func app*)
  and  arith_alg = function
    | `Select (a, i) -> rewrite_store i a
    | `Ite (phi, x, y) -> mk_ite srk (Formula.eval srk alg phi) x y
    | open_term -> ArithTerm.construct srk open_term
  and alg = function
    | `Atom (`Arith (op, x, y)) ->
      (mk_op op) srk (ArithTerm.eval srk arith_alg x) (ArithTerm.eval srk arith_alg y)
    | `Atom(`ArrEq (a, b)) -> 
      let index = mk_symbol srk `TyInt in
      let lhs = rewrite_store (mk_const srk index) a in
      let rhs = rewrite_store (mk_const srk index) b in
      mk_forall_const srk index (mk_eq srk lhs rhs)
    | open_formula -> Formula.construct srk open_formula
  in
  Formula.eval srk alg phi

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



  module Array_analysis (Iter : PreDomain) = struct

    type 'a t = 
      { iter_obj : 'a Iter.t; 
        proj_ind : Symbol.t;
        proj_indpost : Symbol.t;
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
      to_file srk (T.formula tf) "/Users/jakesilverman/Documents/duet/duet/abstractphi.smt2";
      let phi = eliminate_stores srk (T.formula tf) in
      to_file srk phi "/Users/jakesilverman/Documents/duet/duet/elimstores.smt2";
      let phi = eliminate_ite srk phi in
      let phi = unbooleanize srk phi in
      let tf = T.make ~exists:(T.exists tf) phi tr_symbols in
      let proj_ind, proj_indpost, arr_map, tf_proj = projection srk tf in
      to_file srk (T.formula tf_proj) "/Users/jakesilverman/Documents/duet/duet/projection.smt2"; 
      let lia = pmfa_to_lia srk tf_proj in
      to_file srk (T.formula lia) "/Users/jakesilverman/Documents/duet/duet/preqoptlia.smt2"; 
      let phi = Quantifier.eq_guided_qe srk (T.formula lia) in
      let new_trs = List.filter (fun a -> not (List.mem a tr_symbols)) (T.symbols lia) in
      let pre_mbp = time "PRE MBP abstract" in
      let ground  = Quantifier.mbp_qe_inplace srk phi in
      let post_mbp = time "POST MBP ABSTRACT" in
      diff pre_mbp post_mbp "Abstract mbp";
      let ground_tf = TransitionFormula.make ~exists ground (T.symbols lia) in
      let iter_obj = Iter.abstract srk ground_tf in
      let exit_abst = time "Exit ABSTRACT" in
      diff t1 exit_abst "Exit Abstract";

      to_file srk ground "/Users/jakesilverman/Documents/duet/duet/GROUND2.smt2";
      {iter_obj;
       proj_ind;
       proj_indpost;
       arr_map;
       new_trs;
       iter_trs=(T.symbols lia);
       projed_form=ground;
       flag=(!flag)}


    (*let equal _ _ _ _= failwith "todo 5"
      let widen _ _ _ _= failwith "todo 6"
      let join _ _ _ _ = failwith "todo 7"
    *)


    type dir_var = Inc of symbol * symbol | Dec of symbol * symbol
    module E = ExpPolynomial

    let directional_vars srk phi trs =
      List.flatten (
        List.filter_map (fun (x, x') ->
            let xt, xt' = mk_const srk x, mk_const srk x' in
            match Smt.entails srk phi (mk_leq srk xt xt'), 
                  Smt.entails srk phi (mk_not srk (mk_lt srk xt xt')) with
            | `Yes, `Yes -> None 
              (*Some [Inc (x, x'); Dec (x, x')]*)
            | `Yes, _ -> 
              Some [Inc (x, x')]
            | _, `Yes -> 
              Some [Dec (x, x')]
            | _ -> 
              None)
          trs)

    let something_direct srk phi trs symb_index directs lc =
      let exp1term = mk_symbol srk ~name:"exp1" `TyInt in
      let exp2term = mk_symbol srk ~name:"exp2" `TyInt in
      List.map (fun direct ->
          match direct with
          | Inc (x, x') ->
            let x = mk_mul srk [mk_int srk 1; mk_const srk x] in
            let x' = mk_mul srk [mk_int srk 1; mk_const srk x'] in
            let j = mk_const srk symb_index in

            let phi1 = mk_and srk [phi; mk_leq srk x j; mk_leq srk x' j] in
            to_file srk phi1 "/Users/jakesilverman/Documents/duet/duet/LTS1.smt2";
            let tr1 = TransitionFormula.make phi1 trs in
            let phi2 = mk_and srk [phi; mk_leq srk x j; mk_lt srk j x'] in
            let phi3 = mk_and srk [phi; mk_not srk (mk_leq srk x j); mk_not srk (mk_leq srk x' j)] in
            let tr3 = TransitionFormula.make phi3 trs in
            let iter_obj1 = Iter.abstract srk tr1 in
            let iter_proj1 = Iter.exp srk trs (mk_const srk exp1term) iter_obj1 in
            let iter_proj1 = mk_and srk [iter_proj1; mk_leq srk x j; mk_leq srk x' j] in  
            to_file srk iter_proj1 "/Users/jakesilverman/Documents/duet/duet/iter-proj1.smt2";
            let polka = Polka.manager_alloc_loose () in

            let convexhull =
              Abstract.abstract srk polka phi2
              |> SrkApron.formula_of_property
            in
            Log.errorf "hull is %a" (Formula.pp srk) convexhull;
            let convexhull = phi2 in
            let iter_obj3 = Iter.abstract srk tr3 in
            let iter_proj3 = Iter.exp srk trs (mk_const srk exp2term) iter_obj3 in
            let iter_proj3 = mk_and srk [iter_proj3; mk_not srk (mk_leq srk x j); mk_not srk (mk_leq srk x' j)] in


            let pretbl = Hashtbl.create 97 in
            let posttbl = Hashtbl.create 97 in
            let exists = ref Symbol.Set.empty in
            List.iter (fun (x, x') ->
                let new_syms = 
                  (mk_symbol srk ~name:((show_symbol srk x)^"'") `TyInt),
                  (mk_symbol srk ~name:((show_symbol srk x')^"''") `TyInt)
                in
                exists := Symbol.Set.add (fst new_syms) !exists;
                exists := Symbol.Set.add (snd new_syms) !exists;
                Hashtbl.add pretbl x new_syms;
                Hashtbl.add posttbl x' new_syms)
              trs;
            let iter1_comp =
              substitute_const 
                srk
                (fun x ->
                   if Hashtbl.mem posttbl x then
                     mk_const srk (fst (Hashtbl.find posttbl x))
                   else mk_const srk x)
                iter_proj1
            in
            let iter3_comp =
              substitute_const 
                srk
                (fun x ->
                   if Hashtbl.mem pretbl x then
                     mk_const srk (snd (Hashtbl.find pretbl x))
                   else mk_const srk x)
                iter_proj3
            in
            let hull_comp =
              substitute_const 
                srk
                (fun x ->
                   if Hashtbl.mem posttbl x then
                     mk_const srk (snd (Hashtbl.find posttbl x))
                   else if Hashtbl.mem pretbl x then
                     mk_const srk (fst (Hashtbl.find pretbl x))
                   else mk_const srk x)
                convexhull
            in
            to_file srk iter1_comp "/Users/jakesilverman/Documents/duet/duet/iter1_comp.smt2";
            let lccnst = mk_and srk [mk_leq srk (mk_zero srk) (mk_const srk exp1term); mk_leq srk (mk_zero srk) (mk_const srk exp2term)] in
            let comp_formula =
              mk_and srk [iter1_comp; iter3_comp; hull_comp;
                          mk_eq 
                            srk 
                            lc 
                            (mk_add srk [mk_const srk exp2term;
                                         mk_const srk exp1term;
                                         mk_int srk 1])]
            in
            let bonly = mk_and srk [iter_proj3; mk_eq srk lc (mk_const srk exp2term)] in
            let aonly =mk_and srk [iter_proj1; mk_eq srk lc (mk_const srk exp1term)] in 
            let entire_formula = 
              mk_or srk
                [aonly;
                 bonly;
                 comp_formula]
                 
            in
            let entire_formula = mk_and srk [entire_formula; lccnst] in
            to_file srk hull_comp "/Users/jakesilverman/Documents/duet/duet/hull.smt2";
            to_file srk comp_formula "/Users/jakesilverman/Documents/duet/duet/hull_comp.smt2";
            to_file srk aonly "/Users/jakesilverman/Documents/duet/duet/aonly.smt2";
            to_file srk bonly "/Users/jakesilverman/Documents/duet/duet/bonly.smt2";
            to_file srk entire_formula "/Users/jakesilverman/Documents/duet/duet/counter.smt2";
            let final =
              mk_exists_consts
                srk
                (fun sym -> not (Symbol.Set.mem sym !exists))
                entire_formula
            in
            to_file srk final "/Users/jakesilverman/Documents/duet/duet/final_quant.smt2";
            let final = mk_exists_const srk exp1term final in
            let final = mk_exists_const srk exp2term final in

            final
            
          | Dec _ -> mk_true srk
            (*Log.errorf "COMPUTING Dec LTS FOR %s %s\n" (show_symbol srk x) (show_symbol srk x');
            let x = mk_mul srk [mk_int srk 4; mk_const srk x] in
            let x' = mk_mul srk [mk_int srk 4; mk_const srk x'] in
            let j = mk_const srk symb_index in

            let phi1 = mk_and srk [phi; mk_not srk (mk_lt srk j x); mk_not srk (mk_lt srk j x')] in
            let tr1 = TransitionFormula.make phi1 trs in
            let lts1 = Lts.abstract_lts srk tr1 in
            let phi2 = mk_and srk [phi; mk_not srk (mk_lt srk j x); mk_lt srk j x'] in
            let tr2 = TransitionFormula.make phi2 trs in
            let lts2 = Lts.abstract_lts srk tr2 in
            let phi3 = mk_and srk [phi; mk_lt srk j x; mk_lt srk j x'] in
            let tr3 = TransitionFormula.make phi3 trs in
            let lts3 = Lts.abstract_lts srk tr3 in
            Log.errorf "lts 1 is %a\n" (Lts.pp ppdim) lts1;
            Log.errorf "lts 2 is %a\n" (Lts.pp ppdim) lts2;
            Log.errorf "lts 3 is %a\n" (Lts.pp ppdim) lts3;
            ()*))
        directs, exp1term, exp2term

    (*let mk_all_eqs srk trs = 
      if List.length trs = 0 then mk_true srk
      else (
        let snds = List.maps (fun (x, x') -> x') trs in
        let sym = mk_const srk (List.hd snd
      )*)

    (*let mk_all_eqs srk (trs : (symbol * symbol) list) =
      let trs = List.filter (fun (x,_) ->
          (show_symbol srk x) != "j") trs 
      in
      if List.length trs = 0 then mk_true srk else
        (
          let snds = List.map (fun (_, x') -> mk_const srk x') trs in
          let sym = List.hd snds in
          mk_and srk (List.map (fun x -> mk_eq srk x sym) snds)
        )
*)
    let exp srk _ lc obj =
      let t1 = time "EXP IN" in
      let fresh_lc = mk_symbol srk `TyInt in (*this erases relation between lc and syms in iteration... not good*)
      let iter_proj = Iter.exp srk obj.iter_trs (mk_const srk fresh_lc) obj.iter_obj in
      let t3 = time "EXP first" in
      diff t1 t3 "EXP FIRST";
      to_file srk iter_proj "/Users/jakesilverman/Documents/duet/duet/ITER_PROJ2.smt2";
      to_file srk obj.projed_form "/Users/jakesilverman/Documents/duet/duet/PROJED2.smt2";
      let t4 = time "EXP SPEC PROJ" in
      diff t3 t4 "EXP SPEC PROJ";
      (* Clean up later to make use of transitionformula obj*)
      (*let noop_ground, _ = mbp_qe srk noop_all_but_one false in*)
      let t5 = time "EXP SEC" in
      diff t4 t5 "EXP SEC";

      let directs = directional_vars srk obj.projed_form obj.iter_trs in
      let directs_res, _, _ = something_direct srk obj.projed_form obj.iter_trs obj.proj_ind directs lc in
      let noop_eqs = 
        List.map 
          (fun (x, x') -> mk_eq srk (mk_const srk x) (mk_const srk x'))
          obj.iter_trs
      in
      let direct_res = mk_and srk directs_res in
      (*let direct_res = mk_exists_const srk exp1 direct_res in
      let direct_res = mk_exists_const srk exp2 direct_res in*)
      to_file srk direct_res "/Users/jakesilverman/Documents/duet/duet/DIRECTRESPREMBP.smt2"; 
      let direct_res = Quantifier.mbp_qe_inplace srk direct_res in 
      to_file srk direct_res "/Users/jakesilverman/Documents/duet/duet/DIRECTRES.smt2";
      let exp_res_pre = 
        mk_or 
          srk 
          [mk_and srk ((mk_eq srk lc (mk_int srk 0)) :: noop_eqs);
           mk_and srk [(*noop_ground;*) direct_res(*;projed_right_lc*)]] 
      in
      to_file srk exp_res_pre "/Users/jakesilverman/Documents/duet/duet/exp_phi_pre.smt2";
      let t6 = time "EXP TH" in
      diff t5 t6 "EXP TH";
      let map sym =  
        if sym = obj.proj_ind || sym = obj.proj_indpost 
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
