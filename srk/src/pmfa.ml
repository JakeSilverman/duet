open Syntax
open Chc
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

type chcvar = { sym : symbol; param : int} 

[@@deriving ord]

module CHCVar = struct
  type t = chcvar [@@deriving ord]
end

type vars = Sym of symbol | Fv of int 

[@@deriving ord]

module Vars = struct
  type t = vars [@@deriving ord]
end

module VarSet = BatSet.Make(Vars)

module CVSet = BatSet.Make(CHCVar)

(* TODO:
 * Test
 * Existential Elim
 *)

(* Determines which integer fvs are equal in constr, only considering those
 * free fvs that appear in fvcands *)
let determine_eq_int_fvs srk constr fvcands =
  let syms_to_fvs = Hashtbl.create 97 in
  let fvs_to_syms = Memo.memo (fun (ind, typ) -> 
      let sym = mk_symbol srk ~name:"DET EQS" (typ :> typ) in
      if BatSet.Int.mem ind fvcands 
      then Hashtbl.add syms_to_fvs sym ind 
      else ();
      sym) 
  in
  let constr' = 
    substitute srk (fun fv -> mk_const srk (fvs_to_syms fv)) constr 
  in 
  let cells_syms = 
    BatHashtbl.fold (fun sym _ cells ->
        let rec place_in_cell unchecked_cells =
          match unchecked_cells with
          | [] -> [Symbol.Set.singleton sym]
          | hd :: tl ->
            let rep = Symbol.Set.any hd in
            let eq = (mk_eq srk (mk_const srk sym) (mk_const srk rep)) in  
            begin match Smt.entails srk constr' eq with
                      | `Yes -> (Symbol.Set.add sym hd) :: tl
                      | `No -> hd :: (place_in_cell tl) 
                      | `Unknown -> 
                        failwith "determine_eq_int_fvs failure" 
            end
        in
        place_in_cell cells)
      syms_to_fvs
      []
  in
  let cells_fvs = 
    List.map (fun cell ->
        List.map (fun s -> 
            Hashtbl.find syms_to_fvs s) 
          (Symbol.Set.elements cell)
        |> BatSet.Int.of_list)
      cells_syms
  in
  cells_fvs


let iter_fvs f props =
  let _ = List.fold_left (fun fv_counter prop ->
      BatList.fold_lefti (fun fv_counter' ind _ ->
          f fv_counter' prop ind;
          fv_counter' + 1)
        fv_counter
        (Proposition.names_of prop))
      0
      props
  in
  ()

(* Creates a formula whose models are potential offsets
 * for an array class*)
let create_offset_formula srk fp named_rels offsetcands =
  let term_of (rel, arg) = 
    mk_eq 
      srk 
      (Hashtbl.find named_rels (Proposition.symbol_of rel)) 
      (mk_int srk arg)
  in
  let offsetcands_to_fvs props =
    let fv_of = BatHashtbl.create 97 in
    iter_fvs (fun fv rel param -> 
        BatHashtbl.modify_def 
          BatSet.Int.empty
          (Proposition.symbol_of rel, param)
          (BatSet.Int.add fv)
          fv_of) 
      props;
    BatHashtbl.fold (fun rel params fvs ->
        if Hashtbl.mem named_rels rel  then
          (BatSet.Int.fold (fun param fvs ->
               BatHashtbl.find_default fv_of (rel, param) BatSet.Int.empty 
               |> BatSet.Int.union fvs)
              params
              fvs)
        else fvs)
      offsetcands
      BatSet.Int.empty
  in
  let rule_clauses = 
    List.map (fun (conc, hypo, constr) -> 
        let chcvar_of_fv = Hashtbl.create 97 in
        let congruent_fvs = 
          BatArray.make (List.length (Proposition.names_of conc)) [] 
        in
        iter_fvs (fun fv prop param ->    
            if prop = conc
            then congruent_fvs.(param) <- (fv :: (congruent_fvs.(param)))
            else ();
            Hashtbl.add chcvar_of_fv fv (prop, param))
          (conc :: hypo);
        let fv_cands = offsetcands_to_fvs (conc :: hypo) in
        let classes = determine_eq_int_fvs srk constr fv_cands in
        (* This is pretty inefficient fold, but size of list should be small *)
        let fv_class_lists =
          List.map (fun set ->
              List.fold_left (fun ((non_conc_fvs, conc_fvs), unusable_fvs) fv ->
                  let chcvar = Hashtbl.find chcvar_of_fv fv in
                  if (fv < List.length (Proposition.names_of conc))
                  then (
                    let congruents = congruent_fvs.(fv) in
                    if List.for_all (fun fv -> BatSet.Int.mem fv set) congruents 
                    then ((non_conc_fvs, chcvar :: conc_fvs), unusable_fvs)
                    else ((non_conc_fvs, conc_fvs), chcvar :: unusable_fvs))
                  else ((chcvar :: non_conc_fvs, conc_fvs), unusable_fvs))
                (([], []), [])
                (BatSet.Int.elements set))
            classes
        in
        let potential_eqs, unusables = List.split fv_class_lists in
        let unusables = List.flatten unusables in
        let make_edges (non_conc_fvs, conc_fvs) =
          List.fold_left (fun edges conc_fv ->
              (List.map (fun non_conc_fv ->
                   try mk_and srk [term_of conc_fv; term_of non_conc_fv] with
                   | _ -> mk_false srk) 
                  non_conc_fvs) @
              edges)
            []
            conc_fvs
        in

        let edges_phi =
          mk_or
            srk
            (List.flatten (List.map make_edges potential_eqs))
        in
        let inconsist_clause =
          mk_and
            srk
            (List.map (fun fv -> (mk_not srk (term_of fv))) unusables)
        in
        mk_and srk [edges_phi; inconsist_clause]) 
      (Fp.get_rules fp)
  in
  rule_clauses
 


(* This functions serves two purposes:
 *
 * First, it partitions the array free variables of the input formula
 * such that two variables belong to the same cell if they can related by
 * an equality
 *
 * Next, for each cell of the array fv partition, the function finds a list
 * of integer fv that we might want to use as offset candidates for this cell in
 * this formula. The determination of offset candidates is entirely heuristic.
 *)
let local_partiton_and_cands srk constr int_fvs_set _ =

  (* arr_tbl maps each array variables to its cell in the array partitioning;
   * the cell additional carries along a representative (element of the cell)
   * and a list containing sets of integer variables that are used as indexes
   * to read values from/write values to arrays in this cell, one set for each
   * read/write.
   *
   * int_adj_eqs maps each integer variable to those integer variables that are
   * related to the key integer variable by an equality (direct, not transitive).
   *
   * dir_eqs lets us keep track of free integer variables the are equal and
   * follow the pattern of equalities that we introduce during in chc.ml
   * *)
  let arr_tbl = Memo.memo (fun a -> BatUref.uref (a, [], false)) in
  let int_adj_eqs = BatHashtbl.create 97 in 
  let dir_eqs = Memo.memo (fun fv -> BatUref.uref (BatSet.Int.singleton fv)) in

  let int_varset_of_term term = 
    let varset = 
      BatHashtbl.fold (fun fv typ varset ->
          if typ = `TyInt then VarSet.add (Fv fv) varset else assert false)
        (free_vars term)
        VarSet.empty
    in
    List.map (fun sym -> Sym sym) (Symbol.Set.to_list (symbols term))
    |> VarSet.of_list
    |> VarSet.union varset
  in
  let rec populate_tbls_from_arith phi =
    match ArithTerm.destruct srk phi with
    | `Real _ | `App _ | `Var _ -> ()
    | `Add lst | `Mul lst -> List.iter populate_tbls_from_arith lst
    | `Binop (_, s, t) -> List.iter populate_tbls_from_arith [s; t]
    | `Unop (_, s) -> populate_tbls_from_arith s
    | `Ite _ -> assert false
    | `Select (a, i) ->
      let a = ArrTerm.eval srk arr_term_alg a in
      let a_c, varsets, _ = BatUref.uget (arr_tbl a) in
      BatUref.uset (arr_tbl a) (a_c, (int_varset_of_term i) :: varsets, true);
      populate_tbls_from_arith i 
  and populate_tbls_from_phi phi =
    match Formula.destruct srk phi with
    | `Tru | `Fls | `Proposition _ -> ()
    | `And lst | `Or lst -> List.iter populate_tbls_from_phi lst
    | `Not phi -> populate_tbls_from_phi phi
    | `Quantify _ -> assert false
    | `Atom (`Arith (`Eq, s, t)) ->
      let has_arrays term = 
        (BatHashtbl.length (BatHashtbl.filter (fun a -> a = `TyArr) (free_vars term))) > 0
    || (Symbol.Set.exists (fun sym -> typ_symbol srk sym = `TyArr) (symbols term))
      in
      if has_arrays s || has_arrays t then ( 
        populate_tbls_from_arith s;
        populate_tbls_from_arith t)
      else (
        let int_vars = VarSet.union (int_varset_of_term s)  (int_varset_of_term t) in
        VarSet.iter (fun var -> 
            BatHashtbl.modify_def
              (VarSet.singleton var)
              var
              (VarSet.union int_vars)
              int_adj_eqs)
          int_vars;
        match ArithTerm.destruct srk s, ArithTerm.destruct srk t with
        | `Var (i1, `TyInt) , `Var (i2, `TyInt)  ->
          let sel = BatSet.Int.union in
          BatUref.unite ~sel (dir_eqs i1) (dir_eqs i2)
        | _ -> ())
    | `Atom (`Arith (_, s, t)) -> List.iter populate_tbls_from_arith [s; t]
    | `Atom (`ArrEq (a, b)) ->
      let a = ArrTerm.eval srk arr_term_alg a in
      let b = ArrTerm.eval srk arr_term_alg b in
      let sel (a_c, a_vars, a_rw) (b_c, b_vars, b_rw) = 
        match a_c with
        | Fv _ -> a_c, (a_vars @ b_vars), a_rw || b_rw
        | Sym _ -> b_c, (a_vars @ b_vars), a_rw || b_rw
      in
      BatUref.unite ~sel (arr_tbl a) (arr_tbl b)
    | `Ite _ -> assert false
  and arr_term_alg = function
    | `App (sym, []) -> Sym sym 
    | `Ite _ -> assert false 
    | `Store (arr, i, v) ->
      let a_c, varsets, _ = BatUref.uget (arr_tbl arr) in
      BatUref.uset (arr_tbl arr) (a_c, (int_varset_of_term i) :: varsets, true);
      populate_tbls_from_arith i;
      populate_tbls_from_arith v;
      arr
    | `App _ -> assert false
    | `Var (i, _) -> Fv i
  in
  populate_tbls_from_phi constr;

  let arr_varset = 
    let varset = 
      BatHashtbl.fold (fun fv typ varset ->
          if typ = `TyArr then VarSet.add (Fv fv) varset else varset)
        (free_vars constr)
        VarSet.empty
    in
    List.filter_map 
      (fun sym -> 
         if typ_symbol srk sym = `TyArr then Some (Sym sym)
         else None) 
      (Symbol.Set.to_list (symbols constr))
    |> VarSet.of_list
    |> VarSet.union varset
  in

  let arr_fv_class_and_cands = BatHashtbl.create 99 in
  VarSet.iter (fun var ->
        let arr_class, rwvs, has = BatUref.uget (arr_tbl var) in
        let unwrapped_class = match arr_class with Fv fv -> fv | Sym _ -> 
          assert false in
        let cands =
          BatList.fold_left (fun cands rw_vars ->

              let adj_fvs var =
                BatHashtbl.find_default int_adj_eqs var (VarSet.singleton var)
                |> VarSet.to_list
                |> List.filter_map (fun ele ->
                    match ele with
                    | Sym _ -> None
                    | Fv fv -> Some fv)
                |> BatSet.Int.of_list
              in
              let expanded_fvs fvs =
                BatSet.Int.fold (fun ele new_set ->
                    BatSet.Int.union new_set (BatUref.uget (dir_eqs ele)))
                  fvs
                  BatSet.Int.empty
              in
              (* Determine the fvs that may be a candidate for the current read/write *)
              let inter_with = 
                (VarSet.fold (fun rw_var local_cands ->
                     BatSet.Int.union local_cands (expanded_fvs (adj_fvs (rw_var))))
                    rw_vars
                    BatSet.Int.empty)
              in
              (* Only consider those fvs that may be a candidate for each read/write *)
              BatSet.Int.inter cands inter_with)
            int_fvs_set
            rwvs
        in
        BatHashtbl.add arr_fv_class_and_cands var (unwrapped_class, cands, has))
    arr_varset;
  arr_fv_class_and_cands


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



let determine_offsets srk fp =
  
  let global_partitioning = BatHashtbl.create 97 in
  Symbol.Set.iter (fun sym ->
      match typ_symbol srk sym with
      | `TyFun (lst, _) ->
        List.iteri (fun param typ ->
            if typ = `TyArr then (
              let cell =  
                (BatUref.uref (CVSet.singleton {sym; param}, 
                               Hashtbl.create 97,
                               Symbol.Set.empty,
                               BatSet.Int.empty)) 
              in
              Hashtbl.add global_partitioning {sym; param} cell))
          lst
      | _ -> ())
    (Fp.prop_symbols fp);

  (* Populate partitioning and candidate offsets, one rule at a time *)
  List.iteri (fun rule_num (conc, hypo, constr) ->
      (* Compute a map from constr fvs to chcvars;
       * determine which fvs in constrs are int typed *)
      let fvcounter = ref 0 in
      let temp = Hashtbl.create 50 in
      let int_fvs_set = ref BatSet.Int.empty in
      List.iter (fun prop ->
          List.iteri (fun param typ ->
              Hashtbl.add temp !fvcounter {sym=Proposition.symbol_of prop; param};
              if typ = `TyInt 
              then int_fvs_set := BatSet.Int.add !fvcounter !int_fvs_set 
              else ();
              fvcounter := !fvcounter + 1)
            (Proposition.typ_of_params srk prop))
        (conc :: hypo);
      let chcvar_of fv = Hashtbl.find temp fv in
      let cell_of fv = Hashtbl.find global_partitioning (chcvar_of fv) in

      (* Intersection function for cell offset candidates;
       * Where an no value is infinite set *)
      let intersect tbl1 tbl2 =
        BatHashtbl.merge (fun _ tbl1_entry tbl2_entry ->
            match tbl1_entry, tbl2_entry with
            | Some a, Some b -> Some (BatSet.Int.inter a b) 
            | None, a | a, None -> a)
          tbl1
          tbl2
      in
      (* We build a local partitioning for current rule and then merge
       * it into global partitioning *)
      let flag : bool = 
        BatList.mem "vec_add@_shadow.mem.4.0"
          (List.map (fun prop -> show_symbol srk (Proposition.symbol_of prop)) (conc :: hypo))
      in
      let offset_cands = local_partiton_and_cands srk constr !int_fvs_set flag in
      BatHashtbl.iter (fun arr_var (local_arr_cell, int_fvs, has_rw) ->
          let local_cands = BatHashtbl.create 97 in
          BatList.iter (fun chcvar ->
              BatHashtbl.modify_def
                BatSet.Int.empty
                chcvar.sym 
                (BatSet.Int.add chcvar.param)
                local_cands)
            (List.map (fun fv -> chcvar_of fv) (BatSet.Int.to_list int_fvs));
          let add_rule rules = 
            if has_rw then BatSet.Int.add rule_num rules else rules
          in
          match arr_var with
          | Sym sym ->
            let cell, cands, syms, rules = BatUref.uget (cell_of local_arr_cell) in
            BatUref.uset (cell_of local_arr_cell) 
              (cell, intersect cands local_cands, Symbol.Set.add sym syms, add_rule rules)
          | Fv arr_fv ->
            let sel (arrs1, cands1, syms1, rules1) (arrs2, cands2, syms2, rules2) =
              (CVSet.union arrs1 arrs2), 
              (intersect cands1 cands2),  
              Symbol.Set.union syms1 syms2,
              add_rule (BatSet.Int.union rules1 rules2)
            in
            BatUref.unite ~sel (cell_of arr_fv) (cell_of local_arr_cell);
            let arr_cell = CVSet.singleton (chcvar_of local_arr_cell) in
            sel 
              (BatUref.uget (cell_of arr_fv)) 
              (arr_cell, local_cands, Symbol.Set.empty, BatSet.Int.empty)
            |> BatUref.uset (cell_of arr_fv))
        offset_cands;)
    (Fp.get_rules fp);
  (* Obtain a single copy of each cell / offset proposals *)
  let rec ureflist_mem lst urf =
    match lst with
    | [] -> false
    | hd :: tl -> if BatUref.equal hd urf then true else ureflist_mem tl urf
  in
  let array_cells =
    let cell_refs =
      List.fold_left (fun acc cell -> 
          if ureflist_mem acc cell then acc else cell :: acc)
        []
        (BatList.of_enum (BatHashtbl.values global_partitioning)) 
    in
    List.map (fun cell_ref -> BatUref.uget cell_ref) cell_refs
    |> BatArray.of_list
  in
  let chcvar_to_cell = Hashtbl.create 97 in
  let sym_to_cell = Hashtbl.create 97 in
  (* We will create an LIA formula for each cell whose solution is a valid set 
   * of offset candidates that takes proposed candidates into account. *)
  let cell_to_offset = 
    BatArray.mapi (fun cell_num (arrs, offsetcands, syms, rules_with_rws) ->
        (* Create list of relations occuring in this cell *)
        let relations = CVSet.fold (fun chcvar relations ->
            Symbol.Set.add chcvar.sym relations)
            arrs
            Symbol.Set.empty
        in

        (* Create symbols for LIA formula. Each relation symbol will be
         * associated with an integer typed symbol. The values of these
         * integer typed symbols for the models of the formula we construct
         * will determine the offsets *)
        let symb_rel_params = Hashtbl.create 97 in
        let srp_inv = Hashtbl.create 97 in
        Symbol.Set.iter (fun ele ->
            let name = (show_symbol srk ele) in
            let sym = mk_symbol srk ~name `TyInt in
            Hashtbl.add srp_inv sym ele;
            Hashtbl.add symb_rel_params ele (mk_const srk sym))
          relations;
        let sym_to_edge_nums = BatHashtbl.create 97 in
        let edge_nums_to_syms = BatHashtbl.create 97 in
        
        Fp.iteri_rules (fun ind (conc, hypos, _) ->
            BatHashtbl.modify_def
              (BatSet.Int.empty, BatSet.Int.empty)
              (Proposition.symbol_of conc)
              (fun (i, o) -> (BatSet.Int.add ind i), o)
              sym_to_edge_nums;
            let hypos_sym = List.map Proposition.symbol_of hypos in
            List.iter (fun sym ->
                BatHashtbl.modify_def
                  (BatSet.Int.empty, BatSet.Int.empty)
                  sym
                  (fun (i, o) -> i, (BatSet.Int.add ind o))
                  sym_to_edge_nums)
              hypos_sym;
            BatHashtbl.add 
              edge_nums_to_syms 
              ind 
              (hypos_sym, [Proposition.symbol_of conc]))
          fp;
        let rec paint dir marked queue =
          let switch = if dir = true then fst else snd in 
          match queue with
          | [] -> marked
          | hd :: tl ->
            (* This is potentially making unsound assumptions about shape of non-lin chc *)
            let adjs =
              List.fold_left (fun adjs sym ->
                  BatSet.Int.union 
                    adjs 
                    (switch (BatHashtbl.find sym_to_edge_nums sym)))
                BatSet.Int.empty
                (switch (BatHashtbl.find edge_nums_to_syms hd))
            in
            let to_queue = BatSet.Int.to_list (BatSet.Int.diff adjs marked) in
            paint dir (BatSet.Int.union marked adjs) (to_queue @ tl)
        in
        let backwards_paint = paint true rules_with_rws (BatSet.Int.to_list rules_with_rws) in
        let forwards_paint = paint false rules_with_rws (BatSet.Int.to_list rules_with_rws) in
        let full_painted = BatSet.Int.inter backwards_paint forwards_paint in

        let subchc = 
          Fp.filteri_rules (fun ind (conc, hypos, _) ->
              let hypo_rels = Symbol.Set.of_list 
                  (List.map (fun prop -> Proposition.symbol_of prop) hypos)
              in
              (Symbol.Set.mem (Proposition.symbol_of conc) relations) &&
              (not (Symbol.Set.disjoint hypo_rels relations)) &&
              (BatSet.Int.mem ind full_painted))
            fp
        in

        let subchc_formula = 
          create_offset_formula srk subchc symb_rel_params offsetcands 
        in
        let offset_formula = mk_and srk subchc_formula in

        let solver = Smt.mk_solver srk in
        Smt.Solver.add solver [offset_formula];
        match Smt.Solver.get_model solver with
        | `Unsat 
        | `Unknown -> failwith "Cannot determine offsets"
        | `Sat m ->
          match Interpretation.select_implicant m offset_formula with
          | None -> assert false
          | Some imp ->
            let offsets = BatHashtbl.create 97 in
            List.iter (fun phi -> 
                begin match Formula.destruct srk phi with
                  | `Atom (`Arith (`Eq, rel, param)) ->
                    begin match ArithTerm.destruct srk rel, 
                                ArithTerm.destruct srk param with
                    | `App (rel, []), `Real param ->
                      Hashtbl.replace 
                        offsets
                        (Hashtbl.find srp_inv rel)
                        (Option.get (QQ.to_int param))
                    | _ -> assert false
                    end
                  | _ -> assert false
                end) 
              imp; 
            CVSet.iter (fun arr -> Hashtbl.add chcvar_to_cell arr cell_num)
              arrs;
            Symbol.Set.iter (fun sym -> Hashtbl.add sym_to_cell sym cell_num)
              syms;
            offsets)
      array_cells
  in
  cell_to_offset, chcvar_to_cell, sym_to_cell





let rec check_q_array srk phi =
  match Formula.destruct srk phi with
  | `Quantify (_, _, typ, phi) ->
    if typ = `TyArr then assert false
    else check_q_array srk phi
  | open_phi -> Formula.construct srk open_phi

let check_q_array_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, check_q_array srk constr) 
    fp

let elim_ite_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, eliminate_ite srk constr) 
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


let apply_offset_candidate srk constr offsets =
  let rec apply_offset_formula = function
    | `Atom (`Arith (op, s, t)) ->
      let op = match op with | `Eq -> mk_eq | `Lt -> mk_lt | `Leq -> mk_leq in
      let s = ArithTerm.eval srk apply_offset_arith s in
      let t = ArithTerm.eval srk apply_offset_arith t in
      op srk s t
    | `Atom(`ArrEq (a, b)) ->
      let a, _ = ArrTerm.eval srk apply_offset_arr a in
      let b, _ = ArrTerm.eval srk apply_offset_arr b in
      mk_arr_eq srk a b
    | `Proposition (`App (sym, [])) -> mk_const srk sym
    | `Proposition (`Var ind) -> mk_var srk ind `TyBool
    | `Proposition _ -> assert false
    | `Ite _ -> assert false
    | `Quantify _ -> assert false
    | open_formula -> Formula.construct srk open_formula 
  and apply_offset_arith = function
    | `Select (a, term) ->
      let a, offset = ArrTerm.eval srk apply_offset_arr a in
      let offset = Option.get offset in
      (* look into getting rid of div by char size *)
      mk_select 
        srk 
        a 
        (*(mk_floor srk (mk_div srk (mk_sub srk term (mk_var srk offset `TyInt)) (mk_int srk 4)))*)
        (mk_sub srk term (mk_var srk offset `TyInt))
    | `Ite _ -> assert false
    | open_term -> ArithTerm.construct srk open_term
  and apply_offset_arr = function
    | `App (sym, []) -> 
      mk_const srk sym, (Hashtbl.find offsets (Sym sym))
    | `Var (ind, typ) ->
      mk_var srk ind (typ :> typ_fo), (Hashtbl.find offsets (Fv ind))
    | `Store ((a, offset), i, v) ->
      let unwrapped_offset = Option.get offset in
      let i = ArithTerm.eval srk apply_offset_arith i in
      (* Look into getting rid of div by char size *)
      let i_offset = 
        (*mk_floor srk (mk_div srk (mk_sub srk i (mk_var srk unwrapped_offset `TyInt)) (mk_int srk 4))*)
        (mk_sub srk i (mk_var srk unwrapped_offset `TyInt))
      in
      let v = ArithTerm.eval srk apply_offset_arith v in
      mk_store srk a i_offset v, offset
    | _ -> assert false
  in
  
  Formula.eval srk apply_offset_formula constr


let apply_offset_candidates_new srk fp cell_to_offsets chcvar_to_cell sym_to_cell =
  Fp.map_rules (fun (conc, hypo, constr) ->
      let fvs_of = BatHashtbl.create 97 in
      iter_fvs (fun fv rel param -> 
          BatHashtbl.modify_def 
            BatSet.Int.empty
            {sym=Proposition.symbol_of rel; param}
            (BatSet.Int.add fv)
            fvs_of) 
        (conc :: hypo);
      let rec sel_offset offsets rels = 
        match rels with
        | [] -> None
        | hd :: tl ->
          if Hashtbl.mem offsets hd then (
            Some (BatSet.Int.choose (Hashtbl.find fvs_of {sym=hd;param=Hashtbl.find offsets hd})))
          else sel_offset offsets tl
      in
      let fvs_of = Hashtbl.find fvs_of in

      let cell_to_offset = 
        BatArray.map (fun offsets ->
            let rels = List.map Proposition.symbol_of (conc :: hypo) in
            sel_offset offsets rels)
          cell_to_offsets
      in
      let offsets = Hashtbl.create 97 in
      Hashtbl.iter (fun chcvar cell ->
          try
            BatSet.Int.iter (fun fv ->
                Hashtbl.add offsets (Fv fv) cell_to_offset.(cell))
              (fvs_of chcvar)
          with _ -> ())
        chcvar_to_cell;
      Hashtbl.iter (fun sym cell ->
          try
            Hashtbl.add offsets (Sym sym) cell_to_offset.(cell)
          with _ -> ())
        sym_to_cell;
      conc, hypo, apply_offset_candidate srk constr offsets)
    fp

let skolemize_eh srk _ phi =
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
  let quant_free = function
    | `Quantify _ -> failwith "skolemize eh has unexpected quantifiers"
    | _ -> ()
  in
  Formula.eval srk quant_free phi';
  phi', syms


let skolemize_eh_chc srk fp =
  let skolemized_vars = BatHashtbl.create 97 in
  Fp.mapi_rules (fun ind (conc, hypo, constr) ->
      let fvs = ref 0 in
      iter_fvs (fun _ _ _ -> fvs := !fvs + 1) (conc :: hypo);
      let phi', syms = skolemize_eh srk !fvs constr in
      BatHashtbl.add skolemized_vars ind syms;
      conc, hypo, phi')
    fp



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


let pos_bool_elim srk phi syms =
  let bool_fvs = ref Symbol.Set.empty in
  let syms_to_fvs = Hashtbl.create 97 in
  let fvs_to_syms = Memo.memo (fun (ind, typ) -> 
      let sym = mk_symbol srk ~name:"POS_BOOL" (typ :> typ) in
      if typ = `TyBool
      then bool_fvs := Symbol.Set.add sym !bool_fvs
      else ();
      Hashtbl.add syms_to_fvs sym (ind, typ);
      mk_const srk sym) 
  in
  let phi = substitute srk fvs_to_syms phi in 

  let phi = Symbol.Set.fold (fun sym phi ->
      match Smt.entails srk phi (mk_const srk sym) with
        | `Yes -> 
          let substed = 
            substitute_const
              srk
              (fun s -> if sym = s then mk_true srk else mk_const srk s)
              phi
          in
          if Symbol.Set.mem sym !bool_fvs then
            mk_and srk [substed; mk_const srk sym]
          else substed
        | `No -> 
          begin match Smt.entails srk phi (mk_not srk (mk_const srk sym)) with
          | `Yes -> 
            let substed = 
              substitute_const
                srk
                (fun s -> if sym = s then mk_false srk else mk_const srk s)
                phi
            in
            if Symbol.Set.mem sym !bool_fvs then
              mk_and srk [substed; mk_not srk (mk_const srk sym)]
            else substed
          | `No -> 
            phi
          | `Unknown -> 
            failwith "pos_bool_elim failure" 
          end
        | `Unknown -> 
          failwith "pos_bool_elim failure" )
      (Symbol.Set.union
         (Symbol.Set.filter (fun sym -> typ_symbol srk sym = `TyBool) syms)
         !bool_fvs)
    phi
  in

  let phi = 
    substitute_const
      srk
      (fun s -> 
         if Hashtbl.mem syms_to_fvs s
         then
           let ind, typ = Hashtbl.find syms_to_fvs s in
           mk_var srk ind typ
         else mk_const srk s)
      phi
  in
  phi


let offset_analysis srk fp =
  let skolemized_vars = BatHashtbl.create 97 in
  let fp' = 
    Fp.mapi_rules (fun ind (conc, hypo, constr) ->

        let phi', syms = skolemize_eh srk 0 constr in

        BatHashtbl.add skolemized_vars ind syms;
        conc, hypo, phi')
      fp
  in

  let cell_to_offsets, chcvar_to_cell, sym_to_cell = 
    determine_offsets srk fp'
  in
  let fp'' = 
    apply_offset_candidates_new srk fp' cell_to_offsets chcvar_to_cell sym_to_cell 
  in

  let fp'' = 
    Fp.mapi_rules (fun ind (conc, hypo, constr) ->
        conc, hypo, pos_bool_elim srk constr (Hashtbl.find skolemized_vars ind))
      fp''
  in

  (* Unskolemize *)
  let fp'3 = 
    Fp.mapi_rules (fun ind (conc, hypo, constr) -> 
        let constr' =
          mk_exists_consts
            srk
            (fun sym -> not (Symbol.Set.mem sym (BatHashtbl.find skolemized_vars ind)))
            constr
        in

        conc, hypo, constr')
      fp''
  in


  let fp'3 = 
    Fp.map_rules (fun (conc, hypo, constr) ->
        let constr'' = Quantifier.miniscope srk constr in

        let constr' =
          Quantifier.eq_guided_qe 
            srk
            constr''
        in

        let constr' = Quantifier.eq_guided_elim_loop srk constr' in

 
        conc, hypo, constr')
      fp'3
  in

  let fp'3 =check_q_array_chc srk fp'3 in


  (* try some of the exist quant generalization functions *)

  fp'3



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
    (* Maps the term a[i] to an integer symbol where i is not the universally
     * quantified var *)
    let non_uq_read : 'c * 'd -> 'a arith_term =
      Memo.memo (fun (arr, read) -> 
          Hashtbl.add func_consist_reqs arr read;
          let sym = mk_symbol srk ~name:"NON_EQ_RE" `TyInt in
          nuqr_syms := Symbol.Set.add sym !nuqr_syms;
          mk_const srk sym)
    in
    (* TODO: Make sure that array reads normalized for efficiency; don't want
     * seperate symbol for a[x + y] vs a[y + x]*)
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
        skolems : Symbol.Set.t }

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


(*
    let squash_eq_adds srk phi =
      let squash_add term =
        begin match ArithTerm.destruct srk term with
        | `Add [a; b] ->
          begin match ArithTerm.destruct srk a, ArithTerm.destruct srk b with
            | `Unop (`Neg, a_d), _ -> if a_d = b then mk_zero srk else term
            | _, `Unop (`Neg, b_d) -> if a = b_d then mk_zero srk else term
            | _, _ -> term
          end
        | _ -> term
        end
      in
      let alg = function
        | `Atom (`Arith (`Eq, a, b)) -> mk_eq srk (squash_add a) (squash_add b)
        | open_phi -> Formula.construct srk open_phi
      in
      Formula.eval srk alg phi
*)


    let abstract srk tf =
      let t1 = time "In abstract" in


      let eqs = arr_eqs srk tf in

      let trs = ref (T.symbols tf) in

      let eqs_trs =
        List.fold_left (fun eqs_trs (a, b) ->
            if List.mem (a, b) (T.symbols tf) then (
              Symbol.Map.add a b eqs_trs)
            else if List.mem (b, a) (T.symbols tf) then (
              Symbol.Map.add b a eqs_trs)
            else eqs_trs)
          Symbol.Map.empty
          eqs
    in

    let eqs_ints_trs =
      List.fold_left (fun eqs_trs (a, b) ->
          if List.mem (a, b) (T.symbols tf) then (
            trs := BatList.remove !trs (a, b);
            Symbol.Map.add a b eqs_trs)
          else if List.mem (b, a) (T.symbols tf) then (
            trs := BatList.remove !trs (b, a);
            Symbol.Map.add b a eqs_trs)
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





    let phi = eliminate_stores srk phi in
    let phi = eliminate_ite srk phi in
    let phi = unbooleanize srk phi in


    let tf_pmfa = T.update_formula tf phi in
    let tf_pmfa = T.update_symbols tf_pmfa !trs in
    let proj_ind, arr_map, tf_proj, arr_only_trs = projection srk tf_pmfa eqs_trs new_eqs_consts in
    (*let tf_proj' =
      substitute_sym 
        srk
          (fun s ->
             if Hashtbl.mem eqs_map s then (
               mk_const srk (Hashtbl.find eqs_map s))
             else if Hashtbl.mem arr_map s && 
                     Hashtbl.mem eqs_map (Hashtbl.find arr_map s)
             then (
               mk_const srk
                 (Hashtbl.find rev_map (Hashtbl.find eqs_map (Hashtbl.find arr_map s))))
             else mk_const srk s)
          (T.formula tf_proj)
        in*)



    let lia, _ = pmfa_to_lia srk (T.formula tf_proj) in


    let lia = 
      Quantifier.eq_guided_qe 
        srk
        (Quantifier.miniscope srk lia)
    in

    let lia, skolems = skolemize_eh_alt srk lia in 
    let lia = Quantifier.miniscope srk lia in
 
    let ground_lia = Quantifier.mbp_qe_inplace srk lia in






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
       skolems
      }
     
   (* let at_most_single_write srk write noop trs =
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
*)
 
    let at_most_single_write _ _ _ _ =
      true
    


    type 'a dir_var = Inc of 'a arith_term * 'a arith_term | Dec of 'a arith_term * 'a arith_term

    (* Determines which trs in phi are monotonically increasing/decreasing *)
    let _directional_vars srk phi trs =
      List.flatten (
        List.filter_map (fun (x, x') ->
            let xt, xt' = mk_const srk x, mk_const srk x' in
            match Smt.entails srk phi (mk_leq srk xt xt'), 
                  Smt.entails srk phi (mk_leq srk xt' xt) with
            | `Yes, `Yes -> Some [Inc (xt, xt'); Dec (xt, xt')]
            | `Yes, _ -> Some [Inc (xt, xt')]
            | _, `Yes -> Some [Dec (xt, xt')]
            | _ -> None)
          trs)

    let _create_phased_exps srk phi trs symb_index directs lc skolems =
      let exp1term = mk_symbol srk ~name:"exp1" `TyInt in
      let exp2term = mk_symbol srk ~name:"exp2" `TyInt in
      List.map (fun direction ->
          match direction with
          | Inc (x, x') ->
            let j = mk_const srk symb_index in

            let phase1 = mk_and srk [phi; mk_leq srk x j; mk_leq srk x' j] in
            let polka = Polka.manager_alloc_loose () in
            let phase1 =
              rewrite srk ~down:(nnf_rewriter srk) phase1
            in

            let conv = 
              SrkApron.formula_of_property 
                (Abstract.abstract 
                   srk 
                   ~exists:(fun s -> Symbol.Set.mem s (symbols phase1) && not (Symbol.Set.mem s skolems))
                   polka 
                   phase1) 
            in
            let phase1_single = conv in
            let exists s = not (Symbol.Set.mem s skolems) in
            let phase1_single_tr = T.make ~exists phase1_single trs in
 


            let phase2 = mk_and srk [phi;  mk_lt srk j x; mk_lt srk j x'] in
            let polka = Polka.manager_alloc_loose () in
            let phase2 =
              rewrite srk ~down:(nnf_rewriter srk) phase2
            in

            let conv = 
              SrkApron.formula_of_property 
                (Abstract.abstract 
                   srk 
                   ~exists:(fun s -> Symbol.Set.mem s (symbols phase2) && not (Symbol.Set.mem s skolems))
                   polka 
                   phase2) 
            in
            let phase2_single = conv in
            let phase2_single_tr = T.make ~exists phase2_single trs in



            let phase1 = 
              T.make 
                (mk_and srk 
                   [Iter.exp
                      srk 
                      trs 
                      (mk_const 
                         srk 
                         exp1term) 
                      (Iter.abstract 
                         srk
                         phase1_single_tr);
                    mk_leq srk x j; mk_leq srk x' j])
                trs
            in
            let phase2 =
              T.make
                (mk_and srk 
                   [Iter.exp
                      srk 
                      trs 
                      (mk_const 
                         srk 
                         exp2term)
                      (Iter.abstract 
                         srk
                         phase2_single_tr);
                    mk_lt srk j x; mk_lt srk j x'])
                trs
            in

            let inter = mk_and srk [phi;  mk_leq srk x j; mk_lt srk j x'] in


            let polka = Polka.manager_alloc_loose () in
            let inter =
              rewrite srk ~down:(nnf_rewriter srk) inter
            in

            let conv = 
              SrkApron.formula_of_property 
                (Abstract.abstract 
                   srk 
                   ~exists:(fun s -> Symbol.Set.mem s (symbols inter) && not (Symbol.Set.mem s skolems))
                   polka 
                   inter) 
            in
            let inter = conv in
            
            let intermediate_tr = 
              T.make
                ~exists
                inter
                trs
            in

            let phased_tf = T.mul srk phase1 (T.mul srk intermediate_tr phase2) in
            let phased_tr =
              substitute_const
                srk
                (fun s -> if s = exp2term then
                    mk_sub 
                      srk
                      lc
                      (mk_add
                        srk
                        [mk_const srk exp1term; mk_one srk])
                  else mk_const srk s)
                (T.formula phased_tf)
            in
            let phased_tr = mk_exists_consts srk (T.exists phased_tf) phased_tr in

            (* Adds constraints on loop counter depending on which phase(s) taken*)
            let both_phases = 
              mk_and 
                srk
                [phased_tr;
                 mk_leq srk (mk_zero srk) (mk_const srk exp1term); 
                 mk_leq srk (mk_zero srk) 
                   (mk_sub 
                      srk
                      lc
                      (mk_add
                         srk
                         [mk_const srk exp1term; mk_one srk]))]
            in
            let both_phases = mk_exists_const srk exp1term both_phases in
            
            let both_phases = 
              Quantifier.eq_guided_qe 
                srk
                (Quantifier.miniscope srk both_phases)
            in

            (* TODO: make sure quants introduced *)
            let both_phases = Quantifier.mbp_qe_inplace srk both_phases in



let polka = Polka.manager_alloc_loose () in
            let both_phases =
              rewrite srk ~down:(nnf_rewriter srk) both_phases
            in

            let conv = 
              SrkApron.formula_of_property 
                (Abstract.abstract 
                   srk 
                   ~exists:(fun s -> Symbol.Set.mem s (symbols both_phases))
                   polka 
                   both_phases) 
            in
            let both_phases = conv in



            let phase1_only =
              substitute_const
                srk
                (fun s -> if s = exp1term then lc else mk_const srk s)
                (T.formula phase1)
            in
            let phase1_only = mk_exists_consts srk (T.exists phase1) phase1_only in
            
            let phase1_only = 
              Quantifier.eq_guided_qe 
                srk
                (Quantifier.miniscope srk phase1_only)
            in


            (* TODO: make sure quants introduced *)
            let phase1_only = Quantifier.mbp_qe_inplace srk phase1_only in



            let phase2_only =
              substitute_const
                srk
                (fun s -> if s = exp2term then lc else mk_const srk s)
                (T.formula phase2)
            in
            let phase2_only = mk_exists_consts srk (T.exists phase2) phase2_only in

            let phase2_only = 
              Quantifier.eq_guided_qe 
                srk
                (Quantifier.miniscope srk phase2_only)
            in


            (* TODO: make sure quants introduced *)
            let phase2_only = Quantifier.mbp_qe_inplace srk phase2_only in

            mk_or srk [both_phases; phase1_only; phase2_only]

          | Dec _ -> (mk_true srk) (* turned off for now to make testing smoother *)
        )
        directs, exp1term, exp2term



    let exp srk _ lc obj =
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
      let write = conv in

      let noop = mk_and srk [obj.ground_lia; arr_vars_eq] in 


      let noop =
        rewrite srk ~down:(nnf_rewriter srk) noop
      in
      

      let exists s = not (Symbol.Set.mem s obj.skolems) in
      let write = T.make ~exists write obj.iter_trs in
      let noop = T.make ~exists noop obj.iter_trs in
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

          let write_once = 
            T.mul srk noop_star1 (T.mul srk write noop_star2)
          in
          let lc_constr = 
            mk_and srk 
              [mk_eq
                 srk
                 lc
                 (mk_add srk [mk_const srk exp1;
                              mk_const srk exp2;
                              mk_int srk 1]);
                 mk_leq srk (mk_zero srk) (mk_const srk exp1);
               mk_leq srk (mk_zero srk) (mk_const srk exp2)]
          in
          mk_and 
            srk 
            [mk_exists_consts 
               srk
               (fun s -> (T.exists write_once s) && not (s = exp1) && not (s = exp2))
               (T.formula write_once); 
             lc_constr]
        )
        else assert false
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


      (* TODO: make sure quants introduced *)
      let nstarwnstar = Quantifier.mbp_qe_inplace srk nstarwnstar in



     let nstarmbp = time "nstar" in

     diff nstar nstarmbp "nstarmbp";



      let nstar =
        Iter2.exp
           srk 
           obj.iter_trs 
           lc
           (Iter2.abstract
              srk 
              noop)
      in



      let nstar2 =
        Iter.exp
          srk 
          obj.iter_trs 
          lc
          (Iter.abstract
             srk 
             noop)
      in

      let nstar = mk_and srk [nstar; nstar2] in



      let nstar = Quantifier.mbp_qe_inplace srk nstar in
      
      let nstarreal = time "nstarreal" in

      diff nstarmbp nstarreal "nstar real";




      let old_method = 
        mk_or 
          srk 
          [mk_and srk ((mk_eq srk lc (mk_int srk 0)) :: noop_eqs);
            nstar;
           nstarwnstar] 
      in



     (* let arr_vars_eq = 
        mk_and
          srk
          (List.map (fun (z, z') -> mk_eq srk (mk_const srk z) (mk_const srk z')) obj.arr_only_trs)
      in*)

(*

     let noop_eqs = 
        List.map 
          (fun (x, x') -> mk_eq srk (mk_const srk x) (mk_const srk x'))
          obj.iter_trs
      in
*)
      (*let exists s = not (Symbol.Set.mem s obj.skolems) in
 
      let noop = mk_and srk [obj.ground_lia; arr_vars_eq] in 
      let noop = T.make ~exists noop obj.iter_trs in
 
      let nstar =
        Iter2.exp
           srk 
           obj.iter_trs 
           lc
           (Iter2.abstract
              srk 
              noop)
      in


      let nstar = Quantifier.mbp_qe_inplace srk nstar in
*)

      (*let directs = directional_vars srk obj.ground_lia obj.iter_trs in
      let directs_res, _, _ = create_phased_exps srk obj.ground_lia obj.iter_trs obj.proj_ind directs lc obj.skolems in
      (* Redo this part to act on tfs rather than first converting to formula *)
      let direct_res = mk_and srk directs_res in

      let _direct_res = Quantifier.mbp_qe_inplace srk direct_res in 
*)

      let exp_res_pre = 
        mk_or 
          srk 
          [(*mk_and srk ((mk_eq srk lc (mk_int srk 0)) :: noop_eqs);*) old_method] 
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

      (*let all_but_map = time "abp" in

      diff nstarreal all_but_map "all but map";*)



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
end
