open Syntax
open Chc
module T = TransitionFormula



let time _ =
  let t = Unix.gettimeofday () in
  (*Log.errorf "\n%s Curr time: %fs\n" s (t);*) t

let diff _t1 _t2 _s = 
  (*Log.errorf "\n%s Execution time: %fs\n" s (t2 -. t1)*) ()

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
let determine_eq_int_fvs srk constr fvcands : BatSet.Int.t list =
  let fv_classes = Memo.memo (fun a -> BatUref.uref (BatSet.Int.singleton a)) in
  let conjs = match Formula.destruct srk constr with
   | `And conds -> conds
   | _ -> assert false
  in
  List.iter (fun cond ->
      match Formula.destruct srk cond with
      | `Atom (`Arith (`Eq, i, j)) ->
        begin match ArithTerm.destruct srk i, ArithTerm.destruct srk j with
          | `Var (i, _), `Var (j, _) ->
            if BatSet.Int.mem i fvcands && BatSet.Int.mem j fvcands then
              BatUref.unite ~sel:BatSet.Int.union (fv_classes i) (fv_classes j)
            else ()
          | _ -> ()
        end
      | _ -> ())
    conjs;
  let fv_uclasses =
    BatSet.Int.fold (fun fv urefs ->
        if List.mem (fv_classes fv) urefs then urefs
        else (fv_classes fv) :: urefs)
      fvcands
      []
  in
  let fv_classes = List.map (fun uref -> BatUref.uget uref) fv_uclasses in
  fv_classes
 

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
    | `Atom (`IsInt _)
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
        (*let unwrapped_class = match arr_class with Fv fv -> fv | Sym sym ->
          Log.errorf "Sym is %a" (pp_symbol srk) sym;
          assert false in
        Log.errorf "unwrapped class is %n\n\n" unwrapped_class;
        Log.errorf "Size is %n" (List.length rwvs);*)
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
        BatHashtbl.add arr_fv_class_and_cands var (arr_class, cands, has))
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

  let local_offsets = Hashtbl.create 97 in
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
          match local_arr_cell, arr_var with
            | Sym sym_cell, Sym arr_sym ->
              BatHashtbl.modify_opt
                (rule_num, sym_cell)
                (fun v ->
                   match v with
                   | Some (cands, syms) ->
                   Some (intersect cands local_cands, Symbol.Set.add arr_sym syms)
                   | None -> Some (local_cands, Symbol.Set.singleton arr_sym))
                local_offsets
            | Sym _, Fv _ -> assert false
            | Fv local_arr_cell_fv, Sym sym ->
              let cell, cands, syms, rules = BatUref.uget (cell_of local_arr_cell_fv) in
              BatUref.uset (cell_of local_arr_cell_fv) 
                (cell, intersect cands local_cands, Symbol.Set.add sym syms, add_rule rules)
            | Fv local_arr_cell_fv, Fv arr_fv ->
              let sel (arrs1, cands1, syms1, rules1) (arrs2, cands2, syms2, rules2) =
                (CVSet.union arrs1 arrs2), 
                (intersect cands1 cands2),  
                Symbol.Set.union syms1 syms2,
                add_rule (BatSet.Int.union rules1 rules2)
              in
              BatUref.unite ~sel (cell_of arr_fv) (cell_of local_arr_cell_fv);
              let arr_cell = CVSet.singleton (chcvar_of local_arr_cell_fv) in
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
        | `Unknown -> 
          failwith "Cannot determine offsets"
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
  BatHashtbl.iter (fun (rule_num, _) (offsetcands, _syms) ->
      Log.errorf "IN INTERESTING PHASE";
      let _subchc = 
        Fp.filteri_rules (fun ind _ -> ind = rule_num) fp
      in
      BatHashtbl.iter (fun sym fvs ->
          Log.errorf "offset cands for sym %a include\n" (pp_symbol srk) sym;
          BatSet.Int.iter (fun fv -> Log.errorf "includes %n\n" fv) fvs;
          Log.errorf "\n\n")
        offsetcands;
      assert ( 1 = 2);
      ()
      (*let subchc_formula = 
        create_offset_formula srk subchc symb_rel_params offsetcands 
      in

      List.iter (fun f -> Log.errorf "One formula is %a" (Formula.pp srk) f) subchc_formula;
      let offset_formula = mk_and srk subchc_formula in

      let solver = Smt.mk_solver srk in
      Smt.Solver.add solver [offset_formula];
      match Smt.Solver.get_model solver with
      | `Unsat 
      | `Unknown -> 
        Log.errorf "Offset formula is %a\n" (Formula.pp srk) offset_formula;
        failwith "Cannot determine offsets"
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
          offsets)*)
    )
    local_offsets;
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
  let step1 = time () in
  let fp' = 
    Fp.mapi_rules (fun ind (conc, hypo, constr) ->

        let phi', syms = skolemize_eh srk 0 constr in

        BatHashtbl.add skolemized_vars ind syms;
        conc, hypo, phi')
      fp
  in
  let step2b = time () in
 
  let cell_to_offsets, chcvar_to_cell, sym_to_cell = 
    determine_offsets srk fp'
  in
  let step2 = time () in
  let fp'' = 
    apply_offset_candidates_new srk fp' cell_to_offsets chcvar_to_cell sym_to_cell 
  in


  let step3 = time () in
  let fp'' = 
    Fp.mapi_rules (fun ind (conc, hypo, constr) ->
        conc, hypo, pos_bool_elim srk constr (Hashtbl.find skolemized_vars ind))
      fp''
  in
  
  let step4 = time () in
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

  let step5 = time () in
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

  let step6 = time () in

  diff step1 step2 "1 to 2";
  diff step1 step2b "1 to 2b";
  diff step2 step3 "2 to 3"; 
  diff step3 step4 "3 to 4";
  diff step4 step5 "4 to 5";
  diff step5 step6 "5 to 6";
 
  let fp'3 =check_q_array_chc srk fp'3 in
  fp'3
