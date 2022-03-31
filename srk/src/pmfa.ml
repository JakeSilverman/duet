open Syntax
open Chc
module T = TransitionFormula


let typ_symbol_fo srk sym =
    match typ_symbol srk sym with
    | `TyInt -> `TyInt
    | `TyReal -> `TyReal
    | `TyBool -> `TyBool
    | `TyArr -> `TyArr
    | _ -> assert false

type chcvar = { rel : symbol; param : int} 

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

module CHCVarSet = BatSet.Make(CHCVar)

let skolemize_offset srk phi =
  let rec subst_existentials expr =
    match Formula.destruct srk expr with
    | `Quantify (`Exists, name, typ, phi) ->
      let sym = mk_symbol srk ~name (typ :> typ) in
      let phi' =
        substitute
          srk
          (fun (ind, typ) -> if ind = 0 then mk_const srk sym else mk_var srk (ind - 1) typ)
          phi
      in
      subst_existentials phi'
    | `And conjs -> mk_and srk (List.map subst_existentials conjs)
    | open_form -> Formula.construct srk open_form
  in
  subst_existentials phi

(*
let overapprox_arrs srk phi =
  let mk_op op =
    match op with
    | `Leq -> mk_leq srk
    | `Lt -> mk_lt srk
    | `Eq -> mk_eq srk 
  in
  let rec not_contains_arr a =
    match ArithTerm.destruct srk a with
    | `Real _
    | `App _
    | `Var _ -> true
    | `Add terms
    | `Mul terms -> BatList.for_all (fun term -> not_contains_arr term) terms
    | `Binop (_, a, b) -> (not_contains_arr a) && (not_contains_arr b)
    | `Unop (_, a) -> not_contains_arr a
    | `Select _ -> false
    | `Ite _ -> assert false
  in
  let overapprox_formula = function 
    | `Atom (`Arith (op, a, b)) ->
      if not_contains_arr a && not_contains_arr b then mk_op op a b else mk_true srk
    | `Atom (`ArrEq (_, _)) -> mk_true srk
    | `Quantify (_, _, `TyArr, phi) -> 
      substitute srk (fun (ind, typ) -> mk_var srk (ind - 1) typ) phi
    | open_formula -> Formula.construct srk open_formula 
  in
  Formula.eval srk overapprox_formula phi
*)


(*(* Determines which fvs are equal to each other *)
let determine_eq_int_fvs srk constr =
  Log.errorf "constr is %a" (Formula.pp srk) constr;
  let syms_to_fvs = Hashtbl.create 97 in
  let fvs_to_syms = Memo.memo (fun (ind, typ) -> 
      let sym = mk_symbol srk (typ :> typ) in
      if typ = `TyInt then Hashtbl.add syms_to_fvs sym ind else ();
      sym) in
  let constr' = substitute srk (fun fv -> mk_const srk (fvs_to_syms fv)) constr in 
  let cells = 
    BatHashtbl.fold (fun sym _ cells ->
        let rec place_in_cell unchecked_cells =
          match unchecked_cells with
          | [] -> [Symbol.Set.singleton sym]
          | hd :: tl ->
            let rep = Symbol.Set.any hd in
            begin match Smt.entails srk constr' (mk_eq srk (mk_const srk sym) (mk_const srk rep)) with
                      | `Yes -> (Symbol.Set.add sym hd) :: tl
                      | `No -> hd :: (place_in_cell tl) 
                      | `Unknown -> failwith "Unable to determine equiv between ints. Look into this" 
            end
        in
        place_in_cell cells)
      syms_to_fvs
      []
  in
  let cells = 
    List.map (fun cell -> 
        List.fold_left (fun fvs sym -> 
            BatSet.Int.add (Hashtbl.find syms_to_fvs sym) fvs)
      BatSet.Int.empty
      (Symbol.Set.elements cell))
      cells
  in
  BatList.iter (fun set ->
      Log.errorf "PRINTING EQUIV SET";
      BatSet.Int.iter (fun ele ->
          Log.errorf "ELEMENT IS %n" ele)
        set)
    cells;
  cells
*)
(*let find_int_chc_consts srk fp rels =
  List.fold_left (fun valid_offset_sets (conc, hypos, constr) ->
      let constr_cells_fvs = determine_eq_int_fvs srk constr in
      let fvcounter = ref 0 in
      let chcvar_tbl = Hashtbl.create 50 in
      (* fv to chcvar *)
      List.iter (fun prop ->
          List.iteri (fun param typ ->
              Hashtbl.add chcvar_tbl !fvcounter {rel=Proposition.symbol_of prop; param};
              fvcounter := !fvcounter + 1)
            (Proposition.typ_of_params srk prop))
        (conc :: hypo);
      let chcvar_of fv = Hashtbl.find chcvar_tbl fv in
      let dups = ref CHCVarSet.emppty in
      let seen = ref CHCVarSet.empty in
      (* These are the cells for constraint classes *)
      let constr_cells = 
        BatList.map (fun fvs ->
            let chcvarcell = 
              CHCVarSet.of_list (
                List.map 
                  (fun fv -> chcvar_of fv)
                  (BatSet.Int.to_list fvs))
            in
            dups := CHCVarSet.union !dups (CHCVarSet.inter (!seen chcvarcell));
            seen := CHCVarSet.union !seen chcvarcell;
            chcvarcell)
          (determine_eq_int_fvs srk constr)
      in
      let constr_cells =
        List.map (fun cell -> CHCVarSet.diff cell !dups) constr_cells
      in
      let acc' = 
        BatList.filter_map (fun offset_set ->
          )
          valid_offset_sets
      in
      constr_cells)
*)

(* Determines which fvs are equal to each other *)
let determine_eq_int_fvs srk constr =
  Log.errorf "constr is %a" (Formula.pp srk) constr;
  let syms_to_fvs = Hashtbl.create 97 in
  let fvs_to_syms = Memo.memo (fun (ind, typ) -> 
      let sym = mk_symbol srk (typ :> typ) in
      if typ = `TyInt then Hashtbl.add syms_to_fvs sym ind else ();
      sym) in
  let constr' = substitute srk (fun fv -> mk_const srk (fvs_to_syms fv)) constr in 
  let cells = 
    BatHashtbl.fold (fun sym _ cells ->
        let rec place_in_cell unchecked_cells =
          match unchecked_cells with
          | [] -> [Symbol.Set.singleton sym]
          | hd :: tl ->
            let rep = Symbol.Set.any hd in
            begin match Smt.entails srk constr' (mk_eq srk (mk_const srk sym) (mk_const srk rep)) with
                      | `Yes -> (Symbol.Set.add sym hd) :: tl
                      | `No -> hd :: (place_in_cell tl) 
                      | `Unknown -> failwith "Unable to determine equiv between ints. Look into this" 
            end
        in
        place_in_cell cells)
      syms_to_fvs
      []
  in
  let cells = 
    List.map (fun cell -> 
        List.fold_left (fun fvs sym -> 
            BatSet.Int.add (Hashtbl.find syms_to_fvs sym) fvs)
      BatSet.Int.empty
      (Symbol.Set.elements cell))
      cells
  in
  BatList.iter (fun set ->
      Log.errorf "PRINTING EQUIV SET";
      BatSet.Int.iter (fun ele ->
          Log.errorf "ELEMENT IS %n" ele)
        set)
    cells;
  cells

(*
(* Determines which fvs are equal to each other *)
let determine_constr_formulas srk constr rel_to_phisym =
  Log.errorf "constr is %a" (Formula.pp srk) constr;
  let syms_to_fvs = Hashtbl.create 97 in
  let fvs_to_syms = Memo.memo (fun (ind, typ) -> 
      let sym = mk_symbol srk (typ :> typ) in
      Hashtbl.add syms_to_fvs sym ind;
      sym) in
  let constr' = substitute srk (fun fv -> mk_const srk (fvs_to_syms fv)) constr in 
  let cells = 
    BatHashtbl.fold (fun sym _ cells ->
        let rec place_in_cell unchecked_cells =
          match unchecked_cells with
          | [] -> [Symbol.Set.singleton sym]
          | hd :: tl ->
            let rep = Symbol.Set.any hd in
            begin match Smt.entails srk constr' (mk_eq srk (mk_const srk sym) (mk_const srk rep)) with
                      | `Yes -> (Symbol.Set.add sym hd) :: tl
                      | `No -> hd :: (place_in_cell tl) 
                      | `Unknown -> failwith "Unable to determine equiv between ints. Look into this" 
            end
        in
        place_in_cell cells)
      syms_to_fvs
      []
  in
  let cells = 
    List.map (fun cell -> 
        List.fold_left (fun fvs sym -> 
            BatSet.Int.add (Hashtbl.find syms_to_fvs sym) fvs)
      BatSet.Int.empty
      (Symbol.Set.elements cell))
      cells
  in
  BatList.iter (fun set ->
      Log.errorf "PRINTING EQUIV SET";
      BatSet.Int.iter (fun ele ->
          Log.errorf "ELEMENT IS %n" ele)
        set)
    cells;
  cells
*)


let determine_eq_ints_chc srk fp rels =
  let named_rel = Memo.memo (fun _ -> mk_const srk (mk_symbol srk ~name:"named" `TyInt)) in
  let term_of (rel, arg) = mk_eq srk (named_rel rel) (mk_int srk arg) in

  let rel_constraints = 
    List.map (fun rel ->
        mk_and
          srk
          [mk_leq srk (mk_zero srk) (named_rel rel);
           mk_lt srk (named_rel rel) (mk_int srk (List.length (Proposition.names_of rel)))])
      rels
  in
  let rule_clauses = 
    List.map (fun (conc, hypo, constr) -> 
        let chcvar_of_fv = Hashtbl.create 97 in
        let congruent_fvs = BatArray.make (List.length (Proposition.names_of conc)) [] in
        let _ = List.fold_left (fun fv_counter prop ->
            BatList.fold_lefti (fun fv_counter' ind _ ->
                if prop = conc
                then congruent_fvs.(ind) <- (fv_counter' :: (congruent_fvs.(ind)))
                else ();
                Hashtbl.add chcvar_of_fv fv_counter' (prop, ind);
                fv_counter' + 1)
              fv_counter
              (Proposition.names_of prop))
            0
            (conc :: hypo)
        in
        let classes = determine_eq_int_fvs srk constr in
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
                  else ((chcvar :: non_conc_fvs, conc_fvs), unusable_fvs)
                )
                (([], []), [])
                (BatSet.Int.elements set)
            )
            classes
        in
        let potential_eqs, unusables = List.split fv_class_lists in
        let unusables = List.flatten unusables in
        let make_lines (non_conc_fvs, conc_fvs) =
          (List.fold_left (fun edges conc_fv ->
               (List.map (fun non_conc_fv ->
                    mk_and srk [term_of conc_fv; term_of non_conc_fv])
                 non_conc_fvs) ::
           edges))
            []
            conc_fvs
        in

        let rules_edges_phi =
          mk_or
            srk
            (List.flatten (List.flatten (List.map make_lines potential_eqs)))
        in
        let inconsist_clause =
          mk_and
            srk
            (List.map (fun fv -> (mk_not srk (term_of fv))) unusables)
        in
        mk_and srk [rules_edges_phi; inconsist_clause]) 
      (Fp.get_rules fp)
  in
  rule_clauses @ rel_constraints




let get_offset_cands srk constr int_fvs_set =
  Log.errorf "constr is %a" (Formula.pp srk) constr;
  let constr = skolemize_offset srk constr in
  let arr_tbl = Memo.memo (fun a -> BatUref.uref (a, [])) in
  let int_tbl = Memo.memo (fun symbol -> BatUref.uref (symbol, BatSet.Int.empty)) in

  let rec populate_tbls_from_arith phi =
    match ArithTerm.destruct srk phi with
    | `Real _ | `App _ | `Var _ -> ()
    | `Add lst | `Mul lst -> List.iter populate_tbls_from_arith lst
    | `Binop (_, s, t) -> List.iter populate_tbls_from_arith [s; t]
    | `Unop (_, s) -> populate_tbls_from_arith s
    | `Ite _ -> assert false
    | `Select (a, i) ->
      let a = ArrTerm.eval srk arr_term_alg a in
      let a_c, lst = BatUref.uget (arr_tbl a) in
      BatUref.uset (arr_tbl a) (a_c, (symbols i) :: lst);
      BatHashtbl.iter (fun _ _ ->
          assert false)
        (free_vars i);
      populate_tbls_from_arith i 
  and populate_tbls_from_phi phi =
    match Formula.destruct srk phi with
    | `Tru | `Fls | `Proposition _ -> ()
    | `And lst | `Or lst -> List.iter populate_tbls_from_phi lst
    | `Not phi -> populate_tbls_from_phi phi
    | `Quantify _ -> assert false
    | `Atom (`Arith (`Eq, s, t)) ->
      (* Why do we need this? *)
      let has_arrays term = 
        (BatHashtbl.length (BatHashtbl.filter (fun a -> a = `TyArr) (free_vars term))) > 0
    || (Symbol.Set.exists (fun sym -> typ_symbol srk sym = `TyArr) (symbols term))
      in
      if has_arrays s || has_arrays t then 
        ()
      else (
        let fvs term = 
          snd (BatList.split (BatHashtbl.to_list (BatHashtbl.map (fun fv _ -> fv) (free_vars term)))) 
        in
        let fvs = BatSet.Int.union (BatSet.Int.of_list (fvs s)) (BatSet.Int.of_list (fvs t)) in
        let syms = Symbol.Set.union (symbols s) (symbols t) in
        match (Symbol.Set.to_list syms) with
        | [] -> ()
        | hd :: tl -> 
          let c, set = BatUref.uget (int_tbl hd) in
          BatUref.uset (int_tbl hd) (c, BatSet.Int.union fvs set);
          let sel (a, b) (_, d) = a, (BatSet.Int.union b d) in
          BatList.iter 
            (fun ele -> BatUref.unite ~sel (int_tbl hd) (int_tbl ele))
            tl);
      populate_tbls_from_arith s;
      populate_tbls_from_arith t
    | `Atom (`Arith (_, s, t)) -> List.iter populate_tbls_from_arith [s; t]
    | `Atom (`ArrEq (a, b)) ->
      let a = ArrTerm.eval srk arr_term_alg a in
      let b = ArrTerm.eval srk arr_term_alg b in
      let sel (a_c, a_set) (b_c, b_set) = 
        match a_c with
        | Fv _ -> a_c, a_set @ b_set
        | Sym _ -> b_c, a_set @ b_set
      in
      BatUref.unite 
        ~sel
        (arr_tbl a)
        (arr_tbl b)
    | `Ite _ -> assert false
  and arr_term_alg = function
    | `App (sym, []) -> Sym sym 
    | `Ite _ -> assert false 
    | `Store (arr, i, v) ->
      let a_c, lst = BatUref.uget (arr_tbl arr) in
      BatUref.uset (arr_tbl arr) (a_c, (symbols i) :: lst);
      BatHashtbl.iter (fun _ _ ->
          assert false;
          (*assert (typ = `TyInt);
          add_int_to_arr_tbl arr (Fv ind)*))
        (free_vars i);
      populate_tbls_from_arith i;
      populate_tbls_from_arith v;
      arr
    | `App _ -> assert false
    | `Var (i, _) -> Fv i
  in
  populate_tbls_from_phi constr;
  let arr_fv_cands = BatHashtbl.create 99 in
  Log.errorf "\n\n\n\nCREATING TABLRSi\n\n";
  BatHashtbl.iter (fun ind typ ->
      if typ = `TyArr then (
        Log.errorf "\n\nWORKING ON IND %n" ind;
        let arr_class, rws = BatUref.uget (arr_tbl (Fv ind)) in
        let arr_class = match arr_class with Fv fv -> fv | _ -> assert false in
        let rws_classes =
          BatList.fold_left (fun cands read_syms ->
              Log.errorf "INTERSECTION";

              let inter_with = 
                (Symbol.Set.fold (fun sym local_cands ->
                     Log.errorf "looking at symbol %s" (show_symbol srk sym);
                     BatSet.Int.union local_cands (snd (BatUref.uget (int_tbl sym))))
                    read_syms
                    BatSet.Int.empty)
              in
              Log.errorf "cardal midset is %n" (BatSet.Int.cardinal inter_with);
              BatSet.Int.inter
                cands
                inter_with)
            int_fvs_set
            rws
        in
        Log.errorf "TOTAL NUMB ELE IS %n" (BatSet.Int.cardinal rws_classes);
        BatHashtbl.add arr_fv_cands ind (arr_class, rws_classes))
      else ())
    (free_vars constr);
  arr_fv_cands



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


type arrvar = Sym of symbol | Fv of int

let determine_offsets srk fp =
  let global_partitioning = BatHashtbl.create 97 in
  List.iter (fun (conc, hypo, _) ->
      List.iter (fun prop ->
          List.iteri (fun param typ ->
              if typ = `TyArr then (
                Hashtbl.replace 
                  global_partitioning 
                  {rel=Proposition.symbol_of prop; param} 
                  (BatUref.uref 
                     (CHCVarSet.singleton {rel=Proposition.symbol_of prop; param}, 
                      BatHashtbl.create 97)))
              else ())
            (Proposition.typ_of_params srk prop))
        (conc :: hypo))
    (Fp.get_rules fp);

  let merge_tblsets tbl1 tbl2 =
    BatHashtbl.merge (fun _ tbl1_entry tbl2_entry ->
    match tbl1_entry, tbl2_entry with
    | Some a, Some b -> Some (BatSet.Int.inter a b) 
    | None, a -> a
    | a, None -> a)
      tbl1
      tbl2
  in
  List.iteri (fun _ (conc, hypo, constr) ->
      let fvcounter = ref 0 in
      let chcvar_tbl = Hashtbl.create 50 in
      let int_fvs_set = ref BatSet.Int.empty in
      List.iter (fun prop ->
          List.iteri (fun param typ ->
              Hashtbl.add chcvar_tbl !fvcounter {rel=Proposition.symbol_of prop; param};
              if typ = `TyInt then int_fvs_set := BatSet.Int.add !fvcounter !int_fvs_set else ();
              fvcounter := !fvcounter + 1)
            (Proposition.typ_of_params srk prop))
        (conc :: hypo);
      let chcvar_of fv = Hashtbl.find chcvar_tbl fv in

      Log.errorf "DONE";
      let arr_cell_of fv = Hashtbl.find global_partitioning (chcvar_of fv) in
      
      let offset_cands = get_offset_cands srk constr !int_fvs_set in
      BatHashtbl.iter (fun arr_fv (local_arr_cell, int_fvs) ->
          let sel (a, candsa) (b, candsb) = (CHCVarSet.union a b), (merge_tblsets candsa candsb) in
          BatUref.unite ~sel (arr_cell_of arr_fv) (arr_cell_of local_arr_cell);
          let arr_cell' = CHCVarSet.singleton (chcvar_of local_arr_cell) in
          let local_cands = BatHashtbl.create 97 in
          BatList.iter (fun chcvar ->
              BatHashtbl.modify_def
                BatSet.Int.empty
                chcvar.rel 
                (BatSet.Int.add chcvar.param)
                local_cands
            )
            (List.map (fun fv -> chcvar_of fv) (BatSet.Int.to_list int_fvs));
          let cell, cands = BatUref.uget (arr_cell_of arr_fv) in
          let cands' = merge_tblsets cands local_cands in
          BatUref.uset (arr_cell_of arr_fv) (CHCVarSet.union cell arr_cell', cands'))
        offset_cands;)
    (Fp.get_rules fp);
  let array_cells = 
    let cell_refs_dups = BatList.of_enum (BatHashtbl.values global_partitioning) in
    let cell_refs =
      List.fold_left (fun acc cell -> 
          if List.mem cell acc then acc else cell :: acc)
        []
        cell_refs_dups
    in
    List.map (fun cell_ref -> BatUref.uget cell_ref) cell_refs
  in
  let _ = 
  BatList.map (fun (arrs, offsetcands) ->
      let relations = CHCVarSet.fold (fun chcvar relations ->
          Symbol.Set.add chcvar.rel relations)
          arrs
          Symbol.Set.empty
      in
      let subchc = 
        Fp.filter_rules (fun (conc, hypos, _) ->
            let hypo_rels = Symbol.Set.of_list 
                (List.map (fun prop -> Proposition.symbol_of prop) hypos)
            in
            (Symbol.Set.mem (Proposition.symbol_of conc) relations) &&
            (not (Symbol.Set.disjoint hypo_rels relations)))
          fp
      in
      (*let subchc_consts = find_int_chc_consts subchc in*)
      ()
    )
    array_cells
  in
  global_partitioning



(*let select_offset_candidates srk fp candidates = *)

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
            | Phi
                (* Determines which trs in phi are monotonically increasing/decreasing *)phi -> Right phi
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
    | `Or disjs ->
      let disjs = List.map phiize disjs in
      begin match disjs with
        | [dis1; dis2] -> Disj (dis1, dis2) 
        | tl -> Phi (mk_or srk tl)
      end
    | phi -> Phi (Formula.map_construct srk phiize phi)
  in
  phiize (Formula.eval srk alg phi)






type 'a bool_factor_typ = Phi of (BatSet.Int.t * BatSet.Int.t * 'a formula)
                        | Disj of (BatSet.Int.t * BatSet.Int.t * BatSet.Int.t * BatSet.Int.t * 'a formula * 'a formula)
let bool_factor srk phi =
  let phiize bool_factor =
    match bool_factor with
    | Phi (fv_tru, fv_fls, phi) -> (fv_tru, fv_fls, phi)
    | Disj (fv_tru1, fv_fls1, fv_tru2, fv_fls2, phi1, phi2) -> 
      BatSet.Int.inter fv_tru1 fv_tru2, BatSet.Int.inter fv_fls1 fv_fls2, mk_or srk [phi1; phi2]
  in
  let alg = function
    | `And conjs ->
      let phis, disjs =
        BatList.partition_map (fun fact_typ ->
            match fact_typ with
            | Phi (_, _, phi) -> Left phi
            | Disj (fv_tru1, fv_fls1, _, _, phi1, phi2) -> 
              Right (fv_tru1, fv_fls1, phi1, phi2))
          conjs
      in
      let rec add_to_disj_lst disj_lsts (fv_tru', fv_fls', phi1', phi2') =
        match disj_lsts with
        | [] -> [fv_tru', fv_fls', [phi1'], [phi2']]
        | (fv_tru, fv_fls, phi1, phi2) :: tl ->
          if (BatSet.Int.cardinal (BatSet.Int.inter fv_tru fv_tru') > 0 ||
              BatSet.Int.cardinal (BatSet.Int.inter fv_fls fv_fls') > 0) then
            (BatSet.Int.union fv_tru fv_tru', 
            BatSet.Int.union fv_fls fv_fls', 
            phi1' :: phi1,
            phi2' :: phi2) :: tl
          else
            (fv_tru, fv_fls, phi1, phi2) :: (add_to_disj_lst tl (fv_tru', fv_fls', phi1', phi2'))
      in
      let disj_lst =
        List.fold_left (fun disj_lsts disj ->
            add_to_disj_lst disj_lsts disj)
          []
          disjs
      in
      let conjs_of_disjs = 
        List.map (fun (_, _, phis1, phis2) ->
            if List.length phis1 > 1 then
              mk_or srk [mk_and srk phis1; mk_and srk phis2]
            else mk_or srk [List.hd phis1; List.hd phis2])
          disj_lst
      in
      let phi' = mk_and srk (phis @ conjs_of_disjs) in
      let fv_trus, fv_flss =
        List.split
          (List.map (fun factor_typ ->
               match factor_typ with
               | Phi (fv_tru, fv_fls, _) -> fv_tru, fv_fls
               | Disj (fv_tru1, fv_fls1, fv_tru2, fv_fls2, _, _) ->
                 BatSet.Int.inter fv_tru1 fv_tru2, BatSet.Int.inter fv_fls1 fv_fls2)
              conjs)
      in
      let fv_tru' = List.fold_left BatSet.Int.union BatSet.Int.empty fv_trus in
      let fv_fls' = List.fold_left BatSet.Int.union BatSet.Int.empty fv_flss in 
      Phi (fv_tru', fv_fls', phi')
    | `Or disjs ->
      let disjs = List.map phiize disjs in
      begin match disjs with
        | [(fv_tru1, fv_fls1, dis1); (fv_tru2, fv_fls2, dis2)] -> 
          if BatSet.Int.cardinal (BatSet.Int.inter fv_tru1 fv_fls2) > 0 ||
             BatSet.Int.cardinal (BatSet.Int.inter fv_fls1 fv_tru2) > 0 
          then
            Disj (fv_tru1, fv_fls1, fv_tru2, fv_fls2, dis1, dis2)
          else Phi (BatSet.Int.inter fv_tru1 fv_tru2,
                    BatSet.Int.inter fv_fls1 fv_fls2,
                    mk_or srk [dis1; dis2])
        | tl ->
          let fv_tru, fv_fls, phis = 
            List.fold_left (fun (fv_trus, fv_flss, phis) (fv_tru, fv_fls, phi) ->
                BatSet.Int.inter fv_trus fv_tru, BatSet.Int.inter fv_flss fv_fls,
                phi :: phis)
              (BatSet.Int.empty, BatSet.Int.empty, [])
              tl
          in
          Phi (fv_tru, fv_fls, mk_or srk phis)
      end
    | `Tru -> Phi (BatSet.Int.empty, BatSet.Int.empty, mk_true srk)
    | `Fls -> Phi (BatSet.Int.empty, BatSet.Int.empty, mk_true srk)
    | `Atom (`Arith (`Eq, s, t)) ->
      Phi (BatSet.Int.empty, BatSet.Int.empty, mk_eq srk s t)
    | `Atom (`Arith (`Leq, s, t)) ->
      Phi (BatSet.Int.empty, BatSet.Int.empty, mk_leq srk s t)
    | `Atom (`Arith (`Lt, s, t)) ->
     Phi (BatSet.Int.empty, BatSet.Int.empty, mk_lt srk s t)
    | `Atom(`ArrEq (a, b)) ->
      Phi (BatSet.Int.empty, BatSet.Int.empty, mk_arr_eq srk a b)
    | `Ite _ -> failwith "elim ite first"
    | `Not phi ->
      let tru, fls, phi = phiize phi in
      Phi (fls, tru, mk_not srk phi)
    | `Proposition (`Var i) -> Phi (BatSet.Int.singleton i, BatSet.Int.empty, mk_var srk i `TyBool)
    | `Proposition (`App (sym, lst)) -> Phi (BatSet.Int.empty, BatSet.Int.empty, mk_app srk sym lst)
    | `Quantify (`Exists, name, typ, phi) -> 
      let _, _, phi = phiize phi in
      Phi (BatSet.Int.empty, BatSet.Int.empty, mk_exists srk ~name typ phi)
    | `Quantify _ -> failwith "no forall"
  in
  let _, _, phi = phiize (Formula.eval srk alg phi) in
  phi

(* Replaces existentially bound vars with skolem constants. *)
let skolemize_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, skolemize srk constr) 
    fp



let eq_guided_bool_only_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, Quantifier.eq_guided_qe_bool_only srk constr) 
    fp

let prenex_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, Formula.prenex srk constr) 
    fp

let dumb_factor_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, dumb_factor srk true constr) 
    fp


let bool_factor_chc srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo, bool_factor srk constr) 
    fp


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



let eq_guided_qe srk fp =
  Fp.map_rules (fun (conc, hypo, constr) -> 
      conc, hypo,
      (Quantifier.eq_guided_qe srk 
      (Quantifier.eq_guided_qe_old srk 

      (dumb_factor srk true 
      (Quantifier.eq_guided_qe_old srk 
        (Quantifier.miniscope srk
           (dumb_factor srk false 
           (     Quantifier.eq_guided_qe_old srk 
                   (Quantifier.miniscope srk 
           (
      Quantifier.eq_guided_qe_old srk 
        (Quantifier.miniscope srk 
           (Quantifier.eq_guided_qe_old srk (Quantifier.miniscope srk constr)))) )))))))))
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
  let projection srk tf =
    let map = Hashtbl.create (List.length (arr_trs srk tf) * 8 / 3) in
    let j = mk_symbol srk ~name:"j" `TyInt in
    let j' = mk_symbol srk ~name:"j'" `TyInt in

    let f (trs, arr_only_trs, phi) (a, a') = 
      let z = mk_symbol srk ~name:("z"^(show_symbol srk a)) `TyInt in
      let z' = mk_symbol srk ~name:("z'"^(show_symbol srk a')) `TyInt in
      Hashtbl.add map z a;
      Hashtbl.add map z' a';
      (z, z') :: trs,
      (z, z') :: arr_only_trs,
      mk_and 
        srk 
        [mk_eq srk (mk_const srk z) (mk_select srk (mk_const srk a) (mk_const srk j));
         mk_eq srk (mk_const srk z') (mk_select srk (mk_const srk a') (mk_const srk j));
         phi]
    in
    let integer_trs, arr_only_trs, phi = 
      List.fold_left f ((j, j') :: int_trs srk tf, [], T.formula tf) (arr_trs srk tf) 
    in
    (* TODO: Fix assumption that no symbolic constants *)
    let phi = 
      mk_exists_consts srk (fun sym -> List.mem sym (flatten integer_trs)) phi 
    in
    j, j', map, T.make (mk_and srk [phi; mk_eq srk (mk_const srk j) (mk_const srk j')]) integer_trs, arr_only_trs 

  (* Convert from a pmfa formula to an mfa formula.
   * We achieve this by converting the pmfa formula to an equivalent formula
   * in qnf such that there is a single universal quantifier. The key algorithm
   * thus is just a merging of the matrices under potentially many (non-nested) 
   * universal quantifiers. We factor the universal quantifier over disjunction
   * by introducing a new quantified integer sorted variable that acts a boolean
   * that determines which disjunct is "on".*)
  let to_mfa srk tf =
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
    let phi = subst_existentials [] (T.formula tf) in
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
    let uq_sym = mk_symbol srk `TyInt in
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
          let sym = mk_symbol srk `TyInt in
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
    mk_exists_consts srk (fun sym -> not (Symbol.Set.mem sym !nuqr_syms)) phi'


  let pmfa_to_lia srk tf =
    let tf = TransitionFormula.map_formula (eliminate_ite srk) tf in
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
    | _ -> assert false
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



  module Array_analysis (Iter : PreDomain) = struct

    type 'a t = 
      { iter_obj : 'a Iter.t; 
        proj_ind : Symbol.t;
        proj_indpost : Symbol.t;
        arr_map : (Symbol.t, Symbol.t) Hashtbl.t;
        iter_trs : (Symbol.t * Symbol.t) list;
        ground_lia : 'a formula;
        arr_only_trs : (symbol * symbol) list; }

    let abstract srk tf =
      let exists = TransitionFormula.exists tf in
      let phi = eliminate_stores srk (T.formula tf) in
      let phi = eliminate_ite srk phi in
      let phi = unbooleanize srk phi in
      let tf_pmfa = T.update_formula tf phi in
      let proj_ind, proj_indpost, arr_map, tf_proj, arr_only_trs = projection srk tf_pmfa in
      let lia_tf = pmfa_to_lia srk tf_proj in
      let lia = Quantifier.eg_simplification srk (T.formula lia_tf) in
      let ground_lia = Quantifier.mbp_qe_inplace srk lia in
      let ground_tf = TransitionFormula.make ~exists ground_lia (T.symbols lia_tf) in
      let iter_obj = Iter.abstract srk ground_tf in

      {iter_obj;
       proj_ind;
       proj_indpost;
       arr_map;
       iter_trs=(T.symbols lia_tf);
       ground_lia;
       arr_only_trs }
(*
    type 'a dir_var = Inc of 'a arith_term * 'a arith_term | Dec of 'a arith_term * 'a arith_term
    
    (* Determines which trs in phi are monotonically increasing/decreasing *)
    let directional_vars srk phi trs =
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

    let create_phased_exps srk phi trs symb_index directs lc =
      let exp1term = mk_symbol srk ~name:"exp1" `TyInt in
      let exp2term = mk_symbol srk ~name:"exp2" `TyInt in
      List.map (fun direction ->
          match direction with
          | Inc (x, x') ->
            let j = mk_const srk symb_index in

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
                            (T.make (mk_and srk [phi; mk_leq srk x j; mk_leq srk x' j]) trs));
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
                            (T.make (mk_and srk [phi; mk_lt srk j x; mk_lt srk j x']) trs));
                    mk_lt srk j x; mk_lt srk j x'])
                trs
            in
            let intermediate_tr = 
              T.make 
                (mk_and srk [phi; mk_leq srk x j; mk_lt srk j x'])
                trs
            in

            let phased_tr = T.mul srk (T.mul srk phase1 intermediate_tr) phase2 in

            (* Adds constraints on loop counter depending on which phase(s) taken*)
            let both_phases = 
              T.map_formula (fun f ->
                  mk_and 
                    srk
                    [mk_eq 
                       srk 
                       lc 
                       (mk_add srk [mk_const srk exp2term;
                                    mk_const srk exp1term;
                                    mk_int srk 1]);
                     f])
                phased_tr
            in
            let phase1_only = 
              T.map_formula (fun f ->
                  mk_and 
                    srk
                    [mk_eq srk lc (mk_const srk exp1term);
                     f])
                phase1
            in
            let phase2_only = 
              T.map_formula (fun f ->
                  mk_and 
                    srk
                    [mk_eq srk lc (mk_const srk exp2term);
                     f])
                phase2
            in
                     

            let phased_exp =
              T.map_formula
                (fun f ->
                   mk_and
                     srk
                     [mk_leq srk (mk_zero srk) (mk_const srk exp1term); 
                      mk_leq srk (mk_zero srk) (mk_const srk exp2term);
                      f]) 
                (T.add srk (T.add srk both_phases phase1_only) phase2_only)
            in
            (* Need to quantify over newly introduce symbols *)
            (*
            let final =
              mk_exists_consts
                srk
                (fun sym -> not (Symbol.Set.mem sym !exists))
                entire_formula
            in*)
            T.map_formula 
              (fun f ->
                 mk_exists_const srk exp1term (mk_exists_const srk exp2term f))
              phased_exp

          | Dec _ -> T.make (mk_true srk) trs (* turned off for now to make testing smoother *)
            )
        directs, exp1term, exp2term
*)
     
    let at_most_single_write srk write noop trs =
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


    let exp srk _ lc obj =
      let arr_vars_eq = 
        mk_and
          srk
          (List.map (fun (z, z') -> mk_eq srk (mk_const srk z) (mk_const srk z')) obj.arr_only_trs)
      in
      let write = mk_and srk [obj.ground_lia; mk_not srk arr_vars_eq] in
      let noop = mk_and srk [obj.ground_lia; arr_vars_eq] in
      
      let write = T.make write obj.iter_trs in
      let noop = T.make noop obj.iter_trs in

      let projected_exp = 
        if at_most_single_write srk write noop obj.iter_trs 
        then (
          let exp1 = mk_symbol srk ~name:"exp1" `TyInt in
          let exp2 = mk_symbol srk ~name:"exp2" `TyInt in
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

          let write_once = T.formula (T.mul srk noop_star1 (T.mul srk write noop_star2)) in
          let write_once = 
            mk_and
              srk
              [write_once;
               mk_leq srk (mk_zero srk) (mk_const srk exp1);
               mk_leq srk (mk_zero srk) (mk_const srk exp2);
               mk_eq 
                 srk 
                 lc 
                 (mk_add srk [mk_const srk exp2; mk_const srk exp1; mk_int srk 1])]
          in
          let noop_only =
            mk_and
              srk
              [T.formula noop_star1;
               mk_leq srk (mk_zero srk) (mk_const srk exp1);
               mk_eq 
                 srk 
                 lc 
                 (mk_const srk exp1)]
          in
          mk_or srk [write_once; noop_only])
        else assert false
      in

      let noop_eqs = 
        List.map 
          (fun (x, x') -> mk_eq srk (mk_const srk x) (mk_const srk x'))
          obj.iter_trs
      in
      (* Will need to do some kind of mbp to get rid of new vars *)
      let exp_res_pre = 
        mk_or 
          srk 
          [mk_and srk ((mk_eq srk lc (mk_int srk 0)) :: noop_eqs); projected_exp] 
      in
      let map sym =  
        if sym = obj.proj_ind || sym = obj.proj_indpost 
        then mk_var srk 0 `TyInt
        else if Hashtbl.mem obj.arr_map sym 
        then mk_select srk (mk_const srk (Hashtbl.find obj.arr_map sym)) 
            (mk_var srk 0 `TyInt) 
        else mk_const srk sym
      in
      let substed = substitute_const srk map exp_res_pre in
      let res = (mk_forall srk `TyInt substed) in
      res

    
   (* 
    let exp srk _ lc obj =
      let directs = directional_vars srk obj.ground_lia obj.iter_trs in
      let directs_res, _, _ = create_phased_exps srk obj.ground_lia obj.iter_trs obj.proj_ind directs lc in
      let noop_eqs = 
        List.map 
          (fun (x, x') -> mk_eq srk (mk_const srk x) (mk_const srk x'))
          obj.iter_trs
      in
      (* Redo this part to act on tfs rather than first converting to formula *)
      let directs_res = List.map (fun f -> T.formula f) directs_res in
      let direct_res = mk_and srk directs_res in
      let direct_res = Quantifier.mbp_qe_inplace srk direct_res in 
      let exp_res_pre = 
        mk_or 
          srk 
          [mk_and srk ((mk_eq srk lc (mk_int srk 0)) :: noop_eqs); direct_res] 
      in
      let map sym =  
        if sym = obj.proj_ind || sym = obj.proj_indpost 
        then mk_var srk 0 `TyInt
        else if Hashtbl.mem obj.arr_map sym 
        then mk_select srk (mk_const srk (Hashtbl.find obj.arr_map sym)) 
            (mk_var srk 0 `TyInt) 
        else mk_const srk sym
      in
      let substed = substitute_const srk map exp_res_pre in
      let res = (mk_forall srk `TyInt substed) in
      res
*)
    let pp _ _ _= failwith "todo 10"

  end
end
