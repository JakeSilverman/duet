open Syntax
open Chc


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

let get_offset_cands srk constr =
  let constr = skolemize_offset srk constr in
  let arr_tbl = Memo.memo (fun a -> BatUref.uref (a, VarSet.empty)) in
  let int_tbl = Memo.memo (fun int_var -> 
      match int_var with
      | Fv fv -> BatUref.uref (int_var, BatSet.Int.singleton fv)
      | Sym _ -> BatUref.uref (int_var, (BatSet.Int.empty)))
  in

  let add_int_to_arr_tbl a i = 
    let a_c, set = BatUref.uget (arr_tbl a) in
    BatUref.uset (arr_tbl a) (a_c, VarSet.add i set)
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
      Symbol.Set.iter 
        (fun ele -> assert (typ_symbol srk ele = `TyInt); 
          add_int_to_arr_tbl a (Sym ele))
        (symbols i);
      BatHashtbl.iter (fun ind typ ->
          assert (typ = `TyInt);
          add_int_to_arr_tbl a (Fv ind))
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
        let syms term = List.map (fun sym -> Sym sym) (Symbol.Set.to_list (symbols term)) in
        let fvs term = 
          snd (BatList.split (BatHashtbl.to_list (BatHashtbl.map (fun fv _ -> Fv fv) (free_vars term)))) 
        in
        let vars = syms s @ syms t @ fvs s @ fvs t in
        if BatList.is_empty vars then ()
        else (
          let sel (a, b) (_, d) = a, (BatSet.Int.union b d) in
          BatList.iter 
            (fun ele -> BatUref.unite ~sel (int_tbl (List.hd vars)) (int_tbl ele))
            vars));
      populate_tbls_from_arith s;
      populate_tbls_from_arith t
    | `Atom (`Arith (_, s, t)) -> List.iter populate_tbls_from_arith [s; t]
    | `Atom (`ArrEq (a, b)) ->
      let a = ArrTerm.eval srk arr_term_alg a in
      let b = ArrTerm.eval srk arr_term_alg b in
      let sel (a_c, a_set) (b_c, b_set) = 
        match a_c with
        | Fv _ -> a_c, VarSet.union a_set b_set
        | Sym _ -> b_c, VarSet.union a_set b_set
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
      Symbol.Set.iter 
        (fun ele -> assert (typ_symbol srk ele = `TyInt); 
          add_int_to_arr_tbl arr (Sym ele))
        (symbols i);
      BatHashtbl.iter (fun ind typ ->
          assert (typ = `TyInt);
          add_int_to_arr_tbl arr (Fv ind))
        (free_vars i);
      populate_tbls_from_arith i;
      populate_tbls_from_arith v;
      arr
    | `App _ -> assert false
    | `Var (i, _) -> Fv i
  in
  populate_tbls_from_phi constr;
  let arr_fv_cands = BatHashtbl.create 99 in
  BatHashtbl.iter (fun ind typ ->
      if typ = `TyArr then (
        let arr_class, rws = BatUref.uget (arr_tbl (Fv ind)) in
        let arr_class = match arr_class with Fv fv -> fv | _ -> assert false in
        let rws_classes = 
          VarSet.fold (fun ele set -> BatSet.Int.union set (snd (BatUref.uget (int_tbl ele))))
            rws
            BatSet.Int.empty
        in
        BatHashtbl.add arr_fv_cands ind (arr_class, rws_classes))
      else ())
    (free_vars constr);
  arr_fv_cands
(*
  let fvs_ints, fvs_arrs = 
    BatHashtbl.fold (fun ind typ (fv_ints, fv_arrs) ->
        if typ = `TyArr
        then (fv_ints, BatSet.Int.add ind fv_arrs)
        else if typ = `TyInt
        then (BatSet.Int.add ind fv_ints, fv_arrs)
        else (fv_ints, fv_arrs))
      (free_vars constr)
      (BatSet.Int.empty, BatSet.Int.empty)
  in
  let arr_fv_cands = BatHashtbl.create 99 in
  BatSet.Int.iter (fun arr_fv ->
      BatHashtbl.add arr_fv_cands arr_fv BatSet.Int.empty;
      let cand_classes = 
        VarSet.fold 
          (fun ele acc -> (BatUref.uget (int_tbl ele)) :: acc)
          (BatUref.uget (arr_tbl (Fv arr_fv)))
          []
      in
      BatSet.Int.iter (fun ind_fv ->
          if List.mem (BatUref.uget (int_tbl (Fv ind_fv))) cand_classes
          then 
             BatHashtbl.modify arr_fv (BatSet.Int.add ind_fv) arr_fv_cands
          else ())
        fvs_ints)
    fvs_arrs;
  arr_fv_cands
*)

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

(* Not for general formula; just for those of the form we expect to be
 * output by seahorn; requries ite elim first *)
let offset_partitioning srk phi =
  Log.errorf "working on\n\n %a" (Formula.pp srk) phi;
  let phi = skolemize srk phi in
  Log.errorf "working on\n\n %a" (Formula.pp srk) phi;
  (* A map from arr var syms to BatUref objects. Two arr var syms belong
   * to the same cell if their BatUref holds the same value *)
  let class_map = BatHashtbl.create 97 in
  let vars_to_fv = BatHashtbl.create 97 in
  let subst = 
    Memo.memo (fun (ind, typ) ->
        if typ = `TyArr then (
          (* We will compute the equiv classes over the vars introduced
           * in this conditional and then we will transpose the result back
           * to the fvs later *)
          BatHashtbl.add class_map (Fv ind) (BatUref.uref (Fv ind));
          let sym = mk_symbol srk `TyArr in
          BatHashtbl.add vars_to_fv sym ind;
          mk_const srk sym
        )
        else mk_var srk ind typ)
  in

  Symbol.Set.iter (fun sym ->
      if typ_symbol srk sym = `TyArr then
        BatHashtbl.add class_map (Sym sym) (BatUref.uref (Sym sym))
      else ())
    (symbols phi);

  let phi = 
    substitute
      srk
      subst 
      phi
  in
  let merge_cells cells =
    List.fold_left (fun acc_cell cell ->
        match acc_cell, cell with
        | sym1, sym2 ->
          BatUref.unite 
            (BatHashtbl.find class_map sym1) 
            (BatHashtbl.find class_map sym2);
          sym1)
      (List.hd cells)
      cells
  in
  let rec arr_term_alg = function
    | `App (sym, []) -> 
      (* prob can't ensure no array.... doub check*)
      if BatHashtbl.mem vars_to_fv sym then
        Fv (BatHashtbl.find vars_to_fv sym)
      else Sym sym
    | `Ite _ -> assert false 
    | `Store (arr_cell, _, _) -> arr_cell
    | `App _
    | `Var _ -> assert false
  and formula_alg = function
    | `Atom(`ArrEq (a, b)) ->
       let cells1 = ArrTerm.eval srk arr_term_alg a in
       let cells2 = ArrTerm.eval srk arr_term_alg b in
       let _ = merge_cells ([cells1; cells2]) in
       ()
    | `Quantify (`Forall, _, _, _) -> failwith "Need to bring back old cell merging"
    | `Ite _ -> assert false
    | _ -> ()
  in
  let _ = Formula.eval srk formula_alg phi in
  let class_map_fv_only = BatHashtbl.create 97 in
  BatHashtbl.iter (fun k v ->
      match k, (BatUref.uget v) with
      | Fv i, Fv i2 -> BatHashtbl.add class_map_fv_only i i2
      | Fv _, _ -> assert false (* this will have an error - need to use sel during cell uniting *)
      | _ -> ())
    class_map;
  class_map_fv_only 


let determine_offsets srk fp =
  let global_partitioning = BatHashtbl.create 97 in
  List.iter (fun (conc, hypo, _) ->
      List.iter (fun prop ->
          List.iteri (fun param typ ->
              if typ = `TyArr then (
                Hashtbl.replace 
                  global_partitioning 
                  {rel=Proposition.symbol_of prop; param} 
                  (BatUref.uref ({rel=Proposition.symbol_of prop; param}, BatHashtbl.create 97)))
              else ())
            (Proposition.typ_of_params srk prop))
        (conc :: hypo))
    (Fp.get_rules fp);

  let merge_tblsets tbl1 tbl2 =
    BatHashtbl.merge (fun _ tbl1_entry tbl2_entry ->
    match tbl1_entry, tbl2_entry with
    | Some a, Some b -> Some (BatSet.Int.union a b) 
    | None, a -> a
    | a, None -> a)
      tbl1
      tbl2
  in
  List.iteri (fun _ (conc, hypo, constr) ->
      let fvcounter = ref 0 in
      let chcvar_tbl = Hashtbl.create 50 in
      List.iter (fun prop ->
          List.iteri (fun param _ ->
              Hashtbl.add chcvar_tbl !fvcounter {rel=Proposition.symbol_of prop; param};
              fvcounter := !fvcounter + 1)
            (Proposition.names_of prop))
        (conc :: hypo);
      let chcvar_of fv = Hashtbl.find chcvar_tbl fv in

      let local_arr_cells = offset_partitioning srk constr in
      Log.errorf "DONE";
      let arr_cell_of fv = Hashtbl.find global_partitioning (chcvar_of fv) in
      let sel (cella, namesa) (_, namesb) = 
        cella, merge_tblsets namesa namesb
      in
      let merge_cells cell1 cell2 = BatUref.unite ~sel cell1 cell2 in
      BatHashtbl.iter (fun local_arr local_cell ->
          if (arr_cell_of local_arr) = (arr_cell_of local_cell)
          then ()
          else merge_cells (arr_cell_of local_arr) (arr_cell_of local_cell))
        local_arr_cells;

      let offset_cands = get_offset_cands srk constr in
      BatHashtbl.iter (fun arr_fv (local_arr_cell, int_fvs) ->
          let arr_cell' = chcvar_of local_arr_cell in
          let local_cands = BatHashtbl.create 97 in
          BatList.iter (fun chcvar ->
              BatHashtbl.modify_def
                BatSet.Int.empty
                chcvar.rel 
                (BatSet.Int.add chcvar.param)
                local_cands
            )
            (List.map (fun fv -> chcvar_of fv) (BatSet.Int.to_list int_fvs));
          let _, cands = BatUref.uget (arr_cell_of arr_fv) in
          let cands' = merge_tblsets cands local_cands in
          BatUref.uset (arr_cell_of arr_fv) (arr_cell', cands'))
        offset_cands;)
    (Fp.get_rules fp);
  global_partitioning

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



module CHCVarSet = BatSet.Make(CHCVar)
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
    (* TODO: Fix assumption that no symbolic constants *)
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
        ground_lia : 'a formula}

    let abstract srk tf =
      let exists = TransitionFormula.exists tf in
      let phi = eliminate_stores srk (T.formula tf) in
      let phi = eliminate_ite srk phi in
      let phi = unbooleanize srk phi in
      let tf_pmfa = T.update_formula tf phi in
      let proj_ind, proj_indpost, arr_map, tf_proj = projection srk tf_pmfa in
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
       ground_lia;}

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

    let pp _ _ _= failwith "todo 10"

  end
end
