open Syntax
open Chc


type arrvar = Sym of symbol | Fv of int

val skolemize : 'a context -> 'a formula -> 'a formula
val skolemize_chc : 'a context -> 'a fp -> 'a fp
val prenex_chc : 'a context -> 'a fp -> 'a fp
val check_q_array_chc : 'a context -> 'a fp -> 'a fp
val dumb_factor_chc : 'a context -> 'a fp -> 'a fp

val bool_factor_chc : 'a context -> 'a fp -> 'a fp
val collapse_juncts_chc : 'a context -> 'a fp -> 'a fp
val eq_guided_bool_only_chc : 'a context -> 'a fp -> 'a fp
val elim_ite_chc : 'a context -> 'a fp -> 'a fp

val get_offset_cands : 'a context -> 'a formula -> (int, BatSet.Int.t) Hashtbl.t 





type chcvar = { rel : symbol; param : int} 

val eq_guided_qe : 'a context -> 'a fp -> 'a fp
val remove_skol_consts_chc : 'a context -> 'a fp -> 'a fp
(*val offset_partitioning : 'a context -> 'a formula -> (int, int BatUref.uref) Hashtbl.t*)

val determine_offsets : 'a context -> 'a fp -> 
           (chcvar,
            (chcvar * (Syntax.symbol, BatSet.Int.t) Hashtbl.t) BatUref.uref)
           Hashtbl.t 


type cell = Symbol of int | Zero
type offset = DNA | Cell of cell | Unrestricted

(*
val pmfa_chc_offset_partitioning : 'a context -> 'a fp -> 
  (chcvar, chcvar) Hashtbl.t * (int, (int, chcvar option) Hashtbl.t) Hashtbl.t*)
(*val verify_offset_candidates : 'a context -> 'a fp -> (symbol, int) Hashtbl.t -> bool*)
val apply_offset_candidates : 
  'a context -> 
  'a fp ->
  (int, (arrvar, chcvar option) Hashtbl.t) Hashtbl.t ->
  (int * chcvar, offset) Hashtbl.t ->
  'a fp
val propose_offset_candidates_seahorn : 
  'a context ->
  'a fp -> (chcvar, chcvar) Hashtbl.t -> (chcvar, (symbol, int option) Hashtbl.t) Hashtbl.t
val derive_offset_for_each_rule : 
  'a context ->
  'a fp ->
  (chcvar, (symbol, int option) Hashtbl.t) Hashtbl.t ->
  (int * chcvar, offset) Hashtbl.t


module OldPmfa : sig
  open Iteration
  module V = Linear.QQVector
  module M = Linear.QQMatrix
  module Z = Linear.ZZVector
  module T = TransitionFormula
  val pmfa_to_lia : 'a context -> 'a T.t -> 'a T.t

  val eliminate_stores : 'a context -> 'a formula -> 'a formula

  val unbooleanize : 'a context -> 'a formula -> 'a formula

  (* [projection srk tf] returns [(j, j', map, tf')] where [tf'] is a
   * projection of the transition formula [tf] such that for any array
   * transition relation [(a, a')] in [tf], the dynamics of [(a, a')] are
   * projected to just their contents at symbolic index [j], captured by the
   * transition relation [(map a, map a')] of [tf'].*) 
  val projection :  
    'a context -> 'a T.t -> symbol * symbol * (symbol, symbol) Hashtbl.t * 'a T.t

  module Array_analysis (Iter : PreDomain) : sig
    include PreDomain
  end
end
