open Syntax
open Chc


type vars = Sym of symbol | Fv of int

val skolemize : 'a context -> 'a formula -> 'a formula
val skolemize_chc : 'a context -> 'a fp -> 'a fp
val skolemize_eh :
  'a Syntax.context ->
  'b ->
  'a Syntax.Formula.t -> 'a Syntax.formula * Syntax.Symbol.Set.t
val skolemize_eh_chc : 'a context -> 'a fp -> 'a fp
val prenex_chc : 'a context -> 'a fp -> 'a fp
val check_q_array_chc : 'a context -> 'a fp -> 'a fp
val dumb_factor_chc : 'a context -> 'a fp -> 'a fp

val bool_factor_chc : 'a context -> 'a fp -> 'a fp
val collapse_juncts_chc : 'a context -> 'a fp -> 'a fp
val eq_guided_bool_only_chc : 'a context -> 'a fp -> 'a fp
val elim_ite_chc : 'a context -> 'a fp -> 'a fp

val offset_analysis : 'a context -> 'a fp -> 'a fp

val create_offset_formula :
           'a Syntax.context ->
           'a Chc.fp ->
           (Syntax.symbol, 'a Syntax.arith_term) Hashtbl.t ->
           (Syntax.symbol, BatSet.Int.t) Hashtbl.t -> 'a Syntax.formula list


type chcvar = { sym : symbol; param : int} 

module CVSet : BatSet.S with type elt = chcvar

val eq_guided_qe : 'a context -> 'a fp -> 'a fp
val remove_skol_consts_chc : 'a context -> 'a fp -> 'a fp
(*val offset_partitioning : 'a context -> 'a formula -> (int, int BatUref.uref) Hashtbl.t*)

val determine_offsets : 'a context -> 'a fp ->
(Syntax.symbol, int) Hashtbl.t array * (chcvar, int) Hashtbl.t * (Syntax.symbol, int) Hashtbl.t



val eliminate_stores : 'a context -> 'a formula -> 'a formula

module OldPmfa : sig
  open Iteration
  module V = Linear.QQVector
  module M = Linear.QQMatrix
  module Z = Linear.ZZVector
  module T = TransitionFormula
  val pmfa_to_lia : 'a context -> 'a T.t -> 'a T.t


  val unbooleanize : 'a context -> 'a formula -> 'a formula

  (* [projection srk tf] returns [(j, j', map, tf')] where [tf'] is a
   * projection of the transition formula [tf] such that for any array
   * transition relation [(a, a')] in [tf], the dynamics of [(a, a')] are
   * projected to just their contents at symbolic index [j], captured by the
   * transition relation [(map a, map a')] of [tf'].*) 
  val projection :  
    'a context -> 'a T.t -> symbol * symbol * (symbol, symbol) Hashtbl.t * 'a T.t * (symbol * symbol) list

  module Array_analysis (Iter : PreDomain) (Iter2 : PreDomain) : sig
    include PreDomain
  end
end
