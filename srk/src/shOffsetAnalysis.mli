open Syntax
open Chc


type vars = Sym of symbol | Fv of int

val skolemize : 'a context -> 'a formula -> 'a formula
val skolemize_eh :
  'a Syntax.context ->
  'b ->
  'a Syntax.Formula.t -> 'a Syntax.formula * Syntax.Symbol.Set.t
val skolemize_eh_chc : 'a context -> 'a fp -> 'a fp
val check_q_array_chc : 'a context -> 'a fp -> 'a fp

val elim_ite_chc : 'a context -> 'a fp -> 'a fp

val offset_analysis : 'a context -> 'a fp -> 'a fp

val create_offset_formula :
           'a Syntax.context ->
           'a Chc.fp ->
           (Syntax.symbol, 'a Syntax.arith_term) Hashtbl.t ->
           (Syntax.symbol, BatSet.Int.t) Hashtbl.t -> 'a Syntax.formula list


type chcvar = { sym : symbol; param : int} 

module CVSet : BatSet.S with type elt = chcvar

val remove_skol_consts_chc : 'a context -> 'a fp -> 'a fp
(*val offset_partitioning : 'a context -> 'a formula -> (int, int BatUref.uref) Hashtbl.t*)

val determine_offsets : 'a context -> 'a fp ->
(Syntax.symbol, int) Hashtbl.t array * (chcvar, int) Hashtbl.t * (Syntax.symbol, int) Hashtbl.t



val eliminate_stores : 'a context -> 'a formula -> 'a formula


