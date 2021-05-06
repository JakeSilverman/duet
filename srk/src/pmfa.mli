open Syntax
open Chc

val skolemize : 'a context -> 'a formula -> 'a formula * Symbol.Set.t
val offset_partitioning : 'a context -> 'a formula -> (symbol, symbol BatUref.uref) Hashtbl.t
type chcvar = { rel : Relation.t; param : int} 


type cell = Symbol of symbol | Zero
type offset = DNA | Cell of cell | Unrestricted


val pmfa_chc_offset_partitioning : 'a context -> 'a fp -> (chcvar, chcvar) Hashtbl.t
(*val verify_offset_candidates : 'a context -> 'a fp -> (relation, int) Hashtbl.t -> bool*)
val apply_offset_candidates : 
  'a context -> 
  'a fp ->
  (int, (Syntax.symbol, chcvar option) Hashtbl.t) Hashtbl.t ->
  (int * chcvar, offset) Hashtbl.t ->
  unit
(*val propose_offset_candidates_seahorn : 
  'a context -> 'a fp -> (chcvar, chcvar) Hashtbl.t -> (chcvar, (Chc.relation, int) Hashtbl.t) Hashtbl.t*)
