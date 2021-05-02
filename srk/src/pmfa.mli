open Syntax
open Chc

val skolemize : 'a context -> 'a formula -> 'a formula * Symbol.Set.t
val offset_partitioning : 'a context -> 'a formula -> (symbol, int BatUref.uref) Hashtbl.t
type chcvar = { rel : Relation.t; param : int} 
val pmfa_chc_offset_partitioning : 'a context -> 'a fp -> (chcvar, chcvar BatUref.uref) Hashtbl.t
val verify_offset_candidates : 'a context -> 'a fp -> (relation, int) Hashtbl.t -> bool
val apply_offset_candidates : 
  'a context -> 
  'a fp ->
  (chcvar, chcvar) Hashtbl.t ->
  (chcvar, (relation, symbol) Hashtbl.t) Hashtbl.t -> 
  unit 
