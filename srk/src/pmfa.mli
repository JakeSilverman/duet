open Syntax
open Chc


type arrvar = Sym of symbol | Fv of int

val skolemize : 'a context -> 'a formula -> 'a formula
val skolemize_chc : 'a context -> 'a fp -> 'a fp
val remove_skol_consts_chc : 'a context -> 'a fp -> 'a fp
val offset_partitioning : 'a context -> 'a formula -> (arrvar, arrvar BatUref.uref) Hashtbl.t
type chcvar = { rel : symbol; param : int} 


type cell = Symbol of int | Zero
type offset = DNA | Cell of cell | Unrestricted


val pmfa_chc_offset_partitioning : 'a context -> 'a fp -> 
  (chcvar, chcvar) Hashtbl.t * (int, (arrvar, chcvar option) Hashtbl.t) Hashtbl.t
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

  (*val projection : 'a context ->'a formula -> Symbol.Set.t -> 'a t*)

  (** Projects array trans. formula to lia trans formula at symbolic dimension.
      Return is tuple containing:
        projection index sym, primed and unprimed version,
        mapping from array symbol to its lia symbol
        lia trans. symbols and formula *)
  val projection :  
    'a context -> 'a T.t -> symbol * symbol * (symbol, symbol) Hashtbl.t * 'a T.t

  module Array_analysis (Iter : PreDomain) : sig
    include PreDomain
  end
end
