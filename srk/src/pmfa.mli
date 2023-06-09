open Syntax

module OldPmfa : sig
  open Iteration
  module V = Linear.QQVector
  module M = Linear.QQMatrix
  module Z = Linear.ZZVector
  module T = TransitionFormula
  val pmfa_to_lia : 'a context -> 'a formula -> 'a formula * Symbol.Set.t

  val unskolemize_int_arr : 'a context -> 'a formula -> 'a formula



  val unbooleanize : 'a context -> 'a formula -> 'a formula

  (* [projection srk tf] returns [(j, j', map, tf')] where [tf'] is a
   * projection of the transition formula [tf] such that for any array
   * transition relation [(a, a')] in [tf], the dynamics of [(a, a')] are
   * projected to just their contents at symbolic index [j], captured by the
   * transition relation [(map a, map a')] of [tf'].*) 
  val projection :  
    'a context -> 'a T.t  -> 'a Syntax.Symbol.Map.t ->
    Syntax.Symbol.Set.t ->
    symbol * (symbol, symbol) Hashtbl.t * 'a T.t * (symbol * symbol) list

  module Array_analysis (Iter : PreDomain) (Iter2 : PreDomain) : sig
    include PreDomain
    val mp : 'a context -> 'a T.t -> 'a formula
  end
end
