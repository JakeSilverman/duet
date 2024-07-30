(* Constrained horn clauses *)
open Syntax

module Make
    (C : sig
       type t
       val context : t Syntax.context
     end) : sig

  type proposition
  type fp 



  module Proposition : sig
    type t = proposition
    val symbol_of : t -> symbol
    val names_of : t -> string list
    val typ_of_params : t -> typ_fo list
    val mk_proposition : symbol -> string list -> t
  end

  module Fp : sig
    type t = fp
    (** Create fixed point object with no rules/queries *)
    val empty : fp
    val add_rule : fp -> proposition -> proposition list -> C.t formula -> fp
    val get_rules : fp -> (proposition * proposition list * C.t formula) list
    val map_rules : ((proposition * proposition list * C.t formula) -> (proposition * proposition list * C.t formula)) -> fp -> fp
    val filter_rules : ((proposition * proposition list * C.t formula) -> bool) -> fp -> fp
    val filteri_rules : (int -> (proposition * proposition list * C.t formula) -> bool) -> fp -> fp
    val iteri_rules : (int -> (proposition * proposition list * C.t formula) -> unit) -> fp -> unit




    val mapi_rules : (int -> (proposition * proposition list * C.t formula) -> (proposition * proposition list * C.t formula)) -> fp -> fp

    (** Adds query to fp and returns a fresh name for query *)
    val add_query : fp -> symbol -> fp
    (* Returns set of relations that occur in either a rule or query in fp *)
    (*val predicate_symbols : 'a fp -> Symbol.Set.t*)
    val pp : Format.formatter -> fp -> unit
    val pp_rule : Format.formatter -> (proposition * proposition list * C.t formula) -> unit  
    val show : fp -> string

    val prop_symbols : fp -> Symbol.Set.t

    (*module type Absd = Abstract.MakeAbstractRSY(C).Domain*)

    (** [check srk fp pd] returns unknown if a query relation can
     * be reached in the fp where recursion over-approximated using the 
     * star operator of the provided predomain [pd] and returns no otherwise.*)
    val check : 
      fp -> (module Iteration.PreDomain) -> 
      [> `No | `Unknown | `Yes]
    (** [query_vc_condition srk fp pd] returns the final vc condition used in
     * [check srk fp pd]. That is, the vc condition to determine whether a query
     * relation can be reached in the fp where recursion over-approximated using 
     * the star operator of the provided predomain [pd].*)
    val query_vc_condition : 
      fp -> (module Iteration.PreDomain) -> C.t formula

    val query_vc_terminates : 
      fp -> (module Iteration.PreDomain) -> C.t formula 

    (** Solves a fp where recursion is over-approximated using the
     * star operator of the provided predomain [pd]. Where [f = solve srk fp pd]
     * and [r] is a relation used in [fp] the set of solutions to [r] is given by
     * [(syms, phi) = f r] where [phi] is a formula in which [syms.(i)]
     * gives the symbol used for the [i]th argument to [r].*)
    val solve : fp -> (module Iteration.PreDomain) ->
      (int -> C.t formula)
  end

  module ChcSrkZ3 : sig
    (* Convert z3 fixedpoint into srk fixedpoint *)
    val parse_z3fp : ?z3queries:Z3.Expr.expr list -> 
      Z3.Fixedpoint.fixedpoint -> fp
    val parse_file : ?ctx:Z3.context -> string -> fp 
    val parse_string : ?ctx:Z3.context -> string -> fp
  end
  module ShOffsetAnalysis : sig
    type vars = Sym of symbol | Fv of int
    val skolemize : C.t formula -> C.t formula
    val skolemize_eh :
      'b ->
      C.t Syntax.Formula.t -> C.t Syntax.formula * Syntax.Symbol.Set.t
    val skolemize_eh_chc : fp -> fp
    val check_q_array_chc : fp -> fp

    val elim_ite_chc : fp -> fp

    val offset_analysis : fp -> fp

    val create_offset_formula :
      fp ->
      (Syntax.symbol, C.t Syntax.arith_term) Hashtbl.t ->
      (Syntax.symbol, BatSet.Int.t) Hashtbl.t -> C.t Syntax.formula list


    type chcvar = { sym : symbol; param : int} 

    module CVSet : BatSet.S with type elt = chcvar

    val remove_skol_consts_chc : fp -> fp

    val determine_offsets : fp ->
      (Syntax.symbol, int) Hashtbl.t array * (chcvar, int) Hashtbl.t * (Syntax.symbol, int) Hashtbl.t



    val eliminate_stores : C.t formula -> C.t formula


  end
end
