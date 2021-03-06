(** Polynomials and Grobner bases. *)

open Syntax

(** Signature of univariate polynmials *)
module type Univariate = sig
  include Linear.Vector with type dim = int
  val order : t -> int
  val mul : t -> t -> t
  val one : t
  val scalar : scalar -> t
  val compose : t -> t -> t

  (** The polynomial [p(x) = x] *)
  val identity : t

  val eval : t -> scalar -> scalar

  (** Exponentiation *)
  val exp : t -> int -> t
end

(** Univariate polynomials over a given ring *)
module Uvp (R : Linear.Ring) : Univariate with type scalar = R.t

(** Univariate polynomials with rational coefficients *)
module QQX : sig
  include Univariate with type scalar = QQ.t

  val pp : Format.formatter -> t -> unit
  val show : t -> string

  (** Given a polynomial [p(x)], compute a polynomial [q(x)] such that that
      for every integer [x >= 0], we have [q(x) = sum_{i=0}^x p(i)]. *)
  val summation : t -> t

  (** Given a polynomial [p(x)], compute a factorization [p(x) = c*q1(x)^d1 *
      ... qn(x)^dn] such that each qi is an irreducible polynomial with
      integer coefficients. *)
  val factor : t -> QQ.t * ((t * int) list)
end

(** Monomials *)
module Monomial : sig
  type t
  type dim = int

  val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

  val mul : t -> t -> t
  val one : t
  val mul_term : dim -> int -> t -> t
  val singleton : dim -> int -> t
  val power : dim -> t -> int
  val enum : t -> (dim * int) BatEnum.t
  val of_enum : (dim * int) BatEnum.t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pivot : dim -> t -> (int * t)
  val div : t -> t -> t option

  (** Least common multiple *)
  val lcm : t -> t -> t

  (** {2 Monomial orderings} *)

  (** Lexicographic order *)
  val lex : t -> t -> [ `Eq | `Lt | `Gt ]

  (** Compare by total degree, then lexicographic order *)
  val deglex : t -> t -> [ `Eq | `Lt | `Gt ]

  (** Compare by total degree, then reverse lexicographic order *)
  val degrevlex : t -> t -> [ `Eq | `Lt | `Gt ]

  (** Given a list of *subsets* of dimensions [p1, ..., pn], a monomial [m]
      can be considered as a list of monomials ("blocks") [m1, ..., mn, m0],
      where each [mi] contains the dimensions that belong to [pi] (and not to
      any lower [i]), and m0 contains the dimensions not belonging to any pi.
      Given a monomial ordering for comparing blocks, the block ordering is
      the lexicographic ordering on monomials viewed as lists of blocks. *)
  val block :
    ((dim -> bool) list) ->
    (t -> t -> [ `Eq | `Lt | `Gt ]) ->
    (t -> t -> [ `Eq | `Lt | `Gt ])

  val term_of : ('a context) -> (dim -> 'a term) -> t -> 'a term
end

(** Multi-variate polynomials *)
module Mvp : sig
  include Linear.Vector with type dim = Monomial.t
                         and type scalar = QQ.t
  val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit
  val compare : t -> t -> int
  val mul : t -> t -> t
  val sub : t -> t -> t
  val one : t
  val scalar : QQ.t -> t
  val of_dim : Monomial.dim -> t

  (** Convert a rational vector to a linear polynomial, where each dimension
      corresponds to a variable except the designated [const] dimension, which
      is treated at a constant 1. *)
  val of_vec : ?const:int -> Linear.QQVector.t -> t

  (** Write a polynomial as a sum [t + p], where [t] is a linear term and [p]
      is a polynomial in which every monomial has degree >= 2 *)
  val split_linear : ?const:int -> t -> (Linear.QQVector.t * t)

  (** Convert a linear polynomial to a vector, where each dimension
      corresponds to a variable except the designated [const] dimension, which
      is treated at a constant 1.  Return [None] if the polynomial is
      not linear. *)
  val vec_of : ?const:int -> t -> Linear.QQVector.t option

  val term_of : ('a context) -> (Monomial.dim -> 'a term) -> t -> 'a term

  (** Exponentiation by a positive integer *)
  val exp : t -> int -> t

  (** Generalization of polynomial composition -- substitute each dimension
      for a multivariate polynomial *)
  val substitute : (Monomial.dim -> t) -> t -> t

  (** Divide a polynomial by a monomial *)
  val div_monomial : t -> Monomial.t -> t option

  (** Enumerate the set of dimensions that appear in a polynomial *)
  val dimensions : t -> int BatEnum.t
end

(** Rewrite systems for multi-variate polynomials. A polynomial rewrite system
    consists of a set of polynomial rewrite rules [m1 -> p1, ..., mn -> pn]
    where each [mi] is a monomial, each [pi] is a polynomial, and such that
    [mi] is greater than any monomial in [pi] in some admissible order.  An
    admissible order is a total order on monomial such that for all [m], [n],
    [p], we have:
    1. [m <= n] implies [mp <= np]
    2. [m <= mp]
*)
module Rewrite : sig
  type t

  val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

  (** Given an admissible order and a list of zero polynomials, orient the
      polynomials into a rewrite system.  This generalizes Gauss-Jordan
      elimination, but (unlike Groebner basis computation) does not saturate
      the rewrite system with implied equations.  Thus, it can only be used as
      a semi-test for membership in the ideal generated by the input
      polynomials.  *)
  val mk_rewrite : (Monomial.t -> Monomial.t -> [ `Eq | `Lt | `Gt ]) ->
    Mvp.t list ->
    t

  val reduce_rewrite : t -> t

  (** Saturate a polynomial rewrite system with implied equalities  *)
  val grobner_basis : t -> t

  (** Reduce a multi-variate polynomial using the given rewrite rules until
      no more rewrite rules apply *)
  val reduce : t -> Mvp.t -> Mvp.t

  (** Reduce a multi-variate polynomial using the given rewrite rules until no
      more rewrite rules apply.  Return both the reduced polynomial and the
      polynomials used during reduction. *)
  val preduce : t -> Mvp.t -> (Mvp.t * Mvp.t list)

  (** Add a new zero-polynomial to a rewrite system and saturate *)
  val add_saturate : t -> Mvp.t -> t

  val generators : t -> Mvp.t list
end
