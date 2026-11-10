open Syntax

(** Eliminate existential array temporaries with finitely many explicit
    definitions, preserving logical equivalence. Each candidate is substituted
    into the entire body, retaining guards and all other constraints.

    Unsupported definitions and sets exceeding eight candidates are left
    unchanged. The per-temporary limit is not a global formula-size bound. *)
val eliminate : ?limit:int -> 'a context -> 'a formula -> 'a formula
