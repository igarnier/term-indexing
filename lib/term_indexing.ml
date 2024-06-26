module Intf = Intf
module Path = Path
module Pattern = Pattern
module Subst = Subst
module Term = Term
module Term_index = Term_index
module Slow_index = Slow_index

(** [Make(P)] takes a {{!Term_indexing.Intf.Signature}[signature]} as input and returns
    a module packing the main features of the library. *)
module Make (P : Intf.Signature) : sig
  (** First-order terms. *)
  module Term : Intf.Term with type prim = P.t

  (** Paths in first-order terms. *)
  module Path : module type of Path

  (** Patterns over first-order terms and pattern matching. *)
  module Pattern :
    Intf.Pattern
      with type prim = P.t
       and type path = Path.t
       and type term = Term.t

  (** Substitutions. *)
  module Subst : Intf.Subst with type term = Term.t

  (** Term indexing. *)
  module Index :
    Term_index.S
      with type prim = P.t
       and type term = Term.t
       and type subst = Subst.t
end = struct
  module Default_map = Term.Default_map
  module Term = Term.Make_hash_consed (P) (Default_map)
  module Path = Path
  module Pattern = Pattern.Make (P) (Term)
  module Subst = Subst.Make (P) (Default_map) (Term)
  module Index = Term_index.Make (P) (Term) (Subst)
end
