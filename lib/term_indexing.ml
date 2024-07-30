module Intf = Intf
module Pattern = Pattern
module Subst = Subst
module Term = Term
module Int_option = Int_option
module Term_index = Term_index
module Zipper = Zipper

module Make_internal (P : Intf.Signature) = struct
  module Default_map = Term.Default_map
  module Term = Term.Make_hash_consed (P) (Default_map)
  module Zipper = Zipper.Make (P) (Term)
  module Pattern = Pattern.Make (P) (Term) (Zipper)
  module Subst = Subst.Make (P) (Default_map) (Term)
  module Unification = Unification.Make (P) (Term) (Subst)
  module Index = Term_index.Make (P) (Term) (Subst)
end

(** [Make(P)] takes a {{!Term_indexing.Intf.Signature}[signature]} as input and returns
    a module packing the main features of the library. *)
module Make (P : Intf.Signature) : sig
  (** First-order terms. *)
  module Term : Intf.Term with type prim = P.t

  (** Zipper. *)
  module Zipper : Intf.Zipper with type term = Term.t

  (** Patterns over first-order terms and pattern matching. *)
  module Pattern :
    Intf.Pattern
      with type prim = P.t
       and type term = Term.t
       and type zipper = Zipper.t

  (** Handling substitutions. *)
  module Subst : Intf.Subst with type term = Term.t

  (** Solving unification problems on first-order terms. *)
  module Unification :
    Intf.Unification with type term = Term.t and type subst = Subst.t

  (** Term indexing. *)
  module Index :
    Intf.Term_index
      with type prim = P.t
       and type term = Term.t
       and type subst = Subst.t
end =
  Make_internal (P)
