(** The type of hash-consed terms *)
type 'prim term = 'prim desc Hashcons.hash_consed

and 'prim desc = private
  | Prim of 'prim * 'prim term array * Int_option.t
      (** [Prim (prim, ts, ub)] represents a term with head symbol equal to [prim]
          and subterms [ts]. [ub] is equal to {!Int_option.none} if the term is
          ground. Otherwise, [ub] is an upper bound on the value of variables
          contained in [ts]. *)
  | Var of int  (** [Var v] is a variable equal to [v]. *)

val fold : ('a term -> 'b -> 'b) -> 'b -> 'a term -> 'b

exception Get_subterm_oob of int list * int

(** The following functor instantiates a module to manipulate hash-consed terms over the
    signature [P], using an implementation of persistent maps given by [M]. *)
module Make_hash_consed : functor
  (P : Intf.Signature)
  (M : Intf.Map with type key = int)
  ->
  Intf.Term
    with type prim = P.t
     and type t = P.t term
     and type 'a var_map = 'a M.t

(** [Default_map] is a reasonable implementation of [Intf.Map] usable with {!Make_hash_consed} *)
module Default_map : Intf.Map with type key = int
