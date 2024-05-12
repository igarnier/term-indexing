type 'prim term = 'prim desc Hashcons.hash_consed

and 'prim desc = private Prim of 'prim * 'prim term array | Var of int

val fold : ('a term -> Path.t -> 'b -> 'b) -> 'b -> 'a term -> 'b

module type S = sig
  type prim

  type t = prim term

  type var := int

  type 'a var_map

  val equal : t -> t -> bool

  val hash : t -> int

  val prim : prim -> t array -> t

  val var : var -> t

  val is_var : t -> var option

  val fold : (t -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  val fold_variables : (var -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  val get_subterm_fwd : t -> Path.forward -> t

  val get_subterm : t -> Path.t -> t

  val subst : term:t -> path:Path.t -> replacement:t -> t

  val canon : t -> (unit -> var) -> var var_map * t

  val pp : Format.formatter -> t -> unit
end

module Make_hash_consed : functor
  (P : Intf.Signature)
  (M : Intf.Map with type key = int)
  -> S with type prim = P.t and type 'a var_map = 'a M.t
