(** The type of hash-consed terms *)
type 'prim term = 'prim desc Hashcons.hash_consed

and 'prim desc = private
  | Prim of 'prim * 'prim term array * Int_option.t
      (** [Prim (prim, ts, ub)] represents a term with head symbol equal to [prim]
          and subterms [ts]. [ub] is equal to {!Int_option.none} if the term is
          ground. Otherwise, [ub] is an upper bound on the value of variables
          contained in [ts]. *)
  | Var of int  (** [Var v] is a variable equal to [v]. *)

val fold : ('a term -> Path.t -> 'b -> 'b) -> 'b -> 'a term -> 'b

(** The module type of terms. *)
module type S = sig
  (** The type of primitive symbols. *)
  type prim

  (** The type of terms. *)
  type t = prim term

  type var := int

  type 'a var_map

  (** [equal] is an O(1) equality test on terms. *)
  val equal : t -> t -> bool

  (** [hash] is an O(1) hash function. *)
  val hash : t -> int

  (** [prim prim ts] constructs a term with head symbol [prim] and subterms [ts]. *)
  val prim : prim -> t array -> t

  (** [var v] constructs a variable equal to [v]. *)
  val var : var -> t

  (** [ub t] is an upper bound on the absolute values of variables contained in [t],
      or [Int_option.none] if the term is ground. *)
  val ub : t -> Int_option.t

  (** [is_var t] returns [Some v] if [t] is a variable equal to [v]. *)
  val is_var : t -> var option

  (** [fold f acc t] folds [f] over the subterms of [t]. *)
  val fold : (t -> Path.t -> 'acc -> 'acc) -> 'acc -> t -> 'acc

  (** [fold_variables f acc t] folds [f] over the variables of [t]. *)
  val fold_variables : (var -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  (** [map_variables f t] maps [f] over the variables of [t]. *)
  val map_variables : (int -> t) -> t -> t

  (** [get_subterm_fwd t p] returns the subterm of [t] at forward path [p]. *)
  val get_subterm_fwd : t -> Path.forward -> t

  (** [get_subterm t p] returns the subterm of [t] at path [p]. *)
  val get_subterm : t -> Path.t -> t

  (** [subst ~term ~path ~replacement] substitutes [replacement] for the subterm of [term] at path [path]. *)
  val subst : term:t -> path:Path.t -> replacement:t -> t

  (** [canon term gen] returns a canonical representation of [term] given a function [gen] that generates fresh variables. *)
  val canon : t -> (unit -> var) -> var var_map * t

  val pp : Format.formatter -> t -> unit
end

(** The following functor instantiates a module to manipulate hash-consed terms over the
    signature [P], using an implementation of persistent maps given by [M]. *)
module Make_hash_consed : functor
  (P : Intf.Signature)
  (M : Intf.Map with type key = int)
  -> S with type prim = P.t and type 'a var_map = 'a M.t
