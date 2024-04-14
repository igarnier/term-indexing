(** The type of signatures of first-order terms. *)
module type S = sig
  (** The type of symbols. *)
  type t

  (** [compare] is a total order on symbols. *)
  val compare : t -> t -> int

  (** [equal s1 s2] tests whether [s1] and [s2] are equal. *)
  val equal : t -> t -> bool

  (** [hash s] is a hash of [s]. *)
  val hash : t -> int

  (** [pp fmt s] prints a representation of [s] to the formatter [fmt]. *)
  val pp : Format.formatter -> t -> unit

  (** [arity s] is the arity of [s], i.e. a term with head [s] must have exactly [arity s] sub-terms. *)
  val arity : t -> int

  (** [var s] creates a symbol corresponding to the variable [s]. *)
  val var : int -> t

  (** [is_var s] is [Some n] if [s] is a variable equal to [n], and [None] otherwise. *)
  val is_var : t -> int option
end
