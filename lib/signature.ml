(** Hashable, totally ordered, printable types *)
module type Hashed = sig
  type t

  (** [compare] is a total order. *)
  val compare : t -> t -> int

  (** [equal s1 s2] tests whether [s1] and [s2] are equal. *)
  val equal : t -> t -> bool

  (** [hash s] is a hash of [s]. *)
  val hash : t -> int

  (** [pp fmt s] prints a representation of [s] to the formatter [fmt]. *)
  val pp : Format.formatter -> t -> unit
end

(** The type of signatures of first-order terms. *)
module type S = sig
  include Hashed

  (** [arity s] is the arity of [s], i.e. a term with head [s] must have exactly [arity s] sub-terms. *)
  val arity : t -> int
end
