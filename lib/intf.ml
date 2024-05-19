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
module type Signature = sig
  include Hashed

  (** [arity s] is the arity of [s], i.e. a term with head [s] must have exactly [arity s] sub-terms. *)
  val arity : t -> int
end

module type Map = sig
  type key

  type 'a t

  val empty : unit -> 'a t

  val is_empty : 'a t -> bool

  val find_opt : key -> 'a t -> 'a option

  val add : key -> 'a -> 'a t -> 'a t

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

  (** [to_seq m] produces the {b persistent} sequence of elements of [m] in
      increasing key order. *)
  val to_seq : 'a t -> (key * 'a) Seq.t

  val to_seq_keys : 'a t -> key Seq.t

  val of_seq : (key * 'a) Seq.t -> 'a t
end
