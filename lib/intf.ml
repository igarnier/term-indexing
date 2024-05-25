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

(** The module type of finite maps. *)
module type Map = sig
  (** The type of keys. *)
  type key

  (** The type of maps polymorphic in their values. *)
  type 'a t

  (** [empty ()] is the empty map. *)
  val empty : unit -> 'a t

  (** [is_empty m] is true if and only if [m] is empty. *)
  val is_empty : 'a t -> bool

  (** [find_opt k m] is [Some v] if [k] is bound to [v] in [m], and [None] otherwise. *)
  val find_opt : key -> 'a t -> 'a option

  (** [add k v m] is the map that binds [k] to [v] in [m]. If [k] is already bound, the previous binding is shadowed. *)
  val add : key -> 'a -> 'a t -> 'a t

  (** [equal eq m1 m2] is true if and only if [m1] and [m2] are equal according to [eq]. *)
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  (** [union m1 m2] is the union of [m1] and [m2].

      @raise Invalid_argument if [m1] and [m2] have overlapping domains.
  *)
  val union : 'a t -> 'a t -> 'a t

  (** [to_seq m] produces the {b persistent} sequence of elements of [m] in
      increasing key order. *)
  val to_seq : 'a t -> (key * 'a) Seq.t

  (** [of_seq_keys m] is the sequence of keys of [m] *)
  val to_seq_keys : 'a t -> key Seq.t

  (** [of_seq s] constructs a map from the elements of [s]. *)
  val of_seq : (key * 'a) Seq.t -> 'a t
end
