(** The type of backward paths. A value of type [t] describes a path from a subterm to the root. *)
type t = private
  | Root  (** [Root] corresponds to the empty path. *)
  | At_index of int * t
      (** [At_index(i, p)] corresponds to the [i]th subterm corresponding to the term at path [p]. *)

(** The type of forward paths. A value of type [forward] describes a path from the root to a subterm. *)
type forward = int list

(** [root] is {!Root} *)
val root : t

(** [at_index i p] is [At_index (i, p)]. *)
val at_index : int -> t -> t

(** [concat above under] is the path obtained by concatenating [above] and [under]. *)
val concat : above:t -> under:t -> t

(** [reverse p] is the forward path corresponding to the backward path [p]. *)
val reverse : t -> forward

(** [compare] is a total order. *)
val compare : t -> t -> int

(** [equal s1 s2] tests whether [s1] and [s2] are equal. *)
val equal : t -> t -> bool

(** [hash s] is a hash of [s]. *)
val hash : t -> int

(** [pp fmt s] prints a representation of [s] to the formatter [fmt]. *)
val pp : Format.formatter -> t -> unit

val to_string : t -> string
