(** A space-efficient encoding of [int option]. Only caveat: one cannot represent
    [Some Int.max_int]. *)
type t = private int

val equal : t -> t -> bool

val none : t

val of_int : int -> t

val elim : t -> 'a -> (int -> 'a) -> 'a

val is_none : t -> bool

val max : t -> t -> t

val pp : Format.formatter -> t -> unit

val unsafe_to_int : t -> int
