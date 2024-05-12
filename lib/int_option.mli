(** A space-efficient encoding of [int option]. Only caveat: one cannot represent
    [Some Int.max_int]. *)
type t

val none : t

val of_int : int -> t

val elim : t -> 'a -> (int -> 'a) -> 'a

val is_none : t -> bool

val max : t -> t -> t
