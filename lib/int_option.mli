(** A space-efficient encoding of [int option] *)
type t

val none : t

val of_int : int -> t

val elim : t -> 'a -> (int -> 'a) -> 'a

val is_none : t -> bool
