type t = int

let none = Int.min_int

let of_int x =
  if x = Int.max_int then invalid_arg "Int_option.of_int" else x + 1

let elim x ifnone ifsome = if x = none then ifnone else ifsome (x - 1)

let is_none x = x = none

let max = Int.max
