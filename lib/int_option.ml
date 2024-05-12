type t = int

let none = Int.max_int

let of_int x =
  if x = Int.max_int - 1 then invalid_arg "Int_option.of_int" else x + 1

let elim x ifnone ifsome = if x = none then ifnone else ifsome (x - 1)

let is_none x = x = none
