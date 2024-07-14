type t = int

let equal = Int.equal

let none = Int.min_int

let of_int x =
  if x = Int.max_int then invalid_arg "Int_option.of_int" else x + 1

let elim x ifnone ifsome = if x = none then ifnone else ifsome (x - 1)

let is_none x = x = none

let max x y = if x > y then x else y

let pp fmtr x =
  if is_none x then Format.pp_print_string fmtr "none"
  else Format.fprintf fmtr "some %d" (x - 1)

let unsafe_to_int x = x - 1
