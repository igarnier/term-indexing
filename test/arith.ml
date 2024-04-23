open Lib_rewriting

module Prim = struct
  type t = Add | Sub | Mul | Div | Float of float

  let compare (x : t) (y : t) = Stdlib.compare x y

  let equal (x : t) (y : t) = x = y

  let hash = Hashtbl.hash

  let pp fmtr = function
    | Add -> Format.fprintf fmtr "Add"
    | Sub -> Format.fprintf fmtr "Sub"
    | Mul -> Format.fprintf fmtr "Mul"
    | Div -> Format.fprintf fmtr "Div"
    | Float f -> Format.fprintf fmtr "%f" f

  let arity = function Add | Sub | Mul | Div -> 2 | Float _ -> 0
end

module Expr = Term.Make_hash_consed (Prim)

let add x y = Expr.prim Add [| x; y |]

let sub x y = Expr.prim Sub [| x; y |]

let mul x y = Expr.prim Mul [| x; y |]

let div x y = Expr.prim Div [| x; y |]

let float f = Expr.prim (Prim.Float f) [||]

let var s = Expr.var s

(* ---------------------------------------- *)

module Gen = QCheck2.Gen

let symbol =
  Gen.frequencya
    [| (20, `Float);
       (20, `Var);
       (10, `Add);
       (10, `Sub);
       (10, `Mul);
       (10, `Div)
    |]

let var = Gen.map var Gen.small_nat

let float_ = Gen.map float (Gen.float_range (-1000.) 1000.)

let gen : Expr.t Gen.t =
  Gen.(
    fix
      (fun self n ->
        if n = 0 then oneof [var; float_]
        else
          symbol >>= function
          | `Add -> map2 add (self (n - 1)) (self (n - 1))
          | `Sub -> map2 sub (self (n - 1)) (self (n - 1))
          | `Mul -> map2 mul (self (n - 1)) (self (n - 1))
          | `Div -> map2 div (self (n - 1)) (self (n - 1))
          | `Var -> var
          | `Float -> float_)
      5)

let conv qctests = List.map QCheck_alcotest.to_alcotest qctests
