open Term_indexing
open Arith

(* -------------------- *)

module Patt = Pattern.Make_with_hash_consing (Prim) (Expr)

let add x y = Expr.prim Add [| x; y |]

let sub x y = Expr.prim Sub [| x; y |]

let mul x y = Expr.prim Mul [| x; y |]

let div x y = Expr.prim Div [| x; y |]

let float f = Expr.prim (Prim.Float f) [||]

let var s = Expr.var s

(* -------------------- *)

let add_pattern =
  let open Patt in
  prim Prim.Add list_any

let pattern =
  let open Patt in
  focus @@ prim Prim.Mul (any @. add_pattern @. list_empty)

let rewrite_at term path =
  let target = Expr.get_subterm term path in
  match target.Hashcons.node with
  | Prim
      ( Prim.Mul,
        [| something; { node = Prim (Prim.Add, [| lhs; rhs |], _); _ } |],
        _ ) ->
      let replacement = add (mul something lhs) (mul something rhs) in
      Expr.subst ~term ~path (Fun.const replacement)
  | _ -> assert false

(* -------------------- *)

let expression =
  let subexpr = mul (float 2.) (add (var 0) (var 1)) in
  sub subexpr (div subexpr (div subexpr (var 2)))

let assert_eq got expected =
  if not (String.equal got expected) then
    Format.kasprintf failwith "Got: %s\nExpected: %s\n%!" got expected
  else ()

let () =
  assert_eq
    (Format.asprintf "%a" pp_native (to_native expression))
    "((2.000000 * (0 + 1)) - ((2.000000 * (0 + 1)) / ((2.000000 * (0 + 1)) / \
     2)))"

(* Matches are produced in a depth-first fashion, hence matches
   closer to the root are closer to the beginning of the list of
   matches. *)
let matches = Patt.all_matches [pattern] expression

let () =
  match List.map Path.to_string matches with
  | ["0 -> *"; "0 -> 1 -> *"; "0 -> 1 -> 1 -> *"] -> ()
  | _ -> assert false

(* Rewrite deeper matches first *)
let rewritten =
  List.fold_right (fun path acc -> rewrite_at acc path) matches expression

let target =
  let subexpr = add (mul (float 2.) (var 0)) (mul (float 2.) (var 1)) in
  sub subexpr (div subexpr (div subexpr (var 2)))

let () =
  assert_eq
    (Format.asprintf "%a" pp_native (to_native rewritten))
    "(((2.000000 * 0) + (2.000000 * 1)) - (((2.000000 * 0) + (2.000000 * 1)) / \n\
    \                                     (((2.000000 * 0) + (2.000000 * 1)) / \n\
    \                                     2)))"

(* Thanks to hash-consing, structural equality is physical equality *)
let () = assert (target.tag = rewritten.tag)
