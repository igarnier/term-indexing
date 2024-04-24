open Lib_rewriting
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
      (Prim.Mul, [| something; { node = Prim (Prim.Add, [| lhs; rhs |]); _ } |])
    ->
      let replacement = add (mul something lhs) (mul something rhs) in
      Expr.subst ~term ~path ~replacement
  | _ -> assert false

(* -------------------- *)

let expression =
  let subexpr = mul (float 2.) (add (var 0) (var 1)) in
  sub subexpr (div subexpr (div subexpr (var 2)))

let () = Format.eprintf "%a@." pp_native (to_native expression)

(* Matches are produced in a depth-first fashion, hence matches
   closer to the root are closer to the beginning of the list of
   matches. *)
let matches = Patt.all_matches pattern expression

let () =
  List.iter (fun path -> Format.printf "%s@." (Path.to_string path)) matches

(* Rewrite deeper matches first *)
let rewritten =
  List.fold_right (fun path acc -> rewrite_at acc path) matches expression

let target =
  let subexpr = add (mul (float 2.) (var 0)) (mul (float 2.) (var 1)) in
  sub subexpr (div subexpr (div subexpr (var 2)))

let () = Format.eprintf "%a@." pp_native (to_native rewritten)

(* Thanks to hash-consing, structural equality is physical equality *)
let () = assert (target.tag = rewritten.tag)
