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

let rewrite_at term path =
  let target = Expr.get_subterm term path in
  Format.printf "%a@." Expr.pp target ;
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

let basic_rewrite =
  Alcotest.test_case "basic_rewrite" `Quick (fun () ->
      let add_pattern =
        let open Patt in
        prim Prim.Add list_any
      in
      let pattern =
        let open Patt in
        prim Prim.Mul (any @. add_pattern @. list_empty)
      in
      (* Matches are produced in a depth-first fashion, hence matches
         closer to the root are closer to the beginning of the list of
         matches. *)
      let matches = Patt.all_matches [pattern] expression in
      let expected =
        Path.
          [ at_index 0 (at_index 1 (at_index 1 root));
            at_index 0 (at_index 1 root);
            at_index 0 root ]
      in
      let () =
        if List.equal Path.equal matches expected then ()
        else
          Alcotest.failf
            "all_matches %a: expected %a, got %a@."
            Patt.pp
            pattern
            (Fmt.Dump.list Path.pp)
            expected
            (Fmt.Dump.list Path.pp)
            matches
      in
      (* Rewrite deeper matches first *)
      let rewritten =
        List.fold_right (fun path acc -> rewrite_at acc path) matches expression
      in
      let target =
        let subexpr = add (mul (float 2.) (var 0)) (mul (float 2.) (var 1)) in
        sub subexpr (div subexpr (div subexpr (var 2)))
      in
      (* Thanks to hash-consing, structural equality is physical equality *)
      if target.tag = rewritten.tag then ()
      else
        Alcotest.failf
          "rewrite_at %a %a: expected %a, got %a@."
          (Fmt.Dump.list Path.pp)
          matches
          Expr.pp
          expression
          Expr.pp
          target
          Expr.pp
          rewritten)

(* -------------------- *)

let focused_rewrite =
  Alcotest.test_case "focused_rewrite" `Quick (fun () ->
      let mul_pattern =
        let open Patt in
        prim Prim.Mul list_any
      in
      let pattern =
        let open Patt in
        prim Prim.Div (focus mul_pattern @. any @. list_empty)
      in
      (* Matches are produced in a depth-first fashion, hence matches
         closer to the root are closer to the beginning of the list of
         matches. *)
      let first_matches = Patt.first_match [pattern] expression in
      let matches = Patt.all_matches [pattern] expression in
      let () =
        let expected =
          Path.
            [ at_index 0 (at_index 1 root);
              at_index 0 (at_index 1 (at_index 1 root)) ]
        in
        if List.equal Path.equal matches expected then ()
        else
          Alcotest.failf
            "all_matches %a: expected %a, got %a@."
            Patt.pp
            pattern
            (Fmt.Dump.list Path.pp)
            expected
            (Fmt.Dump.list Path.pp)
            matches
      in
      let () =
        (* Only one focused subterm in the pattern so only one element in the result list *)
        let expected = Path.[at_index 0 (at_index 1 (at_index 1 root))] in
        if List.equal Path.equal first_matches expected then ()
        else
          Alcotest.failf
            "first_matches %a: expected %a, got %a@."
            Patt.pp
            pattern
            (Fmt.Dump.list Path.pp)
            expected
            (Fmt.Dump.list Path.pp)
            first_matches
      in
      (* Rewrite deeper matches first *)
      let rewritten =
        List.fold_right (fun path acc -> rewrite_at acc path) matches expression
      in
      let target =
        let subexpr = add (mul (float 2.) (var 0)) (mul (float 2.) (var 1)) in
        sub
          (mul (float 2.) (add (var 0) (var 1)))
          (div subexpr (div subexpr (var 2)))
      in
      (* Thanks to hash-consing, structural equality is physical equality *)
      if target.tag = rewritten.tag then ()
      else
        Alcotest.failf
          "rewrite_at %a %a: expected@.%a@.got@.%a@."
          (Fmt.Dump.list Path.pp)
          matches
          Expr.pp
          expression
          Expr.pp
          target
          Expr.pp
          rewritten)

let () =
  Alcotest.run
    "rewriting"
    [("basic", [basic_rewrite]); ("focus", [focused_rewrite])]
