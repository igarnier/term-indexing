open Arith

(* -------------------- *)

let add x y = Term.prim Add [| x; y |]

let sub x y = Term.prim Sub [| x; y |]

let mul x y = Term.prim Mul [| x; y |]

let div x y = Term.prim Div [| x; y |]

let float f = Term.prim (Prim.Float f) [||]

let var s = Term.var s

(* -------------------- *)

let rewrite_at term path =
  let target = Term.get_subterm term path in
  Term.destruct
    (fun prim subterms ->
      match (prim, subterms) with
      | (Prim.Mul, [| something; add_term |]) ->
          Term.destruct
            (fun prim subterms ->
              match (prim, subterms) with
              | (Prim.Add, [| lhs; rhs |]) ->
                  let replacement =
                    add (mul something lhs) (mul something rhs)
                  in
                  Term.subst ~term ~path (Fun.const replacement)
              | _ -> assert false)
            (fun _ -> assert false)
            add_term
      | _ -> assert false)
    (fun _ -> assert false)
    target

(* -------------------- *)

let expression =
  let subexpr = mul (float 2.) (add (var 0) (var 1)) in
  sub subexpr (div subexpr (div subexpr (var 2)))

let basic_rewrite =
  Alcotest.test_case "basic_rewrite" `Quick (fun () ->
      let add_pattern =
        let open Pattern in
        prim Prim.Add list_any
      in
      let pattern =
        let open Pattern in
        prim Prim.Mul (any @. add_pattern @. list_empty)
      in
      (* Matches are produced in a depth-first fashion, hence matches
         closer to the root are closer to the beginning of the list of
         matches. *)
      let matches =
        Pattern.all_matches [pattern] expression |> List.map Zipper.path
      in
      let expected = [[1; 1; 0]; [1; 0]; [0]] in
      let () =
        if List.equal (List.equal Int.equal) matches expected then ()
        else
          Alcotest.failf
            "all_matches %a: expected %a, got %a@."
            Pattern.pp
            pattern
            Fmt.Dump.(list (list Fmt.int))
            expected
            Fmt.Dump.(list (list Fmt.int))
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
      if Term.equal target rewritten then ()
      else
        Alcotest.failf
          "rewrite_at %a %a: expected %a, got %a@."
          Fmt.Dump.(list (list Fmt.int))
          matches
          Term.pp
          expression
          Term.pp
          target
          Term.pp
          rewritten)

(* -------------------- *)

let focused_rewrite =
  Alcotest.test_case "focused_rewrite" `Quick (fun () ->
      let mul_pattern =
        let open Pattern in
        prim Prim.Mul list_any
      in
      let pattern =
        let open Pattern in
        prim Prim.Div (focus mul_pattern @. any @. list_empty)
      in
      (* Matches are produced in a depth-first fashion, hence matches
         closer to the root are closer to the beginning of the list of
         matches. *)
      let first_matches =
        Pattern.first_match [pattern] expression |> List.map Zipper.path
      in
      let matches =
        Pattern.all_matches [pattern] expression |> List.map Zipper.path
      in
      let () =
        let expected = [[1; 0]; [1; 1; 0]] in
        if List.equal (List.equal Int.equal) matches expected then ()
        else
          Alcotest.failf
            "all_matches %a: expected %a, got %a@."
            Pattern.pp
            pattern
            Fmt.Dump.(list (list Fmt.int))
            expected
            Fmt.Dump.(list (list Fmt.int))
            matches
      in
      let () =
        (* Only one focused subterm in the pattern so only one element in the result list *)
        let expected = [[1; 1; 0]] in
        if List.equal (List.equal Int.equal) first_matches expected then ()
        else
          Alcotest.failf
            "first_matches %a: expected %a, got %a@."
            Pattern.pp
            pattern
            Fmt.Dump.(list (list Fmt.int))
            expected
            Fmt.Dump.(list (list Fmt.int))
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
      if Term.equal target rewritten then ()
      else
        Alcotest.failf
          "rewrite_at %a %a: expected@.%a@.got@.%a@."
          Fmt.Dump.(list (list Fmt.int))
          matches
          Term.pp
          expression
          Term.pp
          target
          Term.pp
          rewritten)

let () =
  Alcotest.run
    "rewriting"
    [("basic", [basic_rewrite]); ("focus", [focused_rewrite])]
