[@@@ocaml.warning "-32"]

open Arith
module Path = Term_indexing.Path

module _ : Index_signature = Index

module Make_shared_test
    (Index : Index_signature)
    (Name : sig
      val name : string
    end) =
struct
  let named s = Name.name ^ "-" ^ s

  let subst_tree_insert_terms =
    Alcotest.test_case (named "subst-tree-insert") `Quick (fun () ->
        let index = Index.create () in
        assert (Index.Internal_for_tests.check_invariants index) ;
        let _ = Index.insert (add (float 1.0) (float 1.0)) 0 index in
        assert (Index.Internal_for_tests.check_invariants index) ;
        let _ = Index.insert (float 1.0) 0 index in
        assert (Index.Internal_for_tests.check_invariants index) ;
        let _ = Index.insert (add (float 1.0) (float 1.0)) 1 index in
        assert (Index.Internal_for_tests.check_invariants index))

  let subst_tree_insert_terms2 =
    Alcotest.test_case (named "subst-tree-insert-terms-2") `Quick (fun () ->
        let index = Index.create () in
        let _ = Index.insert (neg (var 543159235)) 0 index in
        let _ = Index.insert (neg (float ~-.500.0)) 1 index in
        let _ = Index.insert (neg (div (float 42.0) (float 73.))) 2 index in
        let _ = Index.insert (neg (var 543159235)) 3 index in
        Index.iter
          (fun term data ->
            if Term.equal term (neg (var 543159235)) then assert (data = 3)
            else ())
          index)

  module Query_tests = struct
    let collect_unifiable query index =
      let acc = ref [] in
      Index.iter_unifiable (fun term v -> acc := (term, v) :: !acc) index query ;
      !acc

    let collect_unifiable_terms query index =
      collect_unifiable query index |> List.map fst

    let check_alpha_eq_list ~expected ~got =
      if alpha_eq_list expected got then ()
      else
        Alcotest.failf
          "expected: %a@.got: %a @."
          (Fmt.Dump.list Term.pp)
          expected
          (Fmt.Dump.list Term.pp)
          got

    let index_basic =
      Alcotest.test_case (named "index-basic") `Quick (fun () ->
          let index = Index.create () in
          let one = float 1.0 in
          let two = float 2.0 in
          let t0 = add one one in
          let t1 = add one two in
          let t2 = add (mul two two) one in
          Index.insert t0 0 index ;
          Index.insert t1 1 index ;
          Index.insert t2 2 index ;
          assert (Index.Internal_for_tests.check_invariants index) ;
          check_alpha_eq_list
            ~got:(collect_unifiable_terms (add (var 0) (var 1)) index)
            ~expected:[t0; t1; t2] ;
          check_alpha_eq_list
            ~got:(collect_unifiable_terms (add (var 0) one) index)
            ~expected:[t0; t2])

    let index_cant_overwrite =
      Alcotest.test_case (named "index-cant-overwrite") `Quick (fun () ->
          let index = Index.create () in
          let one = float 1.0 in
          let _ = Index.insert (neg (neg (neg one))) 0 index in
          let _ = Index.insert (neg (neg one)) 1 index in
          try ignore (Index.insert (neg (neg (neg one))) 1 index)
          with Invalid_argument _ -> ())

    let index_can_overwrite =
      Alcotest.test_case (named "index-can-overwrite") `Quick (fun () ->
          let index = Index.create () in
          let one = float 1.0 in
          Index.insert (neg (neg (neg one))) 0 index ;
          Index.insert (neg (neg one)) 1 index ;
          let t' = neg (neg (neg one)) in
          Index.insert t' 2 index ;
          match collect_unifiable (neg (neg (neg one))) index with
          | [(t, v)] ->
              if v = 2 && alpha_eq t t' then ()
              else
                Alcotest.failf
                  "expected: %a@.got: %a, %d@."
                  Term.pp
                  t'
                  Term.pp
                  t
                  v
          | _ -> Alcotest.fail "expected one unifiable term")

    let rec mkbintree depth =
      if depth = 0 then float 1.0
      else
        let subtree = mkbintree (depth - 1) in
        add subtree subtree

    let make_generalizations term =
      Term.fold
        (fun _subterm path acc ->
          (path, Term.subst ~term ~path (Fun.const @@ var 0)) :: acc)
        []
        term

    let index_query_generalize =
      Alcotest.test_case (named "index-query-generalize") `Quick (fun () ->
          let index = Index.create () in
          let tree = mkbintree 2 in
          let _ = Index.insert tree 0 index in
          let generalizations = make_generalizations tree in
          (* let generalizations_count = List.length generalizations in *)
          List.iteri
            (fun i (_path, gen) -> Index.insert gen i index)
            generalizations ;
          (* Iterate on all generalizations of (add (var 0) (var 0)).
             We expect to find only a single variable. *)
          Index.iter_generalize
            (fun expr _ ->
              match to_native expr with
              | Var 1 when Name.name = "ref" -> ()
              | Var 0 when Name.name = "eff" -> ()
              | _ ->
                  Alcotest.failf
                    "Expected to find single variable, found %a instead"
                    Term.pp
                    expr)
            index
            (add (var 1) (var 1)) ;
          let query = add (mkbintree 3) (var 0) in
          (* Iterate on all generalizations of [query].
             We expect to find only a single variable or the query itself. *)
          Index.iter_generalize
            (fun expr _ ->
              if not (alpha_eq expr query || Term.is_var expr |> Option.is_some)
              then
                Alcotest.failf
                  "Expected to find full tree or single variable, found %a \
                   instead"
                  Term.pp
                  expr
              else ())
            index
            query)

    let index_query_specialize =
      Alcotest.test_case (named "index-query-specialize") `Quick (fun () ->
          let index = Index.create () in
          let tree = mkbintree 4 in
          let _ = Index.insert tree 0 index in
          let generalizations = make_generalizations tree in
          List.iteri
            (fun i (_path, gen) -> ignore (Index.insert gen i index))
            generalizations ;
          (* Iterate on all specializations of (add (var 0) (var 0)). We expect that the only
             solution found is the full tree. *)
          Index.iter_specialize
            (fun expr _ ->
              if not (Term.equal expr tree) then
                Alcotest.failf
                  "Expected to find full tree, found %a instead"
                  Term.pp
                  expr
              else ())
            index
            (add (var 0) (var 0)) ;
          (* Iterate on all specializations of (add (var 0) (var 0)). We expect that the only
             solution found in the full tree. *)
          let query =
            Term.subst
              ~term:tree
              ~path:
                Path.(at_index 0 (at_index 0 (at_index 0 (at_index 0 root))))
              (Fun.const @@ var 0)
          in
          Index.iter_specialize
            (fun expr _ ->
              if not (Term.equal expr tree || alpha_eq expr query) then
                Alcotest.failf
                  "Expected to find full tree or query, found %a instead"
                  Term.pp
                  expr
              else ())
            index
            query)
  end
end

module Shared_efficient =
  Make_shared_test
    (Index)
    (struct
      let name = "eff"
    end)

module Overlapping_vars_test = struct
  module I = Index

  let internal_to_native internal_term =
    I.reduce
      (fun prim args ->
        match (prim, args) with
        | (Prim.Add, [| lhs; rhs |]) -> Add (lhs, rhs)
        | (Prim.Sub, [| lhs; rhs |]) -> Sub (lhs, rhs)
        | (Prim.Mul, [| lhs; rhs |]) -> Mul (lhs, rhs)
        | (Prim.Div, [| lhs; rhs |]) -> Div (lhs, rhs)
        | (Prim.Neg, [| e |]) -> Neg e
        | (Prim.Float f, [||]) -> Const f
        | _ -> assert false)
      (fun v cycle_opt ->
        match cycle_opt with Some _ -> Cycle v | None -> Var v)
      internal_term

  let collect_unifiable query index =
    let acc = ref [] in
    I.iter_unifiable_transient
      (fun term v ->
        (* if Index.Internal_term.is_cyclic term then () *)
        (* else *)
        acc := (internal_to_native term, v) :: !acc)
      index
      query ;
    !acc

  let collect_unifiable_terms query index = collect_unifiable query index

  let equal_multiset cmp (l1 : (native * int) list) (l2 : (native * int) list) =
    let l1 = List.sort cmp l1 in
    let l2 = List.sort cmp l2 in
    List.equal (fun x y -> cmp x y = 0) l1 l2

  let check ~got ~expected =
    if equal_multiset Stdlib.compare got expected then ()
    else
      Alcotest.failf
        "expected: %a@.got: %a @."
        Fmt.Dump.(list (pair pp_native Fmt.int))
        expected
        Fmt.Dump.(list (pair pp_native Fmt.int))
        got

  let index_overlapping_vars =
    Alcotest.test_case "eff-index-overlapping-vars" `Quick (fun () ->
        let index = I.create () in
        let a = float 1.0 in
        let b = float 2.0 in
        let t0 = add a (var 1) in
        let t1 = add (var 0) b in
        let t2 = var 0 in
        let t3 = add (var 0) (var 0) in
        I.insert t0 0 index ;
        I.insert t1 1 index ;
        I.insert t2 2 index ;
        I.insert t3 3 index ;
        let got = collect_unifiable_terms (var 0) index in
        check
          ~got
          ~expected:
            [ (Add (Const 1.0, Var 1), 0);
              (Add (Var 0, Const 2.0), 1);
              (Var 0, 2);
              (Add (Var 0, Var 0), 3) ] ;
        check
          ~got:(collect_unifiable_terms (add (var 1) (var 1)) index)
          ~expected:
            [ (Add (Const 1.0, Var 1), 0);
              (Add (Var 0, Const 2.0), 1);
              (Var 0, 2);
              (Add (Var 0, Var 0), 3) ])
end

module Test_against_reference (I : Index_signature) = struct
  open QCheck2

  let term_gen canonical_var : Term.t Gen.t =
    let float_ =
      Gen.small_int |> Gen.map (fun i -> float (float_of_int i +. 0.5))
    in
    let try_var path =
      match canonical_var path with
      | None -> float_
      | Some i -> Gen.return (var i)
    in
    let l = Path.at_index 0 in
    let r = Path.at_index 1 in
    let open Gen in
    fix
      (fun self (path, n) ->
        if n = 0 then oneof [try_var path; float_]
        else
          symbol >>= function
          | `Add -> map2 add (self (l path, n - 1)) (self (r path, n - 1))
          | `Sub -> map2 sub (self (l path, n - 1)) (self (r path, n - 1))
          | `Mul -> map2 mul (self (l path, n - 1)) (self (r path, n - 1))
          | `Div -> map2 div (self (l path, n - 1)) (self (r path, n - 1))
          | `Neg -> map neg (self (l path, n - 1))
          | `Var -> small_nat >>= fun i -> return (var i)
          | `Float -> float_)
      (Path.root, 5)

  let gen =
    term_gen (fun path ->
        let hash = Path.hash path in
        Some (hash mod 100))

  let gen_terms = Gen.small_list gen

  let index_collect_unifiable query index =
    let acc = ref [] in
    I.iter_unifiable (fun term v -> acc := (term, v) :: !acc) index query ;
    !acc

  let reference_collect_unifiable query index =
    let acc = ref [] in
    Reference.iter_unifiable
      (fun term v -> acc := (term, v) :: !acc)
      index
      query ;
    !acc

  let count = 100_000

  let unification =
    QCheck2.Test.make
      ~name:"unification"
      ~count
      Gen.(tup2 gen gen_terms)
      (fun (query, terms) ->
        let index = I.create () in
        let baseline_index = Reference.create () in
        List.iteri (fun i t -> I.insert t i index) terms ;
        List.iteri (fun i t -> Reference.insert t i baseline_index) terms ;
        let got = index_collect_unifiable query index |> List.map fst in
        let expected =
          reference_collect_unifiable query baseline_index |> List.map fst
        in
        if not (alpha_eq_list got expected) then
          Test.fail_reportf
            "index:@.@[%a@]@.\n\
             baseline:\n\
             @[%a@]\n\
             query: @[%a@]\n\
             expected: @[%a@]\n\
             got: @[%a@]@."
            (I.pp Fmt.int)
            index
            (Reference.pp Fmt.int)
            baseline_index
            Term.pp
            query
            (Fmt.Dump.list Term.pp)
            expected
            (Fmt.Dump.list Term.pp)
            got
        else true)
    |> QCheck_alcotest.to_alcotest

  let index_collect_generalize query index =
    let acc = ref [] in
    I.iter_generalize (fun term v -> acc := (term, v) :: !acc) index query ;
    !acc

  let reference_collect_generalize query index =
    let acc = ref [] in
    Reference.iter_generalize
      (fun term v -> acc := (term, v) :: !acc)
      index
      query ;
    !acc

  let generalize =
    QCheck2.Test.make
      ~name:"generalize"
      ~count
      Gen.(tup2 gen gen_terms)
      (fun (query, terms) ->
        let index = I.create () in
        let baseline_index = Reference.create () in
        List.iteri (fun i t -> I.insert t i index) terms ;
        List.iteri (fun i t -> Reference.insert t i baseline_index) terms ;
        let got = index_collect_generalize query index |> List.map fst in
        let expected =
          reference_collect_generalize query baseline_index |> List.map fst
        in
        if not (alpha_eq_list got expected) then
          Test.fail_reportf
            "index:@.@[%a@]@.\n\
             baseline:\n\
             @[%a@]\n\
             query: @[%a@]\n\
             expected: @[%a@]\n\
             got: @[%a@]@."
            (I.pp Fmt.int)
            index
            (Reference.pp Fmt.int)
            baseline_index
            Term.pp_sexp
            query
            (Fmt.Dump.list Term.pp_sexp)
            expected
            (Fmt.Dump.list Term.pp_sexp)
            got
        else true)
    |> QCheck_alcotest.to_alcotest

  let index_collect_specialize query index =
    let acc = ref [] in
    I.iter_specialize (fun term v -> acc := (term, v) :: !acc) index query ;
    !acc

  let reference_collect_specialize query index =
    let acc = ref [] in
    Reference.iter_specialize
      (fun term v -> acc := (term, v) :: !acc)
      index
      query ;
    !acc

  let specialize =
    QCheck2.Test.make
      ~name:"specialize"
      ~count
      Gen.(no_shrink (tup2 gen gen_terms))
      (fun (query, terms) ->
        let index = I.create () in
        let baseline_index = Reference.create () in
        List.iteri (fun i t -> I.insert t i index) terms ;
        List.iteri (fun i t -> Reference.insert t i baseline_index) terms ;
        let got = index_collect_specialize query index |> List.map fst in
        let expected =
          reference_collect_specialize query baseline_index |> List.map fst
        in
        if not (alpha_eq_list got expected) then
          Test.fail_reportf
            "index:@.@[%a@]@.\n\
             baseline:\n\
             @[%a@]\n\
             query: @[%a@]\n\
             expected: @[%a@]\n\
             got: @[%a@]@."
            (I.pp Fmt.int)
            index
            (Reference.pp Fmt.int)
            baseline_index
            Term.pp
            query
            (Fmt.Dump.list Term.pp)
            expected
            (Fmt.Dump.list Term.pp)
            got
        else true)
    |> QCheck_alcotest.to_alcotest
end

module Test_against_efficient = Test_against_reference (Index)

module Regression_checks = struct
  let regr1 =
    Alcotest.test_case "regr1_specialize" `Quick (fun () ->
        let keys =
          [ float 0.5;
            mul (float 0.5) (float 0.5);
            mul (sub (float 0.5) (float 0.5)) (float 0.5);
            mul (sub (float 0.5) (float 0.5)) (sub (var 0) (float 0.5)) ]
        in
        let index = Index.create () in
        List.iteri (fun i t -> Index.insert t i index) keys ;
        let query = mul (var 3) (var 3) in
        let acc = ref [] in
        Index.iter_specialize (fun term _ -> acc := term :: !acc) index query ;
        let expected = mul (float 0.5) (float 0.5) in
        match !acc with
        | [t] when Term.equal t expected -> ()
        | got ->
            Format.printf "%a@." (Index.pp Fmt.int) index ;
            Alcotest.failf
              "got: %a, expected: %a"
              (Fmt.Dump.list Term.pp)
              got
              Term.pp
              expected)

  let regr2 =
    Alcotest.test_case "regr2_specialize" `Quick (fun () ->
        let h = float 0.5 in
        let keys =
          [ h;
            div h h;
            div (add h h) h;
            div (div h h) (float 1.5);
            div (div h h) (float 2.5);
            div (div (float 1.5) (float 1.5)) (div (float 1.5) (var 0)) ]
        in

        let index = Index.create () in
        List.iteri (fun i t -> Index.insert t i index) keys ;
        let query = div (var 3) (var 3) in
        let acc = ref [] in
        Index.iter_specialize (fun term _ -> acc := term :: !acc) index query ;
        let expected = div h h in
        match !acc with
        | [t] when Term.equal t expected -> ()
        | got ->
            Format.printf "%a@." (Index.pp Fmt.int) index ;
            Alcotest.failf
              "got: %a, expected: %a"
              (Fmt.Dump.list Term.pp)
              got
              Term.pp
              expected)

  let regr3 =
    Alcotest.test_case "regr3_generalize" `Quick (fun () ->
        let keys =
          [ sub (var 3) (var 3);
            neg (var 5);
            div
              (neg (add (float 0.5) (neg (add (var 18) (var 84)))))
              (float 9.5) ]
        in
        let index = Index.create () in
        List.iteri (fun i t -> Index.insert t i index) keys ;
        let query =
          sub (div (float 8.5) (sub (float 35.5) (neg (float 1.5)))) (var 3)
        in
        let acc = ref [] in
        Index.iter_generalize (fun term _ -> acc := term :: !acc) index query ;
        let got = !acc in
        let expected = [] in
        if alpha_eq_list got expected then ()
        else
          Alcotest.failf
            "got: %a, expected: %a"
            (Fmt.Dump.list Term.pp_sexp)
            got
            (Fmt.Dump.list Term.pp_sexp)
            expected)

  let regr4 =
    Alcotest.test_case "regr4_generalize" `Quick (fun () ->
        let keys =
          [ (float 6.500000, 71);
            (var 9, 75);
            (float 2.500000, 82);
            (float 3.500000, 90);
            (float 7.500000, 8);
            (float 0.500000, 60);
            (var 0, 78);
            (float 5.500000, 96);
            (float 42.500000, 97);
            (float 4.500000, 74);
            (float 1.500000, 43);
            (var 5, 94);
            (float 9.500000, 31);
            (mul (float 6.500000) (float 2.500000), 53);
            (neg (float 0.500000), 88);
            (var 4, 64);
            (var 8, 80);
            (float 24.500000, 83);
            (float 88.500000, 21);
            (var 12, 87);
            (neg (var 4), 41);
            (var 44, 11);
            (neg (var 5), 46);
            (float 28.500000, 42);
            (sub (float 0.500000) (var 8), 67);
            (mul (var 0) (float 8.500000), 14);
            (add (var 4) (float 6.500000), 10);
            (div (var 1) (var 9), 24);
            (var 68, 66);
            (mul (float 2.500000) (var 1), 15);
            (var 2, 13);
            (var 6, 81);
            (var 76, 69);
            ( div
                (mul
                   (add
                      (mul (sub (var 24) (float 49.500000)) (float 4.500000))
                      (sub (div (float 2.500000) (var 84)) (float 25.500000)))
                   (float 3.500000))
                (var 4),
              95 );
            (var 7, 3);
            (mul (sub (var 7) (var 1)) (float 4.500000), 93);
            ( div
                (mul
                   (sub
                      (neg (mul (var 24) (float 1.500000)))
                      (neg (sub (var 18) (float 9.500000))))
                   (div (var 7) (float 70.500000)))
                (float 3.500000),
              92 );
            ( sub
                (neg (float 5.500000))
                (sub
                   (add
                      (neg (add (var 24) (float 6.500000)))
                      (div
                         (add (var 78) (var 9))
                         (mul (float 8.500000) (var 12))))
                   (mul (var 7) (float 90.500000))),
              91 );
            (neg (var 6), 68);
            ( add
                (add
                   (sub
                      (sub
                         (sub (float 45.500000) (float 8.500000))
                         (float 1.500000))
                      (sub (float 13.500000) (neg (var 21))))
                   (float 7.500000))
                (neg (var 6)),
              89 );
            (var 3, 73);
            ( div
                (var 3)
                (neg
                   (mul
                      (add (var 7) (float 1.500000))
                      (mul (mul (float 3.500000) (var 9)) (neg (var 9))))),
              86 );
            ( mul
                (div (var 6) (float 54.500000))
                (div
                   (add
                      (float 4.500000)
                      (sub (neg (var 78)) (div (var 9) (var 12))))
                   (add (var 7) (var 9))),
              85 );
            ( add
                (add
                   (div (var 2) (neg (var 75)))
                   (mul (float 7.500000) (mul (add (var 52) (var 24)) (var 0))))
                (var 28),
              84 );
            (div (float 0.500000) (var 6), 79);
            ( neg
                (div
                   (float 6.500000)
                   (div (neg (div (var 0) (float 70.500000))) (var 70))),
              72 );
            (mul (div (var 7) (float 0.500000)) (float 87.500000), 70);
            (neg (var 59), 65);
            ( mul (float 9.500000) (mul (var 38) (sub (float 0.500000) (var 5))),
              61 );
            ( mul
                (neg (mul (float 1.500000) (mul (float 95.500000) (var 7))))
                (add
                   (float 9.500000)
                   (sub (var 5) (sub (float 2.500000) (float 33.500000)))),
              59 );
            ( mul (sub (var 2) (float 6.500000)) (div (var 36) (float 2.500000)),
              58 );
            (add (var 7) (neg (add (var 0) (var 0))), 57);
            (mul (var 8) (float 32.500000), 56);
            ( div
                (div
                   (float 1.500000)
                   (mul
                      (div
                         (mul (float 70.500000) (float 9.500000))
                         (mul (float 58.500000) (float 6.500000)))
                      (float 7.500000)))
                (float 5.500000),
              55 );
            ( div
                (var 7)
                (mul
                   (add
                      (div (float 90.500000) (mul (var 15) (float 4.500000)))
                      (var 9))
                   (float 8.500000)),
              52 );
            ( div
                (div
                   (mul (var 5) (mul (sub (float 5.500000) (var 84)) (var 58)))
                   (mul (var 8) (var 67)))
                (float 2.500000),
              51 );
            ( div
                (sub
                   (div
                      (var 73)
                      (add (div (var 18) (float 47.500000)) (float 1.500000)))
                   (neg (mul (neg (float 0.500000)) (neg (var 0)))))
                (float 51.500000),
              50 );
            ( add
                (sub
                   (div
                      (sub
                         (add (float 6.500000) (float 8.500000))
                         (add (var 79) (float 21.500000)))
                      (float 58.500000))
                   (var 9))
                (div
                   (var 5)
                   (neg
                      (sub
                         (div (float 0.500000) (float 7.500000))
                         (float 0.500000)))),
              48 );
            (div (var 3) (float 5.500000), 39);
            ( div
                (sub
                   (neg (var 71))
                   (sub
                      (sub (neg (var 0)) (float 5.500000))
                      (mul (var 80) (mul (var 41) (var 38)))))
                (div
                   (div (var 8) (neg (add (float 7.500000) (var 9))))
                   (mul
                      (sub
                         (neg (var 44))
                         (mul (float 7.500000) (float 40.500000)))
                      (add (float 3.500000) (float 1.500000)))),
              37 );
            ( sub
                (var 22)
                (mul
                   (neg
                      (sub
                         (neg (float 62.500000))
                         (sub (var 15) (float 4.500000))))
                   (sub (div (add (var 44) (var 53)) (var 42)) (var 7))),
              35 );
            ( mul
                (neg (var 40))
                (div
                   (add
                      (float 7.500000)
                      (add (var 0) (add (float 46.500000) (var 12))))
                   (mul (neg (sub (var 44) (var 53))) (var 1))),
              34 );
            ( div
                (var 7)
                (div
                   (add
                      (mul
                         (add (float 9.500000) (float 8.500000))
                         (float 7.500000))
                      (mul
                         (sub (float 0.500000) (float 0.500000))
                         (neg (var 9))))
                   (var 0)),
              33 );
            ( mul
                (sub
                   (add
                      (add (add (var 24) (float 90.500000)) (float 4.500000))
                      (var 2))
                   (float 8.500000))
                (sub
                   (add
                      (div
                         (float 1.500000)
                         (add (float 9.500000) (float 2.500000)))
                      (var 7))
                   (var 9)),
              32 );
            ( sub
                (var 54)
                (add
                   (div
                      (mul (neg (var 24)) (neg (float 5.500000)))
                      (div (var 6) (float 7.500000)))
                   (float 0.500000)),
              30 );
            ( add
                (sub (neg (sub (var 2) (float 4.500000))) (float 7.500000))
                (float 81.500000),
              27 );
            ( sub
                (neg
                   (mul (var 1) (sub (mul (float 5.500000) (var 84)) (var 92))))
                (sub (float 81.500000) (var 8)),
              26 );
            (sub (var 9) (div (neg (mul (var 2) (var 5))) (var 5)), 22);
            ( div
                (float 1.500000)
                (mul
                   (div (float 2.500000) (add (var 6) (float 6.500000)))
                   (add (float 48.500000) (var 96))),
              20 );
            (sub (var 86) (sub (var 8) (var 3)), 12);
            ( mul
                (mul
                   (float 2.500000)
                   (sub
                      (mul (add (var 0) (var 91)) (float 9.500000))
                      (neg (div (float 7.500000) (var 24)))))
                (float 3.500000),
              6 );
            (neg (sub (var 7) (var 2)), 5);
            ( div
                (neg (mul (float 3.500000) (float 1.500000)))
                (sub
                   (add (sub (var 9) (float 5.500000)) (float 82.500000))
                   (var 0)),
              0 ) ]
          |> List.map fst
        in
        let index = Index.create () in
        List.iteri (fun i t -> Index.insert t i index) keys ;
        let query = sub (var 2) (var 9) in
        let acc = ref [] in
        Index.iter_generalize (fun term _ -> acc := term :: !acc) index query ;
        let got = !acc in
        let expected =
          [ var 0;
            var 2;
            var 3;
            var 4;
            var 5;
            var 6;
            var 7;
            var 8;
            var 9;
            var 76;
            var 68;
            var 44;
            var 12 ]
        in
        if alpha_eq_list got expected then ()
        else (
          Format.eprintf
            "got: %a@.expected: %a@."
            (Fmt.Dump.list Term.pp_sexp)
            got
            (Fmt.Dump.list Term.pp_sexp)
            expected ;
          let (left, right) = alpha_eq_list_diff got expected in
          Alcotest.failf
            "shouldn't have: %a@.should have: %a@."
            (Fmt.Dump.list Term.pp_sexp)
            left
            (Fmt.Dump.list Term.pp_sexp)
            right))

  let regr5 =
    Alcotest.test_case "regr5_generalize" `Quick (fun () ->
        let keys = [var 0] in
        let index = Index.create () in
        List.iteri (fun i t -> Index.insert t i index) keys ;
        let query = add (float 1.0) (var 0) in
        let acc = ref [] in
        Index.iter_generalize (fun term _ -> acc := term :: !acc) index query ;
        let got = !acc in
        let expected = [var 0] in
        if alpha_eq_list got expected then ()
        else (
          Format.eprintf
            "got: %a@.expected: %a@."
            (Fmt.Dump.list Term.pp_sexp)
            got
            (Fmt.Dump.list Term.pp_sexp)
            expected ;
          let (left, right) = alpha_eq_list_diff got expected in
          Alcotest.failf
            "shouldn't have: %a@.should have: %a@."
            (Fmt.Dump.list Term.pp_sexp)
            left
            (Fmt.Dump.list Term.pp_sexp)
            right))

  let regr6 =
    Alcotest.test_case "regr6_generalize" `Quick (fun () ->
        let keys = [sub (var 3) (mul (var 0) (var 3))] in
        let index = Index.create () in
        List.iteri (fun i t -> Index.insert t i index) keys ;
        let query = sub (var 3) (mul (float 0.5) (float 0.5)) in
        let acc = ref [] in
        Index.iter_generalize (fun term _ -> acc := term :: !acc) index query ;
        let got = !acc in
        let expected = [] in
        if alpha_eq_list got expected then ()
        else (
          Format.eprintf
            "got: %a@.expected: %a@."
            (Fmt.Dump.list Term.pp_sexp)
            got
            (Fmt.Dump.list Term.pp_sexp)
            expected ;
          let (left, right) = alpha_eq_list_diff got expected in
          Alcotest.failf
            "shouldn't have: %a@.should have: %a@."
            (Fmt.Dump.list Term.pp_sexp)
            left
            (Fmt.Dump.list Term.pp_sexp)
            right))

  let regr7 =
    Alcotest.test_case "regr7_unification" `Quick (fun () ->
        let keys = [mul (var 5) (sub (float 0.5) (float 1.5))] in
        let index = Index.create () in
        List.iteri (fun i t -> Index.insert t i index) keys ;
        let query = mul (var 0) (sub (var 5) (var 0)) in
        let acc = ref [] in
        Index.iter_unifiable (fun term _ -> acc := term :: !acc) index query ;
        let got = !acc in
        let expected = [] in
        if alpha_eq_list got expected then ()
        else (
          Format.eprintf
            "got: %a@.expected: %a@."
            (Fmt.Dump.list Term.pp_sexp)
            got
            (Fmt.Dump.list Term.pp_sexp)
            expected ;
          let (left, right) = alpha_eq_list_diff got expected in
          Alcotest.failf
            "shouldn't have: %a@.should have: %a@."
            (Fmt.Dump.list Term.pp_sexp)
            left
            (Fmt.Dump.list Term.pp_sexp)
            right))

  let regr8 =
    Alcotest.test_case "regr8_generalize" `Quick (fun () ->
        let keys = [add (var 0) (var 0)] in
        let index = Index.create () in
        List.iteri (fun i t -> Index.insert t i index) keys ;
        let query = add (float 1.0) (var 0) in
        let acc = ref [] in
        Index.iter_generalize_transient
          (fun term _ ->
            let subst = Index.get_subst term in
            acc := (Index.to_term term, subst) :: !acc)
          index
          query ;
        let got = !acc in
        let expected = [] in
        if alpha_eq_list (List.map fst got) expected then ()
        else (
          Format.eprintf
            "got: %a@.expected: %a@."
            (Fmt.Dump.list (Fmt.Dump.pair Term.pp_sexp Subst.pp))
            got
            (Fmt.Dump.list Term.pp_sexp)
            expected ;
          let (left, right) = alpha_eq_list_diff (List.map fst got) expected in
          Alcotest.failf
            "shouldn't have: %a@.should have: %a@."
            (Fmt.Dump.list Term.pp_sexp)
            left
            (Fmt.Dump.list Term.pp_sexp)
            right))

  let regr9 =
    Alcotest.test_case "regr9_generalize" `Quick (fun () ->
        let keys = [add (var 0) (var 1)] in
        let index = Index.create () in
        List.iteri (fun i t -> Index.insert t i index) keys ;
        let query = add (var 1) (var 0) in
        let acc = ref [] in
        Index.iter_generalize_transient
          (fun term _ ->
            let subst = Index.get_subst term in
            acc := (Index.to_term term, subst) :: !acc)
          index
          query ;
        let got = !acc in
        let expected = [add (var 0) (var 1)] in
        if alpha_eq_list (List.map fst got) expected then ()
        else (
          Format.eprintf
            "got: %a@.expected: %a@."
            (Fmt.Dump.list (Fmt.Dump.pair Term.pp_sexp Subst.pp))
            got
            (Fmt.Dump.list Term.pp_sexp)
            expected ;
          let (left, right) = alpha_eq_list_diff (List.map fst got) expected in
          Alcotest.failf
            "shouldn't have: %a@.should have: %a@."
            (Fmt.Dump.list Term.pp_sexp)
            left
            (Fmt.Dump.list Term.pp_sexp)
            right))

  let regr10 =
    Alcotest.test_case "regr10_specialize" `Quick (fun () ->
        let keys = [(mul (neg (var 1)) (neg (var 1)), 79)] |> List.map fst in
        let index = Index.create () in
        List.iteri (fun i t -> Index.insert t i index) keys ;
        let query = mul (var 5) (var 5) in
        let acc = ref [] in
        Index.iter_specialize (fun term _ -> acc := term :: !acc) index query ;
        let expected = mul (neg (var 1)) (neg (var 1)) in
        match !acc with
        | [t] when Term.equal t expected -> ()
        | got ->
            Format.printf "@.%a@." (Index.pp Fmt.int) index ;
            Alcotest.failf
              "got: %a, expected: %a"
              (Fmt.Dump.list Term.pp)
              got
              Term.pp
              expected)
end

let () =
  Alcotest.run
    "index"
    [ ( "subst-tree",
        [ Shared_efficient.subst_tree_insert_terms;
          Shared_efficient.subst_tree_insert_terms2 ] );
      ( "index-basic-eff",
        Shared_efficient.Query_tests.
          [ index_basic;
            index_cant_overwrite;
            index_query_generalize;
            index_query_specialize;
            Overlapping_vars_test.index_overlapping_vars ] );
      ( "regressions",
        Regression_checks.
          [regr1; regr2; regr3; regr5; regr4; regr6; regr7; regr8; regr9; regr10]
      );
      ( "test-against-reference",
        Test_against_efficient.[unification; generalize; specialize] ) ]
