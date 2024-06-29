[@@@ocaml.warning "-32"]

open Arith
module Path = Term_indexing.Path

module Mscg_tests = struct
  let diag_idempotent =
    QCheck2.Test.make
      ~name:"mscg-diag-idempotent"
      ~print:(fun term -> Format.asprintf "%a" Expr.pp term)
      ~count:100
      Arith.gen
      (fun term ->
        let (res, _, _) = Index_raw.Internal_for_tests.mscg term term in
        Expr.equal term res)
    |> QCheck_alcotest.to_alcotest

  let diag_commutative =
    QCheck2.Test.make
      ~name:"mscg-diag-commutative"
      ~print:(fun (term1, term2) ->
        Format.asprintf "%a, %a" Expr.pp term1 Expr.pp term2)
      ~count:100
      (QCheck2.Gen.pair Arith.gen Arith.gen)
      (fun (term1, term2) ->
        let (res1, _, _) = Index_raw.Internal_for_tests.mscg term1 term2 in
        let (res2, _, _) = Index_raw.Internal_for_tests.mscg term2 term1 in
        Expr.equal res1 res2)
    |> QCheck_alcotest.to_alcotest

  let mscg_case0 =
    Alcotest.test_case "mscg-case0" `Quick (fun () ->
        let term1 = add (mul (var 1) (var 5)) (var 9) in
        let term2 = add (div (var 1) (var 5)) (var 9) in
        let (res, _, _) = Index_raw.Internal_for_tests.mscg term1 term2 in
        match to_native res with
        | Add (Var 0, Var 9) -> ()
        | _ -> Alcotest.fail "mscg-case0")

  let mscg_case1 =
    Alcotest.test_case "mscg-case1" `Quick (fun () ->
        let term1 = add (mul (var 1) (var 5)) (var 9) in
        let term2 = mul (mul (var 1) (var 5)) (var 9) in
        let (res, _, _) = Index_raw.Internal_for_tests.mscg term1 term2 in
        match to_native res with Var 0 -> () | _ -> Alcotest.fail "mscg-case1")

  let mscg_case2 =
    Alcotest.test_case "mscg-case2" `Quick (fun () ->
        let term1 = add (mul (var 1) (var 5)) (var 9) in
        let term2 = add (div (var 1) (var 5)) (div (var 1) (var 5)) in
        let (res, residual1, residual2) =
          Index_raw.Internal_for_tests.mscg term1 term2
        in
        match to_native res with
        | Add (Var 0, Var 4) -> (
            let lexpr1 = Subst.eval_exn 0 residual1 in
            let rexpr1 = Subst.eval_exn 0 residual2 in
            let lexpr2 = Subst.eval_exn 4 residual1 in
            let rexpr2 = Subst.eval_exn 4 residual2 in
            (match (to_native lexpr1, to_native rexpr1) with
            | (Mul (Var 1, Var 5), Div (Var 1, Var 5)) -> ()
            | _ -> Alcotest.fail "mscg-case2: wrong subterm") ;
            match (to_native lexpr2, to_native rexpr2) with
            | (Var 9, Div (Var 1, Var 5)) -> ()
            | _ -> Alcotest.fail "mscg-case2: wrong subterm")
        | _ -> Alcotest.fail "mscg-case2: wrong result")

  let mkgen ?(start = 0) () =
    let c = ref start in
    fun () ->
      let v = !c in
      incr c ;
      Index_raw.Internal_for_tests.indicator v

  let mscg_nofail =
    QCheck2.Test.make
      ~name:"mscg-subst-nofail"
      ~count:1000
      (QCheck2.Gen.pair Arith.subst_gen Arith.subst_gen)
      (fun (subst1, subst2) ->
        try
          ignore
            (Index_raw.Internal_for_tests.mscg_subst
               subst1
               subst2
               (mkgen ~start:(-1000) ())) ;
          true
        with _ -> false)
    |> QCheck_alcotest.to_alcotest

  let mscg_disjoint_support_empty =
    QCheck2.Test.make
      ~name:"mscg-disjoint-support-empty"
      ~count:1000
      Arith.subst_gen
      (fun subst ->
        let subst' =
          let pairs = Subst.to_seq subst |> List.of_seq in
          let len = List.length pairs in
          List.map
            (fun (i, t) -> (i + Index_raw.Internal_for_tests.indicator len, t))
            pairs
          |> List.to_seq |> Subst.of_seq
        in
        let (result, _, _) =
          Index_raw.Internal_for_tests.mscg_subst
            subst
            subst'
            (mkgen ~start:1000 ())
        in
        Subst.is_empty result)
    |> QCheck_alcotest.to_alcotest

  let mscg_subst =
    Alcotest.test_case "mscg-subst-example" `Quick (fun () ->
        (*
         Example drawn from the handbook of automated reasoning
         let sigma1 = *1 = g(a), *2 = f(c, x1), *3 = g(c)
         let sigma2 = *1 = g(b), *2 = x1, *3 = g(x2)
         let rho = *1 = g( *4 ), *3 = g(x5)
         let sigma1/rho = *2 = f(c, x1), *4 = a, *5 = c
         let sigma2/rho = *2 = x1, *4 = b, *5 = x2
       *)
        let a = Arith.float 1.0 in
        let b = Arith.float 2.0 in
        let c = Arith.float 3.0 in
        let x1 = var 1 in
        let x2 = var 2 in
        let subst1 =
          [ (Index_raw.Internal_for_tests.indicator 1, neg a);
            (Index_raw.Internal_for_tests.indicator 2, add c x1);
            (Index_raw.Internal_for_tests.indicator 3, neg c) ]
          |> List.to_seq |> Subst.of_seq
        in
        let subst2 =
          [ (Index_raw.Internal_for_tests.indicator 1, neg b);
            (Index_raw.Internal_for_tests.indicator 2, x1);
            (Index_raw.Internal_for_tests.indicator 3, neg x2) ]
          |> List.to_seq |> Subst.of_seq
        in
        let (mscg, _residual1, _residual2) =
          Index_raw.Internal_for_tests.mscg_subst
            subst1
            subst2
            (mkgen ~start:4 ())
        in
        let assert_eq_subst map k v =
          match Subst.eval k map with
          | None ->
              Alcotest.failf "mscg-subst: %d not found in %a@." k Subst.pp map
          | Some v' ->
              if Expr.equal v v' then ()
              else
                Alcotest.failf
                  "mscg-subst: at %d: expected %a, found %a@."
                  k
                  Expr.pp
                  v
                  Expr.pp
                  v'
        in
        assert_eq_subst
          mscg
          (Index_raw.Internal_for_tests.indicator 1)
          (neg (var (Index_raw.Internal_for_tests.indicator 4))) ;
        assert_eq_subst
          mscg
          (Index_raw.Internal_for_tests.indicator 3)
          (neg (var (Index_raw.Internal_for_tests.indicator 5))))
end

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
            if Expr.equal term (neg (var 543159235)) then assert (data = 3)
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
          (Fmt.Dump.list Expr.pp)
          expected
          (Fmt.Dump.list Expr.pp)
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
                  Expr.pp
                  t'
                  Expr.pp
                  t
                  v
          | _ -> Alcotest.fail "expected one unifiable term")

    let rec mkbintree depth =
      if depth = 0 then float 1.0
      else
        let subtree = mkbintree (depth - 1) in
        add subtree subtree

    let make_generalizations term =
      Expr.fold
        (fun _subterm path acc ->
          (path, Expr.subst ~term ~path (Fun.const @@ var 0)) :: acc)
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
                    Expr.pp
                    expr)
            index
            (add (var 1) (var 1)) ;
          let query = add (mkbintree 3) (var 0) in
          (* Iterate on all generalizations of [query].
             We expect to find only a single variable or the query itself. *)
          Index.iter_generalize
            (fun expr _ ->
              if not (alpha_eq expr query || Expr.is_var expr |> Option.is_some)
              then
                Alcotest.failf
                  "Expected to find full tree or single variable, found %a \
                   instead"
                  Expr.pp
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
              if not (Expr.equal expr tree) then
                Alcotest.failf
                  "Expected to find full tree, found %a instead"
                  Expr.pp
                  expr
              else ())
            index
            (add (var 0) (var 0)) ;
          (* Iterate on all specializations of (add (var 0) (var 0)). We expect that the only
             solution found in the full tree. *)
          let query =
            Expr.subst
              ~term:tree
              ~path:
                Path.(at_index 0 (at_index 0 (at_index 0 (at_index 0 root))))
              (Fun.const @@ var 0)
          in
          Index.iter_specialize
            (fun expr _ ->
              if not (Expr.equal expr tree || alpha_eq expr query) then
                Alcotest.failf
                  "Expected to find full tree or query, found %a instead"
                  Expr.pp
                  expr
              else ())
            index
            query)
  end
end

module Shared_reference =
  Make_shared_test
    (Index)
    (struct
      let name = "ref"
    end)

module Shared_efficient =
  Make_shared_test
    (Index2)
    (struct
      let name = "eff"
    end)

module Overlapping_vars_test = struct
  module I = Index2_raw

  let internal_to_native internal_term =
    I.map
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
    I.iter_unifiable
      (fun term v ->
        (* if Index2.Internal_term.is_cyclic term then () *)
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

  let term_gen canonical_var : Expr.t Gen.t =
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

  let gen_terms = Gen.list gen

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

  let unification =
    QCheck2.Test.make
      ~name:"unification"
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
            Expr.pp
            query
            (Fmt.Dump.list Expr.pp)
            expected
            (Fmt.Dump.list Expr.pp)
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
            Expr.pp
            query
            (Fmt.Dump.list Expr.pp)
            expected
            (Fmt.Dump.list Expr.pp)
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
      Gen.(tup2 gen gen_terms)
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
            Expr.pp
            query
            (Fmt.Dump.list Expr.pp)
            expected
            (Fmt.Dump.list Expr.pp)
            got
        else true)
    |> QCheck_alcotest.to_alcotest
end

module Test_against_efficient = Test_against_reference (Index2)

let () =
  Alcotest.run
    "index"
    [ ("mscg-properties", Mscg_tests.[diag_idempotent; diag_commutative]);
      ("mscg-cases", Mscg_tests.[mscg_case0; mscg_case1; mscg_case2]);
      ( "mscg-subst",
        Mscg_tests.[mscg_nofail; mscg_disjoint_support_empty; mscg_subst] );
      ( "subst-tree",
        [ Shared_reference.subst_tree_insert_terms;
          Shared_reference.subst_tree_insert_terms2;
          Shared_efficient.subst_tree_insert_terms;
          Shared_efficient.subst_tree_insert_terms2 ] );
      ( "index-basic-ref",
        Shared_reference.Query_tests.
          [ index_basic;
            index_cant_overwrite;
            index_query_generalize;
            index_query_specialize ] );
      ( "index-basic-eff",
        Shared_efficient.Query_tests.
          [ index_basic;
            index_cant_overwrite;
            index_query_generalize;
            index_query_specialize;
            Overlapping_vars_test.index_overlapping_vars ] );
      ( "test-against-reference",
        Test_against_efficient.[unification; generalize; specialize] ) ]
