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
        let (res, _, _) = Index.Internal_for_tests.mscg term term in
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
        let (res1, _, _) = Index.Internal_for_tests.mscg term1 term2 in
        let (res2, _, _) = Index.Internal_for_tests.mscg term2 term1 in
        Expr.equal res1 res2)
    |> QCheck_alcotest.to_alcotest

  let mscg_case0 =
    Alcotest.test_case "mscg-case0" `Quick (fun () ->
        let term1 = add (mul (var 1) (var 5)) (var 9) in
        let term2 = add (div (var 1) (var 5)) (var 9) in
        let (res, _, _) = Index.Internal_for_tests.mscg term1 term2 in
        match to_native res with
        | Add (Var 0, Var 9) -> ()
        | _ -> Alcotest.fail "mscg-case0")

  let mscg_case1 =
    Alcotest.test_case "mscg-case1" `Quick (fun () ->
        let term1 = add (mul (var 1) (var 5)) (var 9) in
        let term2 = mul (mul (var 1) (var 5)) (var 9) in
        let (res, _, _) = Index.Internal_for_tests.mscg term1 term2 in
        match to_native res with Var 0 -> () | _ -> Alcotest.fail "mscg-case1")

  let mscg_case2 =
    Alcotest.test_case "mscg-case2" `Quick (fun () ->
        let term1 = add (mul (var 1) (var 5)) (var 9) in
        let term2 = add (div (var 1) (var 5)) (div (var 1) (var 5)) in
        let (res, residual1, residual2) =
          Index.Internal_for_tests.mscg term1 term2
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
      Index.Internal_for_tests.indicator v

  let mscg_nofail =
    QCheck2.Test.make
      ~name:"mscg-subst-nofail"
      ~count:1000
      (QCheck2.Gen.pair Arith.subst_gen Arith.subst_gen)
      (fun (subst1, subst2) ->
        try
          ignore
            (Index.Internal_for_tests.mscg_subst
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
            (fun (i, t) -> (i + Index.Internal_for_tests.indicator len, t))
            pairs
          |> List.to_seq |> Subst.of_seq
        in
        let (result, _, _) =
          Index.Internal_for_tests.mscg_subst
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
          [ (Index.Internal_for_tests.indicator 1, neg a);
            (Index.Internal_for_tests.indicator 2, add c x1);
            (Index.Internal_for_tests.indicator 3, neg c) ]
          |> List.to_seq |> Subst.of_seq
        in
        let subst2 =
          [ (Index.Internal_for_tests.indicator 1, neg b);
            (Index.Internal_for_tests.indicator 2, x1);
            (Index.Internal_for_tests.indicator 3, neg x2) ]
          |> List.to_seq |> Subst.of_seq
        in
        let (mscg, _residual1, _residual2) =
          Index.Internal_for_tests.mscg_subst subst1 subst2 (mkgen ~start:4 ())
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
          (Index.Internal_for_tests.indicator 1)
          (neg (var (Index.Internal_for_tests.indicator 4))) ;
        assert_eq_subst
          mscg
          (Index.Internal_for_tests.indicator 3)
          (neg (var (Index.Internal_for_tests.indicator 5))))
end

module Make_shared_test (Index : sig
  type 'a t

  type term = Arith.Expr.t

  val name : string

  val create : unit -> 'a t

  val insert : term -> 'a -> 'a t -> unit

  val iter : (term -> 'a -> unit) -> 'a t -> unit

  val pp : 'a Fmt.t -> 'a t Fmt.t

  module Internal_for_tests : sig
    val check_invariants : 'a t -> bool

    val canon : term -> term

    val pp_error : Format.formatter -> exn -> unit
  end
end) =
struct
  let named s = Index.name ^ "-" ^ s

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

  let subst_tree_insert_random_term =
    QCheck2.Test.make
      ~name:(named "subst-tree-insert-random-term")
      ~count:100
      (QCheck2.Gen.set_shrink
         (fun _ -> Seq.empty)
         (QCheck2.Gen.array_size
            (QCheck2.Gen.return 10)
            (Arith.term_gen (fun _ -> None))))
      (fun terms ->
        let index = Index.create () in
        let table : (Expr.t, _) Hashtbl.t =
          Hashtbl.create (Array.length terms)
        in
        let exception Unexpected_key of Expr.t in
        let exception Wrong_value of Expr.t * int * int in
        let pp_arr =
          Format.pp_print_array
            ~pp_sep:(fun fmtr () -> Format.fprintf fmtr "@.")
            Expr.pp
        in
        let pp_table fmtr table =
          Format.pp_print_seq
            ~pp_sep:(fun fmtr () -> Format.fprintf fmtr "@.")
            (fun fmtr (k, v) -> Format.fprintf fmtr "@[%a@] -> %d" Expr.pp k v)
            fmtr
            (Hashtbl.to_seq table)
        in
        try
          Array.iteri
            (fun i t ->
              let ct = Index.Internal_for_tests.canon t in
              Index.insert ct i index ;
              Hashtbl.replace table ct i ;
              assert (Index.Internal_for_tests.check_invariants index))
            terms ;
          Index.iter
            (fun term data ->
              match Hashtbl.find_opt table term with
              | None -> raise (Unexpected_key term)
              | Some v ->
                  if Int.equal v data then ()
                  else raise (Wrong_value (term, v, data)))
            index ;
          true
        with
        | Unexpected_key s ->
            QCheck2.Test.fail_reportf
              "@[Unexpected key@.@[%a@]@.in \
               index@.@[%a@]@.Inputs=@.@[%a@]@.Table=@.@[%a@]@]"
              Expr.pp
              s
              (Index.pp Format.pp_print_int)
              index
              pp_arr
              terms
              pp_table
              table
        | Wrong_value (s, expected, got) ->
            QCheck2.Test.fail_reportf
              "@[Wrong value. In index:@.@[%a@]@.At key %a, expected %d, got \
               %d@.Inputs=@.@[%a@]@.Table=@.@[%a@]@]"
              (Index.pp Format.pp_print_int)
              index
              Expr.pp
              s
              expected
              got
              pp_arr
              terms
              pp_table
              table
        | exn ->
            Index.Internal_for_tests.pp_error Format.std_formatter exn ;
            QCheck2.Test.fail_reportf
              "exn %s@.@[%a@]@.Inputs=@.@[%a@]"
              (Printexc.to_string exn)
              (Index.pp Format.pp_print_int)
              index
              pp_arr
              terms)
    |> QCheck_alcotest.to_alcotest
end

module Shared_naive = Make_shared_test (struct
  include Index

  let name = "index-naive"

  let insert f data index = ignore (insert f data index)
end)

module Shared_efficient = Make_shared_test (struct
  include Index2

  type term = Arith.Expr.t

  let name = "index-efficient"

  let iter f index =
    iter (fun iterm data -> f (Internal_term.to_term iterm) data) index

  let insert f data index = ignore (insert f data index)

  module Internal_for_tests = struct
    include Internal_for_tests

    let canon = Index.Internal_for_tests.canon

    let pp_error = Index.Internal_for_tests.pp_error
  end
end)

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
    Alcotest.test_case "index-basic" `Quick (fun () ->
        let index = Index.create () in
        let one = float 1.0 in
        let two = float 2.0 in
        let t0 = Index.insert (add one one) 0 index in
        let t1 = Index.insert (add one two) 1 index in
        let t2 = Index.insert (add (mul two two) one) 2 index in
        assert (Index.Internal_for_tests.check_invariants index) ;
        check_alpha_eq_list
          ~got:(collect_unifiable_terms (add (var 0) (var 1)) index)
          ~expected:[t0; t1; t2] ;
        check_alpha_eq_list
          ~got:(collect_unifiable_terms (add (var 0) one) index)
          ~expected:[t0; t2])

  let index_cant_overwrite =
    Alcotest.test_case "index-cant-overwrite" `Quick (fun () ->
        let index = Index.create () in
        let one = float 1.0 in
        let _ = Index.insert (neg (neg (neg one))) 0 index in
        let _ = Index.insert (neg (neg one)) 1 index in
        try ignore (Index.insert (neg (neg (neg one))) 1 index)
        with Invalid_argument _ -> ())

  let index_can_overwrite =
    Alcotest.test_case "index-can-overwrite" `Quick (fun () ->
        let index = Index.create () in
        let one = float 1.0 in
        let _t0 = Index.insert (neg (neg (neg one))) 0 index in
        let _t1 = Index.insert (neg (neg one)) 1 index in
        let t2 = Index.insert (neg (neg (neg one))) 2 index in
        match collect_unifiable (neg (neg (neg one))) index with
        | [(t, v)] ->
            if v = 2 && alpha_eq t t2 then ()
            else
              Alcotest.failf
                "expected: %a@.got: %a, %d@."
                Expr.pp
                t2
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
    Alcotest.test_case "index-query-generalize" `Quick (fun () ->
        let index = Index.create () in
        let tree = mkbintree 4 in
        let _ = Index.insert tree 0 index in
        let generalizations = make_generalizations tree in
        (* let generalizations_count = List.length generalizations in *)
        List.iteri
          (fun i (_path, gen) -> ignore (Index.insert gen i index))
          generalizations ;
        (* Iterate on all generalizations of (add (var 0) (var 0)).
           We expect to find only a single variable. *)
        Index.iter_generalize
          (fun expr _ ->
            if not (Expr.is_var expr |> Option.is_some) then
              Alcotest.failf
                "Expected to single variable, found %a instead"
                Expr.pp
                expr
            else ())
          index
          (add (var 0) (var 0)) ;
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
    Alcotest.test_case "index-query-specialize" `Quick (fun () ->
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
            ~path:Path.(at_index 0 (at_index 0 (at_index 0 (at_index 0 root))))
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

let () =
  Alcotest.run
    "index"
    [ ("mscg-properties", Mscg_tests.[diag_idempotent; diag_commutative]);
      ("mscg-cases", Mscg_tests.[mscg_case0; mscg_case1; mscg_case2]);
      ( "mscg-subst",
        Mscg_tests.[mscg_nofail; mscg_disjoint_support_empty; mscg_subst] );
      ( "subst-tree",
        [ Shared_naive.subst_tree_insert_terms;
          Shared_naive.subst_tree_insert_terms2;
          Shared_naive.subst_tree_insert_random_term;
          Shared_efficient.subst_tree_insert_terms;
          Shared_efficient.subst_tree_insert_terms2;
          Shared_efficient.subst_tree_insert_random_term ] );
      ( "index-basic",
        Query_tests.
          [ index_basic;
            index_cant_overwrite;
            index_query_generalize;
            index_query_specialize ] ) ]
