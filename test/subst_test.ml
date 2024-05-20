[@@@ocaml.warning "-32"]

open Arith
module Int_map = Lib_rewriting.Int_map

let diag_idempotent =
  QCheck2.Test.make
    ~name:"mscg-diag-idempotent"
    ~print:(fun term -> Format.asprintf "%a" Expr.pp term)
    ~count:100
    Arith.gen
    (fun term ->
      let (res, _, _) = Index.Internal_for_tests.mscg term term in
      Expr.equal term res)

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

let print_test =
  QCheck2.Test.make
    ~name:"subst-print-test"
    ~count:100
    Arith.subst_gen
    (fun term ->
      Format.printf "%a@." Subst.pp term ;
      true)

let mkgen ?(start = 0) () =
  let c = ref start in
  fun () ->
    let v = !c in
    incr c ;
    Index.indicator v

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
        List.map (fun (i, t) -> (i - len, t)) pairs
        |> List.to_seq |> Subst.of_seq
      in
      let (result, _, _) =
        Index.Internal_for_tests.mscg_subst
          subst
          subst'
          (mkgen ~start:(-1000) ())
      in
      Subst.is_identity result)
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
        [ (Index.indicator 1, neg a);
          (Index.indicator 2, add c x1);
          (Index.indicator 3, neg c) ]
        |> List.to_seq |> Subst.of_seq
      in
      let subst2 =
        [ (Index.indicator 1, neg b);
          (Index.indicator 2, x1);
          (Index.indicator 3, neg x2) ]
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
      assert_eq_subst mscg (Index.indicator 1) (neg (var (Index.indicator 4))) ;
      assert_eq_subst mscg (Index.indicator 3) (neg (var (Index.indicator 5))))

let subst_tree_insert_terms =
  Alcotest.test_case "subst-tree-insert" `Quick (fun () ->
      let index = Index.create () in
      assert (Index.Internal_for_tests.check_invariants index) ;
      let _ = Index.insert (add (float 1.0) (float 1.0)) 0 false index in
      assert (Index.Internal_for_tests.check_invariants index) ;
      let _ = Index.insert (float 1.0) 0 false index in
      assert (Index.Internal_for_tests.check_invariants index) ;
      let _ = Index.insert (add (float 1.0) (float 1.0)) 1 true index in
      assert (Index.Internal_for_tests.check_invariants index))

let subst_tree_insert_terms2 =
  Alcotest.test_case "subst-tree-insert-terms-2" `Quick (fun () ->
      let index = Index.create () in
      let _ = Index.insert (neg (var 543159235)) 0 true index in
      let _ = Index.insert (neg (float ~-.500.0)) 1 true index in
      let _ = Index.insert (neg (div (float 42.0) (float 73.))) 2 true index in
      let _ = Index.insert (neg (var 543159235)) 3 true index in
      Index.iter
        (fun term data ->
          if Expr.equal term (neg (var 543159235)) then assert (data = 3)
          else ())
        index)

let subst_tree_insert_random_term =
  QCheck2.Test.make
    ~name:"subst-tree-insert-random-term"
    ~count:100
    (QCheck2.Gen.set_shrink
       (fun _ -> Seq.empty)
       (QCheck2.Gen.array_size
          (QCheck2.Gen.return 10)
          (Arith.term_gen (fun _ -> None))))
    (fun terms ->
      let index = Index.create () in
      let table = Hashtbl.create (Array.length terms) in
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
            let t = Index.insert t i true index in
            Hashtbl.replace table t i ;
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
      | Index.Internal_for_tests.Invariant_violation (path, head, head') ->
          QCheck2.Test.fail_reportf
            "Invariant violated@.@[at path %a@,\
             head=%a@,\
             head'=%a@]@.@[%a@]@.Inputs=@.@[%a@]"
            (Format.pp_print_list
               ~pp_sep:(fun fmtr () -> Format.fprintf fmtr ".")
               Format.pp_print_int)
            path
            Subst.pp
            head
            Subst.pp
            head'
            (Index.pp Format.pp_print_int)
            index
            pp_arr
            terms
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
          QCheck2.Test.fail_reportf
            "exn %s@.@[%a@]@.Inputs=@.@[%a@]"
            (Printexc.to_string exn)
            (Index.pp Format.pp_print_int)
            index
            pp_arr
            terms)
  |> QCheck_alcotest.to_alcotest

let () =
  Alcotest.run
    "subst"
    [ ("mscg-properties", conv [diag_idempotent; diag_commutative]);
      ("mscg-cases", [mscg_case0; mscg_case1; mscg_case2]);
      ("subst-print", conv [print_test]);
      ("mscg-subst", [mscg_nofail; mscg_disjoint_support_empty; mscg_subst]);
      ( "subst-tree",
        [ subst_tree_insert_terms;
          subst_tree_insert_terms2;
          subst_tree_insert_random_term ] ) ]
