[@@@ocaml.warning "-32"]

open Arith
module Int_map = Lib_rewriting.Int_map

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
end

module Unification = struct
  module U = Subst.Unification

  let unify t0 t1 =
    let state = U.empty () in
    try fst (U.unify t0 t1 state)
    with U.Cannot_unify ->
      QCheck.Test.fail_reportf
        "could not unify:@.t0: %a@.t1: %a@."
        Expr.pp
        t0
        Expr.pp
        t1

  let fail_unify t0 t1 =
    let state = U.empty () in
    try
      ignore (U.unify t0 t1 state) ;
      QCheck.Test.fail_reportf
        "didn't expect to unify:@.t0: %a@.t1: %a@."
        Expr.pp
        t0
        Expr.pp
        t1
    with U.Cannot_unify -> ()

  let unification_diag =
    QCheck2.Test.make
      ~name:"unification-diag"
      ~count:100
      (Arith.term_gen (fun _ -> None))
      (fun term ->
        ignore (unify term term) ;
        true)
    |> QCheck_alcotest.to_alcotest

  let unification_cases =
    Alcotest.test_case "unification-cases" `Quick (fun () ->
        let one = float 1.0 in
        let two = float 2.0 in
        let t0 = add one one in
        let t1 = add one two in
        ignore (unify t0 (add (var 0) one)) ;
        ignore (unify t0 (add one (var 0))) ;
        fail_unify t0 (add two (var 0)) ;
        fail_unify t1 (add two (var 0)) ;
        fail_unify t0 t1 ;
        fail_unify (add (var 0) one) (add one two))
end

let () =
  let open Mscg_tests in
  Alcotest.run
    "subst"
    [ ("mscg-properties", conv [diag_idempotent; diag_commutative]);
      ("mscg-cases", [mscg_case0; mscg_case1; mscg_case2]);
      ("subst-print", conv [print_test]);
      ("mscg-subst", [mscg_nofail; mscg_disjoint_support_empty; mscg_subst]);
      ("unification", Unification.[unification_diag; unification_cases]) ]
