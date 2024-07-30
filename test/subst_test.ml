[@@@ocaml.warning "-32"]

open Arith
module Int_map = Map.Make (Int)

module Subst_tests = struct
  let add_shadow_earlier_bindings =
    Alcotest.test_case "subst-add-shadow-earlier-bindings" `Quick (fun () ->
        let fill list =
          List.fold_left
            (fun acc (v, t) -> Subst.add v t acc)
            (Subst.empty ())
            list
        in
        let subst1 =
          fill [(0, var 10); (1, var 11); (2, var 12); (0, var 13)]
        in
        let subst2 = fill [(1, var 11); (2, var 12); (0, var 13)] in
        if not (Subst.equal subst1 subst2) then
          Alcotest.failf "Unexpected: %a <> %a" Subst.pp subst1 Subst.pp subst2
        else ())

  let seq_inverse =
    Alcotest.test_case "subst-seq-inverse" `Quick (fun () ->
        let subst =
          Subst.of_seq (List.to_seq [(0, var 10); (1, var 11); (2, var 12)])
        in
        let subst' = Subst.to_seq subst |> Subst.of_seq in
        if not (Subst.equal subst subst') then
          Alcotest.failf "Unexpected: %a <> %a" Subst.pp subst Subst.pp subst'
        else ())

  let of_seq_shadow_earlier_bindings =
    Alcotest.test_case "subst-seq-shadow-earlier-bindings" `Quick (fun () ->
        let subst1 =
          Subst.of_seq
            (List.to_seq [(0, var 10); (1, var 11); (2, var 12); (0, var 13)])
        in
        let subst2 =
          Subst.of_seq (List.to_seq [(1, var 11); (2, var 12); (0, var 13)])
        in
        if not (Subst.equal subst1 subst2) then
          Alcotest.failf "Unexpected: %a <> %a" Subst.pp subst1 Subst.pp subst2
        else ())
end

module Unification = struct
  module U = Unification

  let unify t0 t1 =
    let state = U.empty () in
    try U.unify_exn t0 t1 state
    with U.Cannot_unify ->
      QCheck.Test.fail_reportf
        "could not unify:@.t0: %a@.t1: %a@."
        Term.pp
        t0
        Term.pp
        t1

  let fail_unify t0 t1 =
    let state = U.empty () in
    try
      ignore (U.unify_exn t0 t1 state) ;
      QCheck.Test.fail_reportf
        "didn't expect to unify:@.t0: %a@.t1: %a@."
        Term.pp
        t0
        Term.pp
        t1
    with U.Cannot_unify -> ()

  let check_unify t0 t1 =
    let state = U.empty () in
    try
      ignore (U.unify_exn t0 t1 state) ;
      true
    with U.Cannot_unify -> false

  let check_fail_unify t0 t1 =
    let state = U.empty () in
    try
      ignore (U.unify_exn t0 t1 state) ;
      false
    with U.Cannot_unify -> true

  let unify_expect ~expected t0 t1 =
    let state = U.empty () in
    try
      let state = U.unify_exn t0 t1 state in
      if not (alpha_eq (Subst.lift (U.subst state) t0) expected) then
        QCheck.Test.fail_reportf "expected: %a, got %a@." Term.pp t0 Term.pp t1
      else ()
    with U.Cannot_unify ->
      QCheck.Test.fail_reportf
        "could not unify:@.t0: %a@.t1: %a@."
        Term.pp
        t0
        Term.pp
        t1

  let unification_diag =
    QCheck2.Test.make
      ~name:"unification-diag"
      ~count:100
      (Arith.term_gen (fun _ -> None))
      (fun term ->
        ignore (unify term term) ;
        true)
    |> QCheck_alcotest.to_alcotest

  let unif_commutative =
    QCheck2.Test.make
      ~name:"unif-commutative"
      ~count:10_000
      (QCheck2.Gen.pair Arith.gen Arith.gen)
      (fun (lhs, rhs) ->
        let clr = check_unify lhs rhs in
        let crl = check_unify rhs lhs in
        if not ((clr && crl) || ((not clr) && not crl)) then
          QCheck.Test.fail_reportf
            "check not symmetric: %a, %a"
            Term.pp
            lhs
            Term.pp
            rhs
        else true)
    |> QCheck_alcotest.to_alcotest

  let unification_case_1 =
    Alcotest.test_case "unification-case-1" `Quick (fun () ->
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

  let unification_case_2 =
    Alcotest.test_case "unification-case-2" `Quick (fun () ->
        let state = U.empty () in
        let state = U.unify_exn (var 0) (var 1) state in
        let state = U.unify_exn (var 1) (var 2) state in
        let state = U.unify_exn (var 0) (float 1.0) state in
        try
          let _state = U.unify_exn (var 2) (float 2.0) state in
          Alcotest.fail "unification-case-2: expected failure"
        with U.Cannot_unify -> ())

  let unification_case_3 =
    Alcotest.test_case "unification-case-3" `Quick (fun () ->
        let one = float 1.0 in
        let two = float 2.0 in
        unify_expect ~expected:(add one two) (add (var 0) two) (add one (var 1)) ;
        unify_expect
          ~expected:(add (add one one) one)
          (add (add (var 0) (var 0)) one)
          (add (var 1) (var 0)))

  let unification_regressions =
    Alcotest.test_case "unification-regressions" `Quick (fun () ->
        let rhs = mul (var 5) (sub (float 0.5) (float 1.0)) in
        let lhs = mul (var 0) (sub (var 5) (var 0)) in
        fail_unify lhs rhs)

  let unfold_case =
    Alcotest.test_case "unfold" `Quick (fun () ->
        let state = U.empty () in
        let state = U.unify_exn (var 0) (var 1) state in
        let state = U.unify_exn (var 1) (var 2) state in
        let term = float 1.0 in
        let state = U.unify_exn (var 2) term state in
        let term' = U.unfold state term in
        if not (alpha_eq term' (float 1.0)) then
          Alcotest.failf "Unexpected: %a <> %a" Term.pp term Term.pp term'
        else ())

  let generalize_diag =
    QCheck2.Test.make
      ~name:"generalize-diag"
      ~count:100
      (Arith.term_gen (fun _ -> None))
      (fun term ->
        ignore (U.generalizes term term) ;
        true)
    |> QCheck_alcotest.to_alcotest

  let generalize t1 t2 =
    if U.generalizes t1 t2 then ()
    else
      QCheck.Test.fail_reportf "expected success: %a, %a" Term.pp t1 Term.pp t2

  let generalize_fail t1 t2 =
    if not (U.generalizes t1 t2) then ()
    else
      QCheck.Test.fail_reportf "expected failure: %a, %a" Term.pp t1 Term.pp t2

  let check_generalize t1 t2 =
    generalize t1 t2 ;
    generalize_fail t2 t1

  let generalize_cases =
    Alcotest.test_case "generalize-cases" `Quick (fun () ->
        let one = float 1.0 in
        let term = add (mul one one) (div one one) in
        check_generalize (add (mul (var 0) (var 0)) (div (var 0) (var 0))) term ;
        generalize_fail (add (var 0) (div (var 0) (var 0))) term ;
        generalize_fail (add (var 0) (var 0)) term ;
        check_generalize (add (var 0) (var 1)) term ;
        check_generalize
          (add (mul (var 0) (var 0)) (div (var 1) (var 1)))
          (add (mul (var 0) (var 0)) (div (var 0) (var 0))) ;
        check_generalize
          (add (mul (var 0) (var 1)) (div (var 2) (var 3)))
          (add (mul (var 0) (var 0)) (div (var 0) (var 0))))
end

let () =
  Alcotest.run
    "subst"
    [ ( "subst",
        Subst_tests.
          [ seq_inverse;
            of_seq_shadow_earlier_bindings;
            add_shadow_earlier_bindings ] );
      ( "unification",
        Unification.
          [ unification_diag;
            unif_commutative;
            unification_case_1;
            unification_case_2;
            unification_case_3;
            unification_regressions;
            unfold_case;
            generalize_diag;
            generalize_cases ] ) ]
