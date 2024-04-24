open Lib_rewriting
open Arith
module Subst = Subst.Make (Prim) (Expr)

let mkgen () =
  let c = ref (-1) in
  fun () ->
    let v = !c in
    decr c ;
    v

let diag_idempotent =
  QCheck2.Test.make
    ~name:"mscg-diag-idempotent"
    ~print:(fun term -> Format.asprintf "%a" Expr.pp term)
    ~count:100
    Arith.gen
    (fun term ->
      let (res, _) = Subst.mscg term term (mkgen ()) in
      Expr.equal term res)

let diag_commutative =
  QCheck2.Test.make
    ~name:"mscg-diag-commutative"
    ~print:(fun (term1, term2) ->
      Format.asprintf "%a, %a" Expr.pp term1 Expr.pp term2)
    ~count:100
    (QCheck2.Gen.pair Arith.gen Arith.gen)
    (fun (term1, term2) ->
      let (res1, _) = Subst.mscg term1 term2 (mkgen ()) in
      let (res2, _) = Subst.mscg term2 term1 (mkgen ()) in
      Expr.equal res1 res2)

let mscg_case0 =
  Alcotest.test_case "mscg-case0" `Quick (fun () ->
      let term1 = add (mul (var 0) (var 1)) (var 2) in
      let term2 = add (div (var 0) (var 1)) (var 2) in
      let (res, _) = Subst.mscg term1 term2 (mkgen ()) in
      match to_native res with
      | Add (Var -1, Var 2) -> ()
      | _ -> Alcotest.fail "mscg-case0")

let mscg_case1 =
  Alcotest.test_case "mscg-case1" `Quick (fun () ->
      let term1 = add (mul (var 0) (var 1)) (var 2) in
      let term2 = mul (mul (var 0) (var 1)) (var 2) in
      let (res, _) = Subst.mscg term1 term2 (mkgen ()) in
      match to_native res with Var -1 -> () | _ -> Alcotest.fail "mscg-case1")

let mscg_case2 =
  Alcotest.test_case "mscg-case2" `Quick (fun () ->
      let term1 = add (mul (var 0) (var 1)) (var 2) in
      let term2 = add (div (var 0) (var 1)) (div (var 0) (var 1)) in
      let (res, extracted) = Subst.mscg term1 term2 (mkgen ()) in
      let extracted = List.map (fun (v, x, y, z) -> (v, (x, y, z))) extracted in
      match to_native res with
      | Add (Var -1, Var -2) -> (
          let (path1, lexpr1, rexpr1) = List.assoc (-1) extracted in
          let (path2, lexpr2, rexpr2) = List.assoc (-2) extracted in
          (match path1 with
          | At_index (0, Root) -> ()
          | _ -> Alcotest.fail "mscg-case2: wrong path1") ;
          (match path2 with
          | At_index (1, Root) -> ()
          | _ -> Alcotest.fail "mscg-case2: wrong path2") ;
          (match (to_native lexpr1, to_native rexpr1) with
          | (Mul (Var 0, Var 1), Div (Var 0, Var 1)) -> ()
          | _ -> Alcotest.fail "mscg-case2: wrong subterm") ;
          match (to_native lexpr2, to_native rexpr2) with
          | (Var 2, Div (Var 0, Var 1)) -> ()
          | _ -> Alcotest.fail "mscg-case2: wrong subterm")
      | _ -> Alcotest.fail "mscg-case2: wrong result")

let () =
  Alcotest.run
    "subst"
    [ ("mscg-properties", conv [diag_idempotent; diag_commutative]);
      ("mscg-cases", [mscg_case0; mscg_case1; mscg_case2]) ]
