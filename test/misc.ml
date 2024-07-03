[@@@ocaml.warning "-32"]

[@@@ocaml.warning "-37"]

module Stub () = struct
  open Arith
  module I = Index2_raw

  let index = I.create ()

  let one = float 1.0

  let () = I.insert one 1 index

  let () = Format.printf "single@.%a@." (I.pp Fmt.int) index

  let term = add (float 1.0) (float 3.0)

  let () = I.insert term 2 index

  let () = Format.printf "two@.%a@." (I.pp Fmt.int) index

  let term = add (float 1.0) (add (float 1.0) (float 3.0))

  let () = I.insert term 3 index

  let () = Format.printf "three@.%a@." (I.pp Fmt.int) index

  let () =
    I.iter (fun k v -> Format.printf "%a -> %d@." I.pp_internal_term k v) index

  (* iter-unifiable *)

  (* let () = Format.printf "iter-unifiable@." *)

  (* let () = *)
  (*   I.iter_unifiable *)
  (*     (fun k v -> Format.printf "%a -> %d@." I.pp_internal_term k v) *)
  (*     index *)
  (*     (I.of_term index (add (var 0) (var 1))) *)

  let () = Format.printf "testing union-find@."

  let index = I.create ()

  let a = float 1.0

  let b = float 2.0

  let c = float 3.0

  let () = I.insert (add (neg a) (neg b)) 1 index

  let () = I.insert (add (neg c) (neg c)) 2 index

  let () = I.insert (div (neg c) (neg c)) 2 index

  let () = Format.printf "%a@." (I.pp Fmt.int) index

  let () = Format.printf "@.testing unification@."

  let () =
    I.iter_unifiable
      (fun k v -> Format.printf "%a -> %d@." I.pp_internal_term k v)
      index
      (add (var 0) (var 1))

  let () =
    Format.printf
      "@.testing unification with equality constraints (add (var 0) (var 0))@."

  let () =
    I.iter_unifiable
      (fun k v -> Format.printf "%a -> %d@." I.pp_internal_term k v)
      index
      (add (var 0) (var 0))

  let () = Format.printf "@.testing specialization search@."

  let () =
    I.iter_specialize
      (fun k v -> Format.printf "%a -> %d@." I.pp_internal_term k v)
      index
      (add (var 0) (var 1))

  let () =
    Format.printf "@.testing specialization search with equality constraints@."

  let () =
    I.iter_specialize
      (fun k v -> Format.printf "%a -> %d@." I.pp_internal_term k v)
      index
      (add (var 0) (var 0))

  let () = Format.printf "@.testing specialization search with no constraints@."

  let () =
    I.iter_specialize
      (fun k v -> Format.printf "%a -> %d@." I.pp_internal_term k v)
      index
      (var 0)

  let () =
    Format.printf "@.testing specialization search with overlapping variables@."

  let index = I.create ()

  let () = I.insert (add (var 0) (var 0)) 1 index

  let () = I.insert (add (var 0) (var 1)) 2 index

  let () = Format.printf "%a@." (I.pp Fmt.int) index

  let () =
    I.iter_generalize
      (fun k v -> Format.printf "%a -> value=%d@." I.pp_internal_term k v)
      index
      (add (var 2) (var 1))

  let () = Format.printf "@.testing generalization@."

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

  let index = I.create ()

  let tree = mkbintree 2

  let _ = I.insert tree 0 index

  let generalizations = make_generalizations tree

  (* let generalizations_count = List.length generalizations in *)
  let () =
    List.iteri (fun i (_path, gen) -> I.insert gen i index) generalizations

  let () = Format.printf "%a@." (I.pp Fmt.int) index

  let () =
    I.iter_generalize
      (fun k v ->
        Format.printf
          "%a -> %a -> value=%d@."
          I.pp_internal_term
          k
          Expr.pp
          (I.to_term k)
          v)
      index
      (add (var 1) (var 1))

  let () = Format.printf "@.testing unification with overlapping variables@."

  let index = I.create ()

  let to_term term = term

  let a = float 1.0

  let b = float 2.0

  let t0 = add a (var 1)

  let t1 = add (var 0) b

  let t2 = var 0

  let t3 = add (var 0) (var 0)

  let () =
    I.insert t0 0 index ;
    I.insert t1 1 index ;
    I.insert t2 2 index ;
    I.insert t3 3 index

  let of_term = I.Internal_for_tests.of_term index

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
    I.iter_unifiable
      (fun term v -> acc := (internal_to_native term, v) :: !acc)
      index
      query ;
    !acc

  let collect_unifiable_terms query index =
    collect_unifiable query index |> List.map fst

  let equal_multiset cmp l1 l2 =
    let l1 = List.sort cmp l1 in
    let l2 = List.sort cmp l2 in
    List.equal (fun x y -> cmp x y = 0) l1 l2

  let () =
    let got = collect_unifiable (to_term t2) index in
    if
      not
        (equal_multiset
           Stdlib.compare
           got
           [ (to_native t0, 0);
             (to_native t1, 1);
             (to_native t2, 2);
             (to_native t3, 3) ])
    then
      Format.printf "failed %a@." Fmt.Dump.(list (pair pp_native Fmt.int)) got
    else Format.printf "succeeded@."

  (* TODO reproduce erroneous case: query = const, index contains const and var, must return both *)

  let index = I.create ()

  let () =
    I.insert (float 1.0) 0 index ;
    I.insert (var 0) 1 index

  let () =
    I.iter_unifiable
      (fun term v -> Format.printf "found %a -> %d@." I.pp_internal_term term v)
      index
      (to_term (float 1.0))
end
