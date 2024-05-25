[@@@ocaml.warning "-32"]

open Arith

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

module Query_tests = struct
  let collect_unifiable query index =
    let acc = ref [] in
    Index.iter_unifiable query (fun term v -> acc := (term, v) :: !acc) index ;
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
        let t0 = Index.insert (add one one) 0 false index in
        let t1 = Index.insert (add one two) 1 false index in
        let t2 = Index.insert (add (mul two two) one) 2 false index in
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
        let _ = Index.insert (neg (neg (neg one))) 0 false index in
        let _ = Index.insert (neg (neg one)) 1 false index in
        try ignore (Index.insert (neg (neg (neg one))) 1 false index)
        with Invalid_argument _ -> ())

  let index_can_overwrite =
    Alcotest.test_case "index-can-overwrite" `Quick (fun () ->
        let index = Index.create () in
        let one = float 1.0 in
        let _t0 = Index.insert (neg (neg (neg one))) 0 false index in
        let _t1 = Index.insert (neg (neg one)) 1 false index in
        let t2 = Index.insert (neg (neg (neg one))) 2 true index in
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
end

let () =
  Alcotest.run
    "subst"
    [ ( "subst-tree",
        [ subst_tree_insert_terms;
          subst_tree_insert_terms2;
          subst_tree_insert_random_term ] );
      ( "index-basic",
        [Query_tests.index_basic; Query_tests.index_cant_overwrite] ) ]
