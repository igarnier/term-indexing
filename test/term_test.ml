open Term_indexing
open Arith

let fold_lexicographic =
  QCheck2.Test.make
    ~name:"fold_lexicographic"
    ~print:(fun term -> Format.asprintf "%a" Expr.pp term)
    ~count:100
    Arith.gen
    (fun term ->
      let paths_sorted_lexicographically =
        Term.fold (fun _term path acc -> Path.reverse path :: acc) [] term
        |> List.rev
      in
      let sort =
        List.sort (List.compare Int.compare) paths_sorted_lexicographically
      in
      paths_sorted_lexicographically = sort)

let fold_variables =
  Alcotest.test_case "fold_variables" `Quick (fun () ->
      let term = Expr.(add (var 0) (var 1)) in
      let vars =
        Expr.fold_variables
          (fun var path acc -> (Path.reverse path, var) :: acc)
          []
          term
      in
      let expected = [([1], 1); ([0], 0)] in
      Alcotest.(check (list (pair (list int) int))) "variables" expected vars)

let to_dispenser xs =
  let s = ref xs in
  fun () ->
    match !s () with
    | Seq.Nil -> None
    | Cons (x, xs) ->
        s := xs ;
        Some x

let rec seq_ints i () = Seq.Cons (i, seq_ints (i + 1))

let ints () =
  let dispenser = to_dispenser (seq_ints 0) in
  fun () -> Option.get (dispenser ())

let canon_variable_count =
  QCheck2.Test.make
    ~name:"canon_variable_count"
    ~print:(fun term -> Format.asprintf "%a" Expr.pp term)
    ~count:100
    Arith.gen
    (fun term ->
      let vars =
        Expr.fold_variables (fun var _path acc -> var :: acc) [] term
        |> List.sort_uniq Int.compare |> List.length
      in
      let (_, canon) = Expr.canon term (ints ()) in
      let canon_vars =
        Expr.fold_variables (fun var _path acc -> var :: acc) [] canon
        |> List.sort_uniq Int.compare |> List.length
      in
      Int.equal vars canon_vars)

let canon_idempotent =
  QCheck2.Test.make
    ~name:"canon_idempotent"
    ~print:(fun term -> Format.asprintf "%a" Expr.pp term)
    ~count:100
    Arith.gen
    (fun term ->
      let (_, canon) = Expr.canon term (ints ()) in
      let (_, canon') = Expr.canon canon (ints ()) in
      Format.printf "%a -> %a -> %a@." Expr.pp term Expr.pp canon Expr.pp canon' ;
      Expr.equal canon canon')

let () =
  Alcotest.run
    "term"
    [ ("fold_lexicographic", conv [fold_lexicographic]);
      ("fold_variables", [fold_variables]);
      ("canon", conv [canon_variable_count; canon_idempotent]) ]
