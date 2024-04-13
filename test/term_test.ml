open Lib_rewriting
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

let () = Alcotest.run "term" [("fold_lexicographic", conv [fold_lexicographic])]
