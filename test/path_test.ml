open Lib_rewriting
open QCheck2

let rec path_of_list : int list -> Path.t =
 fun list ->
  match list with
  | [] -> Path.Root
  | i :: list -> Path.at_index i (path_of_list list)

let gen =
  let open Gen in
  map path_of_list (list_size (return 5) (int_range 0 9))

(* Of course that a hash function is not injective, but for small enough paths
   it's good enough. *)
let path_hash_injectivity =
  Test.make
    ~name:"path_hash_injectivity"
    ~count:1000
    ~print:(fun (p1, p2) -> Format.asprintf "%a, %a" Path.pp p1 Path.pp p2)
    (Gen.pair gen gen)
    (fun (p1, p2) ->
      if Path.compare p1 p2 <> 0 then Path.hash p1 <> Path.hash p2 else true)

let conv qctests = List.map QCheck_alcotest.to_alcotest qctests

let () =
  Alcotest.run
    "path"
    [("short_path_hash_injectivity", conv [path_hash_injectivity])]
