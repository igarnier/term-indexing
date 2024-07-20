module Prim = struct
  type t = Zero | One | Two | Three | Four

  let compare (x : t) (y : t) = Stdlib.compare x y

  let equal (x : t) (y : t) = x = y

  let hash = Hashtbl.hash

  let pp fmtr = function
    | Zero -> Format.fprintf fmtr "zero"
    | One -> Format.fprintf fmtr "one"
    | Two -> Format.fprintf fmtr "two"
    | Three -> Format.fprintf fmtr "three"
    | Four -> Format.fprintf fmtr "four"

  let arity = function
    | Zero -> 0
    | One -> 1
    | Two -> 2
    | Three -> 3
    | Four -> 4
end

module Pack = Term_indexing.Make (Prim)
open Pack
module Z = Zipper
module Gen = QCheck2.Gen

let zero = Term.prim Zero [||]

let one t = Term.prim One [| t |]

let two t0 t1 = Term.prim Two [| t0; t1 |]

let three t0 t1 t2 = Term.prim Three [| t0; t1; t2 |]

let four t0 t1 t2 t3 = Term.prim Four [| t0; t1; t2; t3 |]

let symbol =
  Gen.frequencya
    [| (20, `Zero); (15, `One); (10, `Two); (5, `Three); (1, `Four) |]

let term_gen : Term.t Gen.t =
  let open Gen in
  fix
    (fun self (path, n) ->
      if n = 0 then return zero
      else
        symbol >>= function
        | `Zero -> return zero
        | `One -> map one (self (0 :: path, n - 1))
        | `Two -> map2 two (self (0 :: path, n - 1)) (self (1 :: path, n - 1))
        | `Three ->
            map3
              three
              (self (0 :: path, n - 1))
              (self (1 :: path, n - 1))
              (self (2 :: path, n - 1))
        | `Four ->
            let* t0 = self (0 :: path, n - 1)
            and* t1 = self (1 :: path, n - 1)
            and* t2 = self (2 :: path, n - 1)
            and* t3 = self (3 :: path, n - 1) in
            return (four t0 t1 t2 t3))
    ([], 5)

let path : Term.t -> int list Gen.t =
 fun t ->
  let open Gen in
  let rec aux path t =
    Term.destruct
      (fun _prim subterms ->
        let arity = Array.length subterms in
        if arity = 0 then return path
        else
          let* c = Gen.bool in
          if c then
            let* i = Gen.int_bound (arity - 1) in
            aux (i :: path) subterms.(i)
          else return path)
      (fun _ -> return path)
      t
  in
  aux [] t

let rec guide_zip path zip =
  match path with
  | [] -> zip
  | i :: path' -> (
      match Z.move_at zip i with
      | None ->
          QCheck2.Test.fail_reportf
            "guide_zip: invalid path (%a, %a)"
            (Fmt.Dump.list Fmt.int)
            path
            Term.pp
            (Z.cursor zip)
      | Some zip' -> guide_zip path' zip')

let test_zip_unzip =
  QCheck2.Test.make
    ~count:1000
    ~name:"zip_unzip"
    Gen.(
      term_gen >>= fun t ->
      path t >>= fun p -> return (t, p))
  @@ fun (t, p) ->
  let zip = guide_zip (List.rev p) (Z.of_term t) in
  let unzip = Z.to_term zip in
  if Term.equal t unzip then true
  else
    QCheck2.Test.fail_reportf
      "unzip (zip t) =/= t\nt = %a\nunzip (zip t) = %a\npath = %a"
      Term.pp
      t
      Term.pp
      unzip
      Fmt.Dump.(list Fmt.int)
      p

let test_zip_move_up =
  QCheck2.Test.make
    ~count:1000
    ~name:"zip_move_up"
    Gen.(
      term_gen >>= fun t ->
      path t >>= fun p -> return (t, p))
  @@ fun (t, p) ->
  let zip = guide_zip (List.rev p) (Z.of_term t) in
  let unzip =
    let rec fixp zip =
      match Z.move_up zip with None -> zip | Some zip' -> fixp zip'
    in
    fixp zip |> Z.cursor
  in
  if Term.equal t unzip then true
  else
    QCheck2.Test.fail_reportf
      "unzip (zip t) =/= t\nt = %a\nunzip (zip t) = %a\npath = %a"
      Term.pp
      t
      Term.pp
      unzip
      Fmt.Dump.(list Fmt.int)
      p

let test_zip_compare_eq =
  QCheck2.Test.make
    ~count:1000
    ~name:"zip_compare_eq"
    Gen.(
      term_gen >>= fun t ->
      path t >>= fun p -> return (t, p))
  @@ fun (t, p) ->
  let zip = guide_zip (List.rev p) (Z.of_term t) in
  if Z.compare zip zip = 0 then true
  else
    QCheck2.Test.fail_reportf
      "compare zip zip =/= 0\nterm = %a\npath = %a"
      Term.pp
      t
      Fmt.Dump.(list Fmt.int)
      p

let test_zip_eq =
  QCheck2.Test.make
    ~count:1000
    ~name:"zip_eq"
    Gen.(
      term_gen >>= fun t ->
      path t >>= fun p -> return (t, p))
  @@ fun (t, p) ->
  let zip = guide_zip (List.rev p) (Z.of_term t) in
  let zip' = guide_zip (List.rev p) (Z.of_term t) in
  if Z.equal zip zip' then true
  else
    QCheck2.Test.fail_reportf
      "eq zip zip =/= true\nterm = %a\npath = %a"
      Term.pp
      t
      Fmt.Dump.(list Fmt.int)
      p

let test_zip_set =
  QCheck2.Test.make ~count:1000 ~name:"zip_set" term_gen @@ fun t ->
  let module ZS = Set.Make (Zipper) in
  let zipper_set =
    Z.fold (fun zip acc -> ZS.add zip acc) ZS.empty (Z.of_term t)
  in
  let card = ZS.cardinal zipper_set in
  let node_count = Term.fold (fun _ acc -> acc + 1) 0 t in
  if Int.equal card node_count then true
  else
    QCheck2.Test.fail_reportf
      "cardinal zip_set =/= node_count\nterm = %a\ncard = %d\nnode_count = %d"
      Term.pp
      t
      card
      node_count

let test_zip_hash =
  Alcotest.test_case "zip_hash" `Quick @@ fun () ->
  let t = Gen.generate1 term_gen in
  let p = Gen.generate1 (path t) in
  let zip = guide_zip (List.rev p) (Z.of_term t) in
  ignore (Z.hash zip)

let conv qctests = List.map QCheck_alcotest.to_alcotest qctests

let () =
  Alcotest.run
    "path"
    [ ("zip_unzip", conv [test_zip_unzip; test_zip_move_up]);
      ("zip_compare", conv [test_zip_compare_eq; test_zip_eq; test_zip_set]);
      ("zip_hash", [test_zip_hash]) ]
