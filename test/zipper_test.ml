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
        | `One -> map one (self (Path.at_index 0 path, n - 1))
        | `Two ->
            map2
              two
              (self (Path.at_index 0 path, n - 1))
              (self (Path.at_index 1 path, n - 1))
        | `Three ->
            map3
              three
              (self (Path.at_index 0 path, n - 1))
              (self (Path.at_index 1 path, n - 1))
              (self (Path.at_index 2 path, n - 1))
        | `Four ->
            let* t0 = self (Path.at_index 0 path, n - 1)
            and* t1 = self (Path.at_index 1 path, n - 1)
            and* t2 = self (Path.at_index 2 path, n - 1)
            and* t3 = self (Path.at_index 3 path, n - 1) in
            return (four t0 t1 t2 t3))
    (Path.root, 5)

let path : Term.t -> Path.t Gen.t =
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
            aux (Path.at_index i path) subterms.(i)
          else return path)
      (fun _ -> return path)
      t
  in
  aux Path.root t

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
  Format.printf "%a, %a@." Term.pp t Path.pp p ;
  let zip = guide_zip (Path.reverse p) (Z.of_term t) in
  let unzip = Z.to_term zip in
  if Term.equal t unzip then true
  else
    QCheck2.Test.fail_reportf
      "unzip (zip t) =/= t\nt = %a\nunzip (zip t) = %a\npath = %a"
      Term.pp
      t
      Term.pp
      unzip
      Path.pp
      p

let test_zip_move_up =
  QCheck2.Test.make
    ~count:1000
    ~name:"zip_move_up"
    Gen.(
      term_gen >>= fun t ->
      path t >>= fun p -> return (t, p))
  @@ fun (t, p) ->
  Format.printf "%a, %a@." Term.pp t Path.pp p ;
  let zip = guide_zip (Path.reverse p) (Z.of_term t) in
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
      Path.pp
      p

let conv qctests = List.map QCheck_alcotest.to_alcotest qctests

let () =
  Alcotest.run "path" [("zip_unzip", conv [test_zip_unzip; test_zip_move_up])]
