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

let zero = Term.prim Zero [||]

let one t = Term.prim One [| t |]

let two t0 t1 = Term.prim Two [| t0; t1 |]

let three t0 t1 t2 = Term.prim Three [| t0; t1; t2 |]

let four t0 t1 t2 t3 = Term.prim Four [| t0; t1; t2; t3 |]

(* ---------------------------------------------------------------- *)

let timeit f =
  let t0 = Unix.gettimeofday () in
  f () ;
  let t1 = Unix.gettimeofday () in
  t1 -. t0
[@@ocaml.inline]

(* ---------------------------------------------------------------- *)

let path : Term.t -> Path.t =
 fun t ->
  let rec aux path t =
    Term.destruct
      (fun _prim subterms ->
        let arity = Array.length subterms in
        if arity = 0 then path
        else
          let i = Random.int arity in
          aux (Path.at_index i path) subterms.(i))
      (fun _ -> path)
      t
  in
  aux Path.root t

let rec large_term n =
  if n = 0 then zero
  else
    let t = large_term (n - 1) in
    four t t t t

let rec guide_zip path zip =
  match path with
  | [] -> zip
  | i :: path' -> (
      match Zipper.move_at zip i with
      | None -> assert false
      | Some zip' -> guide_zip path' zip')

let () =
  let t = large_term 1_000_000 in
  let acc = ref 0.0 in
  for i = 0 to 100 do
    let p = path t |> Path.reverse in
    let dt =
      timeit (fun () ->
          let z = guide_zip p (Zipper.of_term t) in
          Sys.opaque_identity (ignore (Zipper.to_term z)))
    in
    acc := !acc +. dt
  done ;
  Format.printf "zipper bench: %f@." !acc

(* ---------------------------------------------------------------- *)
