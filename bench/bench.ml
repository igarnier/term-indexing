[@@@ocaml.warning "-32"]

module Prim = struct
  type t = Add | Sub | Mul | Div | Neg | Float of float

  let compare (x : t) (y : t) =
    match (x, y) with
    | (Add, Add) -> 0
    | (Add, _) -> -1
    | (_, Add) -> 1
    | (Sub, Sub) -> 0
    | (Sub, _) -> -1
    | (_, Sub) -> 1
    | (Mul, Mul) -> 0
    | (Mul, _) -> -1
    | (_, Mul) -> 1
    | (Div, Div) -> 0
    | (Div, _) -> -1
    | (_, Div) -> 1
    | (Neg, Neg) -> 0
    | (Neg, _) -> -1
    | (_, Neg) -> 1
    | (Float f, Float f') -> Float.compare f f'

  let equal (x : t) (y : t) = compare x y = 0

  let hash = Hashtbl.hash

  let pp fmtr = function
    | Add -> Format.fprintf fmtr "Add"
    | Sub -> Format.fprintf fmtr "Sub"
    | Mul -> Format.fprintf fmtr "Mul"
    | Div -> Format.fprintf fmtr "Div"
    | Neg -> Format.fprintf fmtr "Neg"
    | Float f -> Format.fprintf fmtr "%f" f

  let arity = function Add | Sub | Mul | Div -> 2 | Neg -> 1 | Float _ -> 0
end

module TI = Term_indexing.Make (Prim)
open TI
open Term

let add x y = prim Add [| x; y |]

let sub x y = prim Sub [| x; y |]

let mul x y = prim Mul [| x; y |]

let div x y = prim Div [| x; y |]

let neg x = prim Neg [| x |]

let float f = prim (Prim.Float f) [||]

let var s = var s

(* ---------------------------------------------------------------- *)

let timeit f =
  let t0 = Unix.gettimeofday () in
  f () ;
  let t1 = Unix.gettimeofday () in
  t1 -. t0
[@@ocaml.inline]

(* ---------------------------------------------------------------- *)

let rec iter_exhaustive depth k =
  if depth = 0 then k (float 0.0)
  else
    iter_exhaustive (depth - 1) @@ fun l ->
    k (neg l) ;
    iter_exhaustive (depth - 1) @@ fun r ->
    k (add l r) ;
    (* k (sub l r) ; *)
    (* k (mul l r) ; *)
    k (div l r)

let () =
  let index = Index.create () in
  let c = ref 0 in
  let acc = ref 0.0 in
  iter_exhaustive 4 (fun expr ->
      incr c ;
      let dt = timeit (fun () -> Index.insert expr 0 index) in
      acc := !acc +. dt) ;
  Format.printf
    "%d distinct terms inserted (%f kiloterms/secs)@."
    !c
    (float_of_int !c /. 1000.0 /. !acc) ;
  let stored = ref 0 in
  Gc.compact () ;
  let dt = timeit (fun () -> Index.iter (fun _term _ -> incr stored) index) in
  Format.printf
    "iter: %d distinct terms stored (%f kiloterms/secs)@."
    !stored
    (float_of_int !stored /. 1000.0 /. dt) ;
  stored := 0 ;
  let dt =
    timeit (fun () -> Index.iter_transient (fun _term _ -> incr stored) index)
  in
  Format.printf
    "iter_transient: %d distinct terms stored (%f kiloterms/secs)@."
    !stored
    (float_of_int !stored /. 1000.0 /. dt) ;
  stored := 0 ;
  let dt =
    timeit (fun () ->
        Index.iter_unifiable_transient
          (fun _term _ -> incr stored)
          index
          (var 0))
  in
  Format.printf
    "iter_unifiable_transient: %d distinct terms stored (%f kiloterms/secs)@."
    !stored
    (float_of_int !stored /. 1000.0 /. dt)
