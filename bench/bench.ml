[@@@ocaml.warning "-32"]

open Term_indexing

module Prim = struct
  type t = Add | Sub | Mul | Div | Neg | Float of float

  let compare (x : t) (y : t) = Stdlib.compare x y

  let equal (x : t) (y : t) = x = y

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

module Var_map : Intf.Map with type key = int = struct
  include Map.Make (Int)

  let empty () = empty

  let to_seq_keys map = to_seq map |> Seq.map fst

  let union m1 m2 =
    union
      (fun _ _ _ -> invalid_arg "Var_map.union: maps have overlapping domains")
      m1
      m2
end

module Expr = Term.Make_hash_consed (Prim) (Var_map)
module Subst_mod = Subst.Make (Prim) (Var_map) (Expr)
module Index = Index.Make (Prim) (Var_map) (Expr) (Subst_mod)
module Subst = Subst_mod

let add x y = Expr.prim Add [| x; y |]

let sub x y = Expr.prim Sub [| x; y |]

let mul x y = Expr.prim Mul [| x; y |]

let div x y = Expr.prim Div [| x; y |]

let neg x = Expr.prim Neg [| x |]

let float f = Expr.prim (Prim.Float f) [||]

let var s = Expr.var s

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
  let table = Hashtbl.create 10_000 in
  let c = ref 0 in
  let add_to_set i =
    if Hashtbl.mem table i then ()
    else (
      Hashtbl.add table i () ;
      incr c)
  in
  let t0 = Unix.gettimeofday () in
  iter_exhaustive 4 (fun expr ->
      add_to_set expr ;
      ignore (Index.insert expr 0 index)) ;
  let t1 = Unix.gettimeofday () in
  let time_to_insert = t1 -. t0 in
  let stored = ref 0 in
  Gc.compact () ;
  let t0 = Unix.gettimeofday () in
  Index.iter (fun _term _ -> incr stored) index ;
  let t1 = Unix.gettimeofday () in
  let time_to_iter = t1 -. t0 in
  Format.printf "%d distinct terms inserted (%f secs)@." !c time_to_insert ;
  Format.printf "%d distinct terms stored (%f terms/secs)@." !stored (float_of_int !stored /. time_to_iter)
