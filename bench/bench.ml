[@@@ocaml.warning "-32"]

open Term_indexing

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

module type Benchable_index = sig
  type 'a t

  type internal_term

  type term

  val create : unit -> 'a t

  val insert : term -> int -> int t -> unit

  val iter : (internal_term -> 'a -> unit) -> 'a t -> unit

  val pp : 'a Fmt.t -> 'a t Fmt.t
end

module Make_bench
    (T : Intf.Term_core with type prim = Prim.t)
    (I : Benchable_index with type term = T.t) =
struct
  open T

  let add x y = prim Add [| x; y |]

  let sub x y = prim Sub [| x; y |]

  let mul x y = prim Mul [| x; y |]

  let div x y = prim Div [| x; y |]

  let neg x = prim Neg [| x |]

  let float f = prim (Prim.Float f) [||]

  let var s = var s

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
    let index = I.create () in
    let c = ref 0 in
    let acc = ref 0.0 in
    iter_exhaustive 4 (fun expr ->
        incr c ;
        let t0 = Unix.gettimeofday () in
        I.insert expr 0 index ;
        let t1 = Unix.gettimeofday () in
        let time_to_insert = t1 -. t0 in
        acc := !acc +. time_to_insert) ;
    Format.printf
      "%d distinct terms inserted (%f kiloterms/secs)@."
      !c
      (float_of_int !c /. 1000.0 /. !acc) ;
    let stored = ref 0 in
    Gc.compact () ;
    let t0 = Unix.gettimeofday () in
    I.iter (fun _term _ -> incr stored) index ;
    (* Format.printf "%a@." (I.pp Fmt.int) index ; *)
    let t1 = Unix.gettimeofday () in
    let time_to_iter = t1 -. t0 in
    Format.printf
      "%d distinct terms stored (%f kiloterms/secs)@."
      !stored
      (float_of_int !stored /. 1000.0 /. time_to_iter)
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
module Index = Slow_index.Make (Prim) (Var_map) (Expr) (Subst_mod)
module Subst = Subst_mod

module _ =
  Make_bench
    (Expr)
    (struct
      include Index

      type internal_term = term

      let insert k v i = ignore (insert k v i)
    end)

module Index2 = Term_index.Make (Prim) (Expr) (Subst)

module _ =
  Make_bench
    (Expr)
    (struct
      include Index2

      let iter = iter_transient
    end)
