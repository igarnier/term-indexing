[@@@ocaml.warning "-32"]

module Prim = struct
  type t = Add | Mul | Neg | Float of float

  let compare (x : t) (y : t) = Stdlib.compare x y

  let equal (x : t) (y : t) = x = y

  let hash = Hashtbl.hash

  let pp fmtr = function
    | Add -> Fmt.pf fmtr "Add"
    | Mul -> Fmt.pf fmtr "Mul"
    | Neg -> Fmt.pf fmtr "Neg"
    | Float f -> Fmt.pf fmtr "%.1f" f

  let arity = function Add | Mul -> 2 | Neg -> 1 | Float _ -> 0
end

module TI = Term_tools.Make (Prim)
open TI

let add x y = Term.prim Add [| x; y |]

let mul x y = Term.prim Mul [| x; y |]

let neg x = Term.prim Neg [| x |]

let float f = Term.prim (Prim.Float f) [||]

let var s = Term.var s

let t = add (var 0) (mul (var 1) (var 1))

(* Example: indexing *)

module Index = Term_indexing.Substitution_tree.Make (Prim) (TI.Term)

let keys =
  [ float 42.0;
    add (mul (var 1) (float 2.0)) (float 2.0);
    mul (float 1.0) (mul (var 2) (float 4.0));
    neg (neg (add (float 1.0) (var 3)));
    neg (neg (float 1.0));
    neg (float 1.0);
    add (var 1) (mul (float 2.0) (float 3.0)) ]

let index = Index.create ()

let () = List.iteri (fun i key -> Index.insert key i index) keys

let () = Index.iter (fun key v -> Fmt.pr "%a -> %d@." Term.pp key v) index

let query = add (mul (float 3.0) (var 0)) (var 2)

let () = Fmt.pr "unifiable@."

let () =
  Index.iter_unifiable (fun key _ -> Fmt.pr "%a@." Term.pp key) index query

let () = Fmt.pr "specialize@."

let () =
  Index.iter_specialize (fun key _ -> Fmt.pr "%a@." Term.pp key) index query

let () = Fmt.pr "generalize@."

let () =
  Index.iter_generalize (fun key _ -> Fmt.pr "%a@." Term.pp key) index query

let query = neg (var 0)

let () =
  Index.iter_specialize (fun key _ -> Fmt.pr "%a@." Term.pp key) index query

let query = neg (neg (add (float 1.0) (float 2.0)))

let () =
  Index.iter_generalize (fun key _ -> Fmt.pr "%a@." Term.pp key) index query
