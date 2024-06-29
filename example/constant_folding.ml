[@@@ocaml.warning "-32"]

module Prim = struct
  type t = Add | Mul | Neg | Float of float

  let compare (x : t) (y : t) = Stdlib.compare x y

  let equal (x : t) (y : t) = x = y

  let hash = Hashtbl.hash

  let pp fmtr = function
    | Add -> Format.fprintf fmtr "Add"
    | Mul -> Format.fprintf fmtr "Mul"
    | Neg -> Format.fprintf fmtr "Neg"
    | Float f -> Format.fprintf fmtr "%.1f" f

  let arity = function Add | Mul -> 2 | Neg -> 1 | Float _ -> 0
end

module TI = Term_indexing.Make (Prim)
open TI

let add x y = Term.prim Add [| x; y |]

let mul x y = Term.prim Mul [| x; y |]

let neg x = Term.prim Neg [| x |]

let float f = Term.prim (Prim.Float f) [||]

let var s = Term.var s

(* example: path, folding *)

let t = add (var 0) (mul (var 1) (var 1))

let all_subterms = Term.fold (fun subt p acc -> (p, subt) :: acc) [] t

let () =
  List.iter
    (fun (p, subt) -> Format.printf "%a -> %a@." Path.pp p Term.pp subt)
    all_subterms

(* Example: rewriting *)

let float_patt =
  Pattern.prim_pred (function Float _ -> true | _ -> false) Pattern.list_empty

let add_patt = Pattern.(prim Prim.Add (float_patt @. float_patt @. list_empty))

let mul_patt = Pattern.(prim Prim.Mul (float_patt @. float_patt @. list_empty))

let neg_patt = Pattern.(prim Prim.Neg (float_patt @. list_empty))

let get_float (term : Term.t) : float option =
  Term.destruct
    term
    (fun prim _ -> match prim with Prim.Float f -> Some f | _ -> None)
    (fun _ -> None)

let reduce (term : Term.t) : Term.t option =
  Term.destruct
    term
    (fun prim operands ->
      match (prim, operands) with
      | ((Add | Mul), [| l; r |]) ->
          Option.bind (get_float l) @@ fun l ->
          Option.bind (get_float r) @@ fun r ->
          Option.some
            (match prim with
            | Add -> float (l +. r)
            | Mul -> float (l *. r)
            | _ -> assert false)
      | (Neg, [| x |]) ->
          Option.bind (get_float x) @@ fun x -> Option.some (float (-.x))
      | _ -> Option.some term)
    (fun _ -> Option.some term)

let rec rewrite_until_fixpoint term =
  let matches = Pattern.first_match [add_patt; mul_patt; neg_patt] term in
  match matches with
  | [] -> term
  | path :: _ ->
      let rewritten =
        Term.subst ~term ~path (fun e ->
            match reduce e with
            | Some reduced -> reduced
            | None -> failwith "can't happen")
      in
      Format.printf "%a -> %a@." Term.pp term Term.pp rewritten ;
      rewrite_until_fixpoint rewritten

let expression = add (float 1.0) (add (float 2.0) (mul (float 3.0) (float 4.0)))

let normalized = rewrite_until_fixpoint expression

(* Example: indexing *)
