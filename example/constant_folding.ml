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

module TI = Term_indexing.Make (Prim)
open TI

let add x y = Term.prim Add [| x; y |]

let mul x y = Term.prim Mul [| x; y |]

let neg x = Term.prim Neg [| x |]

let float f = Term.prim (Prim.Float f) [||]

let var s = Term.var s

let t = add (var 0) (mul (var 1) (var 1))

(* example: zipper, folding *)

let zipper = Zipper.of_term t

let left = Zipper.move_at zipper 0 |> Option.get

let () = Fmt.pr "left: %a@." Term.pp (Zipper.cursor left)

let right = Zipper.move_at zipper 1 |> Option.get

let () = Fmt.pr "right: %a@." Term.pp (Zipper.cursor right)

let rewritten = Zipper.to_term (Zipper.replace (float 42.0) right)

let () = Fmt.pr "rewritten: %a@." Term.pp rewritten

let all_subterms =
  Zipper.fold (fun z acc -> Zipper.cursor z :: acc) (Zipper.of_term t) []

let () = Fmt.pr "%a@." (Fmt.Dump.list Term.pp) all_subterms

let all_variables =
  Zipper.fold_variables (fun v _z acc -> v :: acc) (Zipper.of_term t) []

let () = Fmt.pr "%a@." Fmt.Dump.(list Fmt.int) all_variables

(* Example: rewriting *)

let float_patt =
  Pattern.prim_pred (function Float _ -> true | _ -> false) Pattern.list_empty

let add_patt = Pattern.(prim Prim.Add (float_patt @. float_patt @. list_empty))

let mul_patt = Pattern.(prim Prim.Mul (float_patt @. float_patt @. list_empty))

let neg_patt = Pattern.(prim Prim.Neg (float_patt @. list_empty))

let get_float (term : Term.t) : float option =
  Term.destruct
    (fun prim _ -> match prim with Prim.Float f -> Some f | _ -> None)
    (fun _ -> None)
    term

let reduce (term : Term.t) : Term.t option =
  Term.destruct
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
    term

let rec rewrite_until_fixpoint term =
  let matches = Pattern.first_match [add_patt; mul_patt; neg_patt] term in
  match matches with
  | [] -> term
  | zipper :: _ ->
      let rewritten =
        match reduce (Zipper.cursor zipper) with
        | Some reduced -> reduced
        | None -> failwith "can't happen"
      in
      Fmt.pr "%a -> %a@." Term.pp term Term.pp rewritten ;
      rewrite_until_fixpoint rewritten

let expression = add (float 1.0) (add (float 2.0) (mul (float 3.0) (float 4.0)))

let normalized = rewrite_until_fixpoint expression

(* Example: substitution *)

(* Note that the domain of the substitution does not need to match the variables contained
   in the term. *)
let subst =
  [(0, float 0.0); (1, neg (float 42.0)); (2, float 2.0)]
  |> List.to_seq |> Subst.of_seq

let () = assert (Option.equal Term.equal (Subst.get 0 subst) (Some (float 0.0)))

let () = assert (Option.equal Term.equal (Subst.get 3 subst) None)

let term = add (var 1) (mul (var 2) (var 2))

let substituted = Subst.lift subst term

let () = Fmt.pr "%a@." Term.pp substituted

(* Example: unification *)

let uf_state = Unification.empty ()

let t1 = add (mul (float 1.0) (float 2.0)) (var 1)

let t2 = add (var 2) (mul (float 3.0) (float 4.0))

let () =
  match Unification.unify t1 t2 uf_state with
  | None -> failwith "unification failed"
  | Some uf_state' ->
      let subst = Unification.subst uf_state' in
      Fmt.pr "%a@." Subst.pp subst

let () = Fmt.pr "%a@." Subst.pp subst

(* Example: indexing *)

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
