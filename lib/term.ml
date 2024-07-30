type 'prim term = 'prim desc Hashcons.hash_consed

and 'prim desc = Prim of 'prim * 'prim term array * Int_option.t | Var of int
(* OPTIM: may be worth special-casing Prim for arities < 4 *)

let rec pp pp_prim fmtr term =
  let open Format in
  let pp_print_array ~pp_sep pp_elt fmtr arr =
    Format.pp_print_list ~pp_sep pp_elt fmtr (Array.to_list arr)
  in
  match term.Hashcons.node with
  | Var i -> fprintf fmtr "V(%d)" i
  | Prim (prim, [||], _) -> fprintf fmtr "%a" pp_prim prim
  | Prim (prim, subterms, _) ->
      fprintf
        fmtr
        "@[<hv 1>%a(%a)@]"
        pp_prim
        prim
        (pp_print_array
           ~pp_sep:(fun fmtr () -> fprintf fmtr ",@ ")
           (pp pp_prim))
        subterms

let rec pp_sexp pp_prim fmtr term =
  let open Format in
  let pp_print_array ~pp_sep pp_elt fmtr arr =
    Format.pp_print_list ~pp_sep pp_elt fmtr (Array.to_list arr)
  in
  match term.Hashcons.node with
  | Var i -> fprintf fmtr "(var %d)" i
  | Prim (prim, [||], _) -> fprintf fmtr "%a" pp_prim prim
  | Prim (prim, subterms, _) ->
      fprintf
        fmtr
        "@[<hv 1>(%a %a)@]"
        pp_prim
        prim
        (pp_print_array
           ~pp_sep:(fun fmtr () -> fprintf fmtr "@ ")
           (pp_sexp pp_prim))
        subterms

(* Fold over the term.
   TODO: make tail-recursive if needed. *)
let rec fold f term acc =
  let acc = f term acc in
  match term.Hashcons.node with
  | Var _ -> acc
  | Prim (_, subterms, _) -> fold_subterms f subterms acc 0

and fold_subterms f subterms acc i =
  if i = Array.length subterms then acc
  else
    let acc = fold f subterms.(i) acc in
    fold_subterms f subterms acc (i + 1)

let fold f term acc = fold f term acc

exception Get_subterm_oob of int list * int

let rec get_subterm : 'prim term -> int list -> 'prim term =
 fun term path ->
  match path with
  | [] -> term
  | index :: l -> (
      match term.Hashcons.node with
      | Prim (_, subterms, _) ->
          let len = Array.length subterms in
          if index >= len then raise (Get_subterm_oob (path, len))
          else get_subterm subterms.(index) l
      | Var _ -> raise (Get_subterm_oob (path, 0)))

module Make_hash_consed
    (P : Intf.Signature)
    (M : Intf.Map with type key = int) :
  Intf.Term
    with type prim = P.t
     and type t = P.t term
     and type 'a var_map = 'a M.t = struct
  type prim = P.t

  type t = prim term

  type 'a var_map = 'a M.t

  let hash_empty_array = Hashtbl.hash [||]

  let hash_node_array (l : t array) : int =
    let open Hashcons in
    Array.fold_left (fun h elt -> Hashtbl.hash (h, elt.hkey)) hash_empty_array l

  module Hcons = Hashcons.Make (struct
    type t = prim desc

    let equal desc1 desc2 =
      match (desc1, desc2) with
      | (Var i1, Var i2) -> Int.equal i1 i2
      | (Prim (p1, a1, ub1), Prim (p2, a2, ub2)) ->
          P.equal p1 p2
          && Array.length a1 = Array.length a2
          && Int_option.equal ub1 ub2
          && Array.for_all2 ( == ) a1 a2
      | _ -> false

    let hash = function
      | Var i -> Hashtbl.hash i
      | Prim (p, a, ub) -> Hashtbl.hash (P.hash p, hash_node_array a, ub)
  end)

  let table = Hcons.create 1024

  let equal (t1 : t) (t2 : t) = t1 == t2

  let compare (t1 : t) (t2 : t) = Int.compare t1.Hashcons.tag t2.Hashcons.tag

  let hash t = t.Hashcons.hkey

  let ub : _ term -> Int_option.t =
   fun term ->
    match term.Hashcons.node with
    | Var v -> Int_option.of_int (Int.abs v)
    | Prim (_, _, ub) -> ub

  let ub_array : _ term array -> Int_option.t =
   fun subterms ->
    (* TODO optim: manually unroll the cases where the length is <= 3 *)
    Array.fold_left
      (fun acc term -> Int_option.max acc (ub term))
      Int_option.none
      subterms

  let prim head subterms =
    if Array.length subterms <> P.arity head then
      Format.kasprintf
        invalid_arg
        "Invalid number of arguments for prim %a: expected %d, got %d"
        P.pp
        head
        (Array.length subterms)
        (P.arity head)
    else Hcons.hashcons table (Prim (head, subterms, ub_array subterms))

  let var i = Hcons.hashcons table (Var i)

  let is_var term =
    match term.Hashcons.node with Var v -> Some v | Prim (_, _, _) -> None

  let destruct fprim fvar term =
    match term.Hashcons.node with
    | Prim (p, subterms, _) -> fprim p subterms
    | Var v -> fvar v
  [@@ocaml.inline]

  let destruct2 fpp fpv fvp fvv term1 term2 =
    match (term1.Hashcons.node, term2.Hashcons.node) with
    | (Prim (p1, subterms1, _), Prim (p2, subterms2, _)) ->
        fpp p1 subterms1 p2 subterms2
    | (Prim (p, subterms, _), Var v) -> fpv p subterms v
    | (Var v, Prim (p, subterms, _)) -> fvp v p subterms
    | (Var v1, Var v2) -> fvv v1 v2
  [@@ocaml.inline]

  (* re-export generic fold *)
  let fold = fold

  let rec fold_variables f term acc =
    match term.Hashcons.node with
    | Var v -> f v acc
    | Prim (_, subterms, ub) ->
        if Int_option.is_none ub then acc
        else fold_variables_subterms f subterms acc 0

  and fold_variables_subterms f subterms acc i =
    if i = Array.length subterms then acc
    else
      let acc = fold_variables f subterms.(i) acc in
      fold_variables_subterms f subterms acc (i + 1)

  let fold_variables f acc term = fold_variables f acc term

  let rec map_variables f term =
    match term.Hashcons.node with
    | Prim (p, subterms, ub) ->
        if Int_option.is_none ub then term
        else prim p (Array.map (fun t -> map_variables f t) subterms)
    | Var v -> f v

  (* re-export generic get_subterm *)
  let get_subterm = get_subterm

  let rec subst : term:t -> path:int list -> (t -> t) -> t =
   fun ~term ~path f ->
    match path with
    | [] -> f term
    | index :: l -> (
        match term.Hashcons.node with
        | Var _ -> raise (Get_subterm_oob (path, 0))
        | Prim (s, subterms, _ub) -> prim s (subst_at subterms index l f))

  and subst_at : t array -> int -> int list -> (t -> t) -> t array =
   fun subterms index path f ->
    Array.mapi
      (fun i term -> if i = index then subst ~term ~path f else term)
      subterms

  (* TODO optim: consider using an extensible array from int to int instead of an M.t *)
  let canon : t -> (unit -> int) -> int M.t * t =
   fun term enum ->
    let acc =
      fold_variables
        (fun v canon_map ->
          match M.find_opt v canon_map with
          | None ->
              let canon_v = enum () in
              M.add v canon_v canon_map
          | Some _ -> canon_map)
        term
        (M.empty ())
    in
    let result =
      map_variables
        (fun v ->
          match M.find_opt v acc with
          | None -> assert false
          | Some canon_v -> var canon_v)
        term
    in
    (acc, result)

  (* re-export pretty-printer *)
  let pp fmtr term = pp P.pp fmtr term

  let pp_sexp fmtr term = pp_sexp P.pp fmtr term

  let uid term = term.Hashcons.tag
end
[@@ocaml.inline]

module Default_map : Intf.Map with type key = int = struct
  include Int_map

  let empty () = empty

  let to_seq_keys map = to_seq map |> Seq.map fst

  let union m1 m2 =
    union
      (fun _ _ _ -> invalid_arg "Var_map.union: maps have overlapping domains")
      m1
      m2
end
