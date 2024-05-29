type 'prim term = 'prim desc Hashcons.hash_consed

and 'prim desc = Prim of 'prim * 'prim term array * Int_option.t | Var of int
(* OPTIM: may be worth special-casing Prim for arities < 4 *)

let rec pp pp_prim fmtr term =
  let open Format in
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

(* Fold over the term. Paths are in lexicographic order when reversed.
   TODO: make tail-recursive if needed. *)
let rec fold f acc term path =
  let acc = f term path acc in
  match term.Hashcons.node with
  | Var _ -> acc
  | Prim (_, subterms, _) -> fold_subterms f acc subterms path 0

and fold_subterms f acc subterms path i =
  if i = Array.length subterms then acc
  else
    let acc = fold f acc subterms.(i) (Path.at_index i path) in
    fold_subterms f acc subterms path (i + 1)

let fold f acc term = fold f acc term Path.root

exception Get_subterm_oob of Path.forward * int

let rec get_subterm_fwd : 'prim term -> Path.forward -> 'prim term =
 fun term path ->
  match path with
  | [] -> term
  | index :: l -> (
      match term.Hashcons.node with
      | Prim (_, subterms, _) ->
          let len = Array.length subterms in
          if index >= len then raise (Get_subterm_oob (path, len))
          else get_subterm_fwd subterms.(index) l
      | Var _ -> raise (Get_subterm_oob (path, 0)))

let get_subterm : 'prim term -> Path.t -> 'prim term =
 fun term path ->
  let path = Path.reverse path in
  get_subterm_fwd term path

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

  (* re-export generic fold *)
  let fold = fold

  let rec fold_variables f acc term path =
    match term.Hashcons.node with
    | Var v -> f v path acc
    | Prim (_, subterms, ub) ->
        if Int_option.is_none ub then acc
        else fold_variables_subterms f acc subterms path 0

  and fold_variables_subterms f acc subterms path i =
    if i = Array.length subterms then acc
    else
      let acc = fold_variables f acc subterms.(i) (Path.at_index i path) in
      fold_variables_subterms f acc subterms path (i + 1)

  let fold_variables f acc term = fold_variables f acc term Path.root

  let rec map_variables f term =
    match term.Hashcons.node with
    | Prim (p, subterms, _) ->
        prim p (Array.map (fun t -> map_variables f t) subterms)
    | Var v -> f v

  (* re-export generic get_subterm_fwd *)
  let get_subterm_fwd = get_subterm_fwd

  (* re-export generic get_subterm *)
  let get_subterm = get_subterm

  let rec subst_aux : term:t -> path:Path.forward -> replacement:t -> t =
   fun ~term ~path ~replacement ->
    match path with
    | [] -> replacement
    | index :: l -> (
        match term.Hashcons.node with
        | Var _ -> raise (Get_subterm_oob (path, 0))
        | Prim (s, subterms, _ub) ->
            prim s (subst_at subterms index l replacement))

  and subst_at : t array -> int -> Path.forward -> t -> t array =
   fun subterms index path replacement ->
    Array.mapi
      (fun i term ->
        if i = index then subst_aux ~term ~path ~replacement else term)
      subterms

  let subst : term:t -> path:Path.t -> replacement:t -> t =
   fun ~term ~path ~replacement ->
    let path = Path.reverse path in
    subst_aux ~term ~path ~replacement

  (* TODO optim: consider using an extensible array from int to int instead of an M.t *)
  let canon : t -> (unit -> int) -> int M.t * t =
   fun term enum ->
    let acc =
      fold_variables
        (fun v _path canon_map ->
          match M.find_opt v canon_map with
          | None ->
              let canon_v = enum () in
              M.add v canon_v canon_map
          | Some _ -> canon_map)
        (M.empty ())
        term
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
end

module Default_map : Intf.Map with type key = int = struct
  include Map.Make (Int)

  let empty () = empty

  let to_seq_keys map = to_seq map |> Seq.map fst

  let union m1 m2 =
    union
      (fun _ _ _ -> invalid_arg "Var_map.union: maps have overlapping domains")
      m1
      m2
end
