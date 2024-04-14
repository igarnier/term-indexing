type 'prim term = 'prim desc Hashcons.hash_consed

and 'prim desc = Prim of 'prim * 'prim term array
(* OPTIM: add a boolean to compute in O(1) whether a term is ground *)

let get_prim term = match term.Hashcons.node with Prim (prim, _) -> prim
[@@ocaml.inline]

let get_subterms term =
  match term.Hashcons.node with Prim (_, subterms) -> subterms
[@@ocaml.inline]

let rec pp pp_prim fmtr term =
  let open Format in
  match term.Hashcons.node with
  | Prim (prim, [||]) -> fprintf fmtr "%a" pp_prim prim
  | Prim (prim, subterms) ->
      fprintf
        fmtr
        "@[<hv 1>%a(%a)@]"
        pp_prim
        prim
        (pp_print_array
           ~pp_sep:(fun fmtr () -> fprintf fmtr ";@ ")
           (pp pp_prim))
        subterms

(* Fold over the term. Paths are in lexicographic order when reversed.
   TODO: make tail-recursive if needed. *)
let rec fold f acc term path =
  let acc = f term path acc in
  fold_subterms f acc (get_subterms term) path 0

and fold_subterms f acc subterms path i =
  if i = Array.length subterms then acc
  else
    let path = Path.at_index i path in
    let acc = fold f acc subterms.(i) path in
    fold_subterms f acc subterms path (i + 1)

let fold f acc term = fold f acc term Path.root

exception Get_subterm_oob of Path.forward * int

let rec get_subterm_fwd : 'prim term -> Path.forward -> 'prim term =
 fun term path ->
  match path with
  | [] -> term
  | index :: l -> (
      match term.Hashcons.node with
      | Prim (_, subterms) ->
          let len = Array.length subterms in
          if index >= len then raise (Get_subterm_oob (path, len))
          else get_subterm_fwd subterms.(index) l)

let get_subterm : 'prim term -> Path.t -> 'prim term =
 fun term path ->
  let path = Path.reverse path in
  get_subterm_fwd term path

module type S = sig
  type prim

  type t = prim term

  val prim : prim -> t array -> t

  val fold : (t -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  val fold_variables : (t -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  val get_subterm_fwd : 'a term -> Path.forward -> 'a term

  val get_subterm : 'a term -> Path.t -> 'a term

  val subst : term:t -> path:Path.t -> replacement:t -> t

  val pp : Format.formatter -> t -> unit
end

module Make_hash_consed (X : Signature.S) : S with type prim = X.t = struct
  type prim = X.t

  type t = prim term

  let hash_empty_array = Hashtbl.hash [||]

  let hash_node_array (l : t array) : int =
    let open Hashcons in
    Array.fold_left (fun h elt -> Hashtbl.hash (h, elt.hkey)) hash_empty_array l

  module Hcons = Hashcons.Make (struct
    type t = prim desc

    let equal (Prim (p1, a1)) (Prim (p2, a2)) =
      if Array.length a1 <> Array.length a2 then false
      else X.equal p1 p2 && Array.for_all2 (fun x y -> x == y) a1 a2

    let hash (Prim (p, a)) = Hashtbl.hash (Hashtbl.hash p, hash_node_array a)
  end)

  let table = Hcons.create 1024

  let prim head subterms =
    if Array.length subterms <> X.arity head then
      Format.kasprintf
        failwith
        "Invalid number of arguments for prim %a: expected %d, got %d"
        X.pp
        head
        (Array.length subterms)
        (X.arity head)
    else Hcons.hashcons table (Prim (head, subterms))

  let fold = fold

  let fold_variables f acc term =
    fold
      (fun term path acc ->
        match X.is_var (get_prim term) with
        | None -> acc
        | Some _ -> f term path acc)
      acc
      term

  let get_subterm_fwd = get_subterm_fwd

  let get_subterm = get_subterm

  let rec subst_aux : term:t -> path:Path.forward -> replacement:t -> t =
   fun ~term ~path ~replacement ->
    match path with
    | [] -> replacement
    | index :: l -> (
        match term.Hashcons.node with
        | Prim (s, subterms) -> prim s (subst_at subterms index l replacement))

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

  let pp fmtr term = pp X.pp fmtr term
end
