type 'prim term = 'prim desc Hashcons.hash_consed

and 'prim desc = Prim of 'prim * 'prim term array | Var of int
(* OPTIM: add a boolean tag to compute in O(1) whether a term is ground *)

let rec pp pp_prim fmtr term =
  let open Format in
  match term.Hashcons.node with
  | Var i -> fprintf fmtr "V(%d)" i
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
  match term.Hashcons.node with
  | Var _ -> acc
  | Prim (_, subterms) -> fold_subterms f acc subterms path 0

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
      | Prim (_, subterms) ->
          let len = Array.length subterms in
          if index >= len then raise (Get_subterm_oob (path, len))
          else get_subterm_fwd subterms.(index) l
      | Var _ -> raise (Get_subterm_oob (path, 0)))

let get_subterm : 'prim term -> Path.t -> 'prim term =
 fun term path ->
  let path = Path.reverse path in
  get_subterm_fwd term path

module type S = sig
  type prim

  type t = prim term

  type var := int

  type 'a var_map

  val equal : t -> t -> bool

  val hash : t -> int

  val prim : prim -> t array -> t

  val var : var -> t

  val is_var : t -> var option

  val fold : (t -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  val fold_variables : (var -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  val get_subterm_fwd : t -> Path.forward -> t

  val get_subterm : t -> Path.t -> t

  val subst : term:t -> path:Path.t -> replacement:t -> t

  val canon : t -> (unit -> var) -> var var_map * t

  val pp : Format.formatter -> t -> unit
end

module Make_hash_consed
    (P : Intf.Signature)
    (M : Intf.Map with type key = int) :
  S with type prim = P.t and type 'a var_map = 'a M.t = struct
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
      | (Prim (p1, a1), Prim (p2, a2)) ->
          P.equal p1 p2
          && Array.length a1 = Array.length a2
          && Array.for_all2 ( == ) a1 a2
      | _ -> false

    let hash = function
      | Var i -> Hashtbl.hash i
      | Prim (p, a) -> Hashtbl.hash (P.hash p, hash_node_array a)
  end)

  let table = Hcons.create 1024

  let equal (t1 : t) (t2 : t) = t1 == t2

  let hash t = t.Hashcons.hkey

  let prim head subterms =
    if Array.length subterms <> P.arity head then
      Format.kasprintf
        failwith
        "Invalid number of arguments for prim %a: expected %d, got %d"
        P.pp
        head
        (Array.length subterms)
        (P.arity head)
    else Hcons.hashcons table (Prim (head, subterms))

  let var i = Hcons.hashcons table (Var i)

  let is_var term =
    match term.Hashcons.node with Var v -> Some v | Prim (_, _) -> None

  (* re-export generic fold *)
  let fold = fold

  let fold_variables f acc term =
    fold
      (fun term path acc ->
        match term.Hashcons.node with Var v -> f v path acc | _ -> acc)
      acc
      term

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

  (* TODO optim: consider using an extensible array from int to int instead of an M.t *)
  (* TODO optim: this algorithm is potentially quadratic as we perform rewrites on-the-fly. We
     could batch those rewrites and perform them in one go. *)
  let canon : t -> (unit -> int) -> int M.t * t =
   fun term enum ->
    fold_variables
      (fun v path (canon_map, canon_term) ->
        match M.find_opt v canon_map with
        | None ->
            let canon_v = enum () in
            let canon_map = M.add v canon_v canon_map in
            let canon_term =
              if Int.equal v canon_v then
                (* We avoid doing any trivial rewrites. *)
                canon_term
              else subst ~term:canon_term ~path ~replacement:(var canon_v)
            in
            (canon_map, canon_term)
        | Some canon_v ->
            let canon_term =
              if Int.equal v canon_v then
                (* We avoid doing any trivial rewrites. *)
                canon_term
              else subst ~term:canon_term ~path ~replacement:(var canon_v)
            in
            (canon_map, canon_term))
      (M.empty (), term)
      term

  (* re-export pretty-printer *)
  let pp fmtr term = pp P.pp fmtr term
end
