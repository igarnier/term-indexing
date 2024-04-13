(* Rewriting terms. *)

module type S = sig
  type prim

  type path

  type patt

  type node = prim Term.term

  exception Rewrite_error of string * node option

  val get_subterm : term:node -> path:path -> node

  val subst : term:node -> path:path -> replacement:node -> node

  val pattern_matches : patt -> node -> bool

  val all_matches : patt -> node -> path list
end

module Make
    (X : Signature.S)
    (M : Term.S with type prim = X.t)
    (Patt : Pattern.S
              with type prim = X.t
               and type path = Path.t
               and type node = M.t) :
  S with type prim = X.t and type path = Path.t and type patt = Patt.t = struct
  type prim = X.t

  type path = Path.t

  type patt = Patt.t

  type node = M.t

  type forward_path = Path.forward

  exception Rewrite_error of string * node option

  let rec get_subterm_aux : term:node -> path:forward_path -> node =
   fun ~term ~path ->
    match path with
    | [] -> term
    | index :: l -> (
        match term.Hashcons.node with
        | Prim (_, subterms) -> get_subterm_at subterms index l)

  and get_subterm_at : node array -> int -> forward_path -> node =
   fun subterms index path ->
    let len = Array.length subterms in
    if index >= len then
      Format.kasprintf
        (fun msg -> raise (Rewrite_error (msg, None)))
        "get_subterm_at: index out of bounds (%d >= %d)"
        index
        len
    else get_subterm_aux ~term:subterms.(index) ~path

  let get_subterm : term:node -> path:path -> node =
   fun ~term ~path ->
    let path = Path.reverse path in
    get_subterm_aux ~term ~path

  let rec subst_aux : term:node -> path:forward_path -> replacement:node -> node
      =
   fun ~term ~path ~replacement ->
    match path with
    | [] -> replacement
    | index :: l -> (
        match term.Hashcons.node with
        | Prim (prim, subterms) ->
            M.prim prim (subst_at subterms index l replacement))

  and subst_at : node array -> int -> forward_path -> node -> node array =
   fun subterms index path replacement ->
    Array.mapi
      (fun i term ->
        if i = index then subst_aux ~term ~path ~replacement else term)
      subterms

  let subst : term:prim Term.term -> path:Path.t -> replacement:node -> node =
   fun ~term ~path ~replacement ->
    let path = Path.reverse path in
    subst_aux ~term ~path ~replacement

  let pattern_matches patt (n : node) = Patt.pattern_matches patt n

  let all_matches (patt : patt) (node : node) = Patt.all_matches patt node
end
