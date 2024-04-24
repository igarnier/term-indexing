module Vec = Containers.Vector

module Make (X : Signature.S) (T : Term.S with type prim = X.t) = struct
  type subst = T.t Int_map.t

  (* Invariant: variables in a key are strictly negative *)
  type key = T.t

  type 'a tree = Node of subst * 'a tree array | Leaf of 'a

  let is_indicator v = v < 0

  let generalize t1 t2 gen path acc =
    let var = gen () in
    (T.var var, (var, path, t1, t2) :: acc)
  [@@ocaml.inline]

  let rec mscg (t1 : T.t) (t2 : T.t) gen path acc =
    if T.equal t1 t2 then (t1, acc)
    else
      match (t1.Hashcons.node, t2.Hashcons.node) with
      | (Term.Var v1, Term.Var v2) ->
          if is_indicator v1 then (t1, (v1, path, t1, t2) :: acc)
          else if is_indicator v2 then (t2, (v1, path, t1, t2) :: acc)
          else generalize t1 t2 gen path acc
      | (Term.Prim (prim1, subterms1), Term.Prim (prim2, subterms2)) ->
          if X.equal prim1 prim2 then
            let (subterms, acc) =
              mscg_subterms subterms1 subterms2 gen path acc [] 0
            in
            (T.prim prim1 subterms, acc)
          else generalize t1 t2 gen path acc
      | (Term.Prim _, Term.Var _) | (Term.Var _, Term.Prim _) ->
          generalize t1 t2 gen path acc

  and mscg_subterms subterms1 subterms2 gen path acc terms i =
    assert (Array.length subterms1 = Array.length subterms2) ;
    if i = Array.length subterms1 then (Array.of_list (List.rev terms), acc)
    else
      let (term, acc) =
        mscg subterms1.(i) subterms2.(i) gen (Path.at_index i path) acc
      in
      mscg_subterms subterms1 subterms2 gen path acc (term :: terms) (i + 1)

  let mscg t1 t2 gen = mscg t1 t2 gen Path.root []

  (* Array.fold_left2 *)
  (*   (fun (path, acc) t1 t2 -> mscg t1 t2 path gen acc) *)
  (*   (path, acc) *)
  (*   subterms1 *)
  (*   subterms2 *)

  let eval (subst : subst) (v : int) = Int_map.find_opt v subst

  exception Break

  (** [instantiate sigma tau] checks whether [sigma] instantiates [tau].

      This is the case if for all variable [x] in the domain of [tau], one has
      [term_instantiate (eval sigma x) (eval tau x)] *)
  let rec instantiate sigma tau =
    Int_map.for_all
      (fun x tau_x ->
        match eval sigma x with
        | None -> raise Break
        | Some sigma_x -> instantiate_term sigma_x tau_x)
      tau

  (** [instantiate_term s t] checks whether [s] instantiates [t].

      This is the case if any of the following conditions hold:
      - [s = t]
      - [s] is not a variable and [t] is a variable
  *)
  and instantiate_term (_s : T.t) (_t : T.t) = assert false

  let unify _uf _head _query = assert false

  (* let instantiates query subst = *)
  (*   Int_map.union (fun v term1 term2 -> instantiate term1 term2) query subst *)

  (* checks whether [query] instantiates [key] *)
  (* let instantiates uf (key : key) (query : T.t) = assert false *)

  let rec retrieve (query : subst) (t : 'a tree) uf acc =
    match t with
    | Node (head, ts) -> (
        let (uf, res_opt) = unify uf head query in
        match res_opt with
        | None -> acc
        | Some refined_query ->
            Array.fold_left
              (fun acc subtree -> retrieve refined_query subtree uf acc)
              acc
              ts)
    | Leaf data -> data :: acc
end
