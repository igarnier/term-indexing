module Vec = Containers.Vector

(** The module type of substitutions *)
module type S = sig
  (** The type of terms *)
  type term

  (** The type of substitutions *)
  type t

  val of_list : (int * term) list -> t

  val to_list : t -> (int * term) list

  val pp : Format.formatter -> t -> unit

  val identity : unit -> t

  val is_identity : t -> bool

  val equal : t -> t -> bool

  val eval : int -> t -> term option

  val eval_exn : int -> t -> term

  val lift : t -> term -> term

  (** [union s1 s2] computes the union of [s1] and [s2].
      Returns [None] if [s1] and [s2] do not have disjoint domains. *)
  val union : t -> t -> t option

  (** [mscg term1 term2 freshgen] computes a triple [(result, residual1, residual2)] where
      [result] is the most spceific common generalization of [term1] and [term2],
      [residual1] is a substitution such that [result] is equal to [term1] after applying [residual1],
      and [residual2] is a substitution such that [result] is equal to [term2] after applying [residual2]. *)
  val mscg : term -> term -> (unit -> int) -> term * t * t

  (** [mscg_subst s1 s2 freshgen] computes a triple [(result, residual1, residual2)] where
      [result] is the most specific common generalization of [s1] and [s2],
      [residual1] is a substitution such that [result] is equal to [s1] after composing with [residual1],
      and [residual2] is a substitution such that [result] is equal to [s2] after composing [residual2]. *)
  val mscg_subst : t -> t -> (unit -> int) -> t * t * t
end

(** The module type of substitution trees *)
module type Tree_S = sig
  (** The type of substitutions *)
  type subst

  (** The type of terms *)
  type term

  (** The type of substitution trees *)
  type 'a t

  val create : unit -> 'a t

  (** TODO *)
  val insert : term -> 'a -> 'a t -> unit

  val iter : (term -> 'a) -> 'a t -> unit
end

let is_indicator v = v < 0

module Make (X : Signature.S) (T : Term.S with type prim = X.t) :
  S with type term = T.t = struct
  type term = T.t

  type t = T.t Int_map.t

  let identity () = Int_map.empty

  let is_identity : t -> bool = Int_map.is_empty

  let of_list l : t = Int_map.of_list l

  let to_list (subst : t) = Int_map.bindings subst

  let pp fmtr subst =
    let pp_binding fmtr (v, t) =
      if is_indicator v then
        Format.fprintf fmtr "@[<hov 2>[%d] ->@ @[%a@]@]" v T.pp t
      else Format.fprintf fmtr "@[<hov 2>%d ->@ @[%a@]@]" v T.pp t
    in
    Format.fprintf
      fmtr
      "{@[@,%a@,@]}"
      (Format.pp_print_list
         ~pp_sep:(fun fmtr () -> Format.fprintf fmtr "@.")
         pp_binding)
      (Int_map.to_list subst)

  let equal (s1 : t) (s2 : t) = Int_map.equal T.equal s1 s2

  let eval v (subst : t) = Int_map.find_opt v subst

  let eval_exn v (subst : t) = Int_map.find v subst

  (* /!\ no occur check, the substitution should be well-founded or this will stack overflow *)
  let rec lift subst (term : term) =
    match term.Hashcons.node with
    | Prim (prim, subterms) -> T.prim prim (Array.map (lift subst) subterms)
    | Var v -> (
        match eval v subst with None -> term | Some term -> lift subst term)

  let union subst1 subst2 =
    let exception Invalid_union in
    try
      Int_map.union (fun _ _ _ -> raise Invalid_union) subst1 subst2
      |> Option.some
    with Invalid_union -> None

  let generalize t1 t2 gen residual1 residual2 =
    let v = gen () in
    (T.var v, Int_map.add v t1 residual1, Int_map.add v t2 residual2)
  [@@ocaml.inline]

  (*
     invariant: domain of residuals are indexing variables. Newly
     added variables in residuals are disjoint from all existing variables.
  *)
  let rec mscg_aux (t1 : T.t) (t2 : T.t) gen residual1 residual2 =
    if T.equal t1 t2 then (t1, residual1, residual2)
    else
      (* Does it hold that t1 and t2 cannot be both indicator variables? *)
      match (t1.Hashcons.node, t2.Hashcons.node) with
      | (Term.Prim (prim1, subterms1), Term.Prim (prim2, subterms2)) ->
          if X.equal prim1 prim2 then
            let (subterms, residual1, residual2) =
              mscg_subterms subterms1 subterms2 gen residual1 residual2 [] 0
            in
            (T.prim prim1 subterms, residual1, residual2)
          else generalize t1 t2 gen residual1 residual2
      | (_, Term.Var v) ->
          if is_indicator v then (t2, Int_map.add v t1 residual1, residual2)
          else generalize t1 t2 gen residual1 residual2
      | (Term.Var v, _) ->
          if is_indicator v then (t1, residual1, Int_map.add v t2 residual2)
          else generalize t1 t2 gen residual1 residual2

  and mscg_subterms subterms1 subterms2 gen residual1 residual2 terms i =
    assert (Array.length subterms1 = Array.length subterms2) ;
    if i = Array.length subterms1 then
      (Array.of_list (List.rev terms), residual1, residual2)
    else
      let (term, residual1, residual2) =
        mscg_aux subterms1.(i) subterms2.(i) gen residual1 residual2
      in
      mscg_subterms
        subterms1
        subterms2
        gen
        residual1
        residual2
        (term :: terms)
        (i + 1)

  let mscg t1 t2 gen = mscg_aux t1 t2 gen Int_map.empty Int_map.empty

  let top_symbol_disagrees (t1 : T.t) (t2 : T.t) =
    match (t1.Hashcons.node, t2.Hashcons.node) with
    | (Term.Prim (prim1, _), Term.Prim (prim2, _)) -> not (X.equal prim1 prim2)
    | (Term.Var v1, Term.Var v2) -> v1 <> v2
    | (Term.Prim _, Term.Var _) | (Term.Var _, Term.Prim _) -> true

  let mscg_subst (s1 : t) (s2 : t) gen =
    let residual1_acc = ref Int_map.empty in
    let residual2_acc = ref Int_map.empty in
    let result =
      Int_map.merge
        (fun v t1_opt t2_opt ->
          match (t1_opt, t2_opt) with
          | (None, None) -> assert false
          | (None, Some t2) ->
              residual2_acc := Int_map.add v t2 !residual2_acc ;
              None
          | (Some t1, None) ->
              residual1_acc := Int_map.add v t1 !residual1_acc ;
              None
          | (Some t1, Some t2) ->
              if T.equal t1 t2 then (* optimization *)
                Some t1
              else if top_symbol_disagrees t1 t2 then (
                (* If [top_symbol_disagrees t1 t2] then calling [mscg] would yield
                   a mapping from [v] (an indicator variable, by assumption) to a fresh indicator variable,
                   and in the residuals, mapping the fresh indicator variable to resp. [t1] and [t2]. We
                   avoid creating a new variable by directly mapping [v] to [t1] (resp. [t2])
                *)
                residual1_acc := Int_map.add v t1 !residual1_acc ;
                residual2_acc := Int_map.add v t2 !residual2_acc ;
                None)
              else
                let (res, residual1, residual2) =
                  mscg_aux t1 t2 gen !residual1_acc !residual2_acc
                in
                residual1_acc := residual1 ;
                residual2_acc := residual2 ;
                Some res)
        s1
        s2
    in
    (result, !residual1_acc, !residual2_acc)
end

module Make_index
    (X : Signature.S)
    (T : Term.S with type prim = X.t)
    (Subst : S with type term = T.t) =
struct
  type term = T.t

  type subst = Subst.t

  (* Invariant: keys of a substitution are indexing variables,
     which are strictly negative *)
  type 'a tree = { fresh : int ref; nodes : 'a node Vec.vector }

  and 'a node =
    { mutable head : subst;
      (* We should be able to index nodes by the head constructor *)
      subtrees : 'a node Vec.vector;
      mutable data : 'a option
    }

  let rec to_box pp_data node =
    let open PrintBox in
    hlist
      [ box_of_subst node.head;
        vlist
          (box_of_data pp_data node.data
          :: box_of_subtrees pp_data node.subtrees) ]

  and box_of_data pp_data data =
    let open PrintBox in
    match data with
    | None -> text "<>"
    | Some data -> text (Format.asprintf "%a" pp_data data)

  and box_of_subst subst = PrintBox.text (Format.asprintf "%a" Subst.pp subst)

  and box_of_subtrees pp_data vec = Vec.to_list vec |> List.map (to_box pp_data)

  let pp_node pp_data fmtr node = PrintBox_text.pp fmtr (to_box pp_data node)

  let pp pp_data fmtr tree =
    PrintBox_text.pp fmtr (PrintBox.vlist (box_of_subtrees pp_data tree.nodes))

  let canonical_indexing_variable = -1

  let create () =
    (* It is critical that indexing variables are < canonical_indexing_variable *)
    { fresh = ref canonical_indexing_variable; nodes = Vec.create () }

  let try_set tree data may_overwrite =
    if may_overwrite then tree.data <- Some data
    else
      match tree.data with
      | None -> tree.data <- Some data
      | Some _ -> invalid_arg "try_set"

  let insert_subst (subst : subst) (data : 'a) (may_overwrite : bool)
      (tree : 'a tree) =
    let counter = tree.fresh in
    assert (not (Subst.is_identity subst)) ;
    (* We insert [subst] in the tree, possibly refining existing nodes. *)
    let rec insert_aux subst (t : 'a node Vec.vector) i =
      if i >= Vec.length t then
        Vec.push t { head = subst; subtrees = Vec.create (); data = Some data }
      else
        let ti = Vec.get t i in
        match ti with
        | { head; subtrees; data = _ } ->
            (* [residual1] contains either variables in the domain of [subst] or fresh variables,
               similarly for [residual2] wrt [head].
               Those variables correspond either to
               - variables out the domain of the other substitution,
               - variables corresponding to incompatible terms
               - fresh variables mapping to sub-terms witnessing incompatibility.
               If a variable is in the domain of [result] it is neither in [residual1]
               or [residual2].
            *)
            let (result, residual1, residual2) =
              Subst.mscg_subst subst head (fun () ->
                  decr counter ;
                  !counter)
            in
            if Subst.is_identity result then
              (* [subst] is incompatible with [head], try next sibling
                 TODO: we might optimize the search by indexing trees by their head constructor for a particular variable.
                 This is reminiscent of a trie. The heuristic to choose which variable to split would be crucial. *)
              insert_aux subst t (i + 1)
            else if Subst.equal result head then
              if
                (* [subst] instantiates (refines) [head]. *)
                (* Here, [residual1] may only define variables disjoint from [result]. *)
                Subst.is_identity residual1
              then
                (* [subst] = [result] = [head] *)
                try_set ti data may_overwrite
              else insert_aux residual1 subtrees 0
            else (
              (* [subst] has a nontrivial mscg
                 - we replace [head] by [result] ([result] generalizes [head])
                 - we introduce a new node below the current one labelled by [residual2]
                 - next to the node labelled by [residual2] we introduce a leaf labelled by [residual1] *)
              assert (not (Subst.is_identity residual2)) ;
              ti.head <- residual2 ;
              let new_node_children =
                Vec.of_array
                  [| ti;
                     { head = residual1;
                       subtrees = Vec.create ();
                       data = Some data
                     }
                  |]
              in
              let new_node =
                { head = result; subtrees = new_node_children; data = None }
              in
              Vec.set t i new_node)
    in
    insert_aux subst tree.nodes 0

  let canonical_indexing_variable = -1

  let insert term data may_overwrite tree =
    insert_subst
      (Subst.of_list [(canonical_indexing_variable, term)])
      data
      may_overwrite
      tree

  let check_invariants tree =
    let exception Fail in
    let rec check_invariants node =
      let head = node.head in
      Vec.iter
        (fun node' ->
          let head' = node'.head in
          if not (Option.is_some (Subst.union head head')) then raise Fail ;
          check_invariants node')
        node.subtrees
    in
    try
      Vec.iter check_invariants tree.nodes ;
      true
    with Fail -> false

  (*
     To reconstruct the substitution at a given node, we can rely on the fact that on
     a path from the root all substitutions have disjoint domains. From such a substitution,
     we can extract the term by evaluating the substitution.
   *)

  let rec iter_node f subst node =
    let subst =
      match Subst.union node.head subst with
      | None -> assert false
      | Some subst -> subst
    in
    (match node.data with
    | None -> ()
    | Some data ->
        let term = Subst.eval_exn canonical_indexing_variable subst in
        f (Subst.lift subst term) data) ;
    for i = 0 to Vec.length node.subtrees - 1 do
      iter_node f subst (Vec.get node.subtrees i)
    done

  let iter f { nodes; _ } = Vec.iter (iter_node f (Subst.identity ())) nodes

  (* TODO *)
  (* let iter_unifiable_node query f tree = *)
  (*   (\* if head is unifiable with current state then *)
  (*      1) iterate on node.data if relevant *)
  (*      2) iterate on subtrees *\) *)
  (*   assert false *)

  (* let iter_unifiable query f { nodes; _ } = *)
  (*   Vec.iter (iter_unifiable_node query f) nodes *)
end
