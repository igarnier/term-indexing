module Vec = Containers.Vector

module IRef = struct
  type 'a ref = { mutable contents : 'a; uid : int }

  let fresh : unit -> int =
    let counter = ref 0 in
    fun () ->
      let uid = !counter in
      counter := !counter + 1 ;
      uid

  let ref x = { contents = x; uid = fresh () }

  let ( ! ) r = r.contents

  let ( := ) r x = r.contents <- x

  let pp_ref pp_data fmtr r = Format.fprintf fmtr "%d=%a" pp_data r.contents
end

module Make
    (P : Intf.Signature)
    (T : Intf.Term with type prim = P.t and type t = P.t Term.term) =
struct
  open IRef

  module Internal_term = struct
    type prim = P.t

    type var = int

    type desc = Prim of prim * t array | Var of var | IVar

    and t = desc ref

    let is_ivar (t : t) = match !t with IVar -> true | _ -> false

    let rec copy : t -> t =
     fun term ->
      match !term with
      | Prim (prim, subtrees) -> ref (Prim (prim, Array.map copy subtrees))
      | Var v -> ref (Var v)
      | IVar -> ref IVar

    let pp_uid_opt fmtr = function
      | None -> ()
      | Some uid -> Format.fprintf fmtr "%d:" uid

    let rec desc_to_tree : ?uid:int -> desc -> PrintBox.t =
     fun ?uid desc ->
      match desc with
      | Prim (prim, subtrees) ->
          PrintBox.tree
            (PrintBox.text (Format.asprintf "%a%a" pp_uid_opt uid P.pp prim))
            (Array.to_list (Array.map to_tree subtrees))
      | Var v -> PrintBox.text (Format.asprintf "%aV(%d)" pp_uid_opt uid v)
      | IVar -> PrintBox.asprintf "%aivar" pp_uid_opt uid

    and to_tree term = desc_to_tree ~uid:term.uid !term

    let pp fmtr term =
      let tree = to_tree term in
      PrintBox_text.pp fmtr tree

    let prim p subterms = ref (Prim (p, subterms))

    let var v = ref (Var v)

    let destruct term ifprim ifvar =
      match !term with
      | Prim (p, subterms) -> ifprim p subterms
      | Var v -> ifvar v
      | IVar -> assert false

    let is_var term =
      match !term with
      | Var v -> Some v
      | Prim (_, _) -> None
      | IVar -> assert false

    let rec fold f acc term path =
      let acc = f term path acc in
      match !term with
      | Var _ -> acc
      | Prim (_, subterms) -> fold_subterms f acc subterms path 0
      | IVar -> assert false

    and fold_subterms f acc subterms path i =
      if i = Array.length subterms then acc
      else
        let acc = fold f acc subterms.(i) (Path.at_index i path) in
        fold_subterms f acc subterms path (i + 1)

    let fold f acc term = fold f acc term Path.root

    let ivars term =
      let rec loop term acc =
        match !term with
        | Var _ -> acc
        | Prim (_, subterms) ->
            Array.fold_left (fun acc term -> loop term acc) acc subterms
        | IVar -> term :: acc
      in
      loop term []

    let vars_upper_bound term =
      let rec loop term acc =
        match !term with
        | Var v -> Int.max v acc
        | Prim (_, subterms) ->
            Array.fold_left (fun acc term -> loop term acc) acc subterms
        | IVar -> acc
      in
      loop term 0

    let rec of_term : T.t -> t =
     fun term ->
      match term.Hashcons.node with
      | Term.Var v -> var v
      | Term.Prim (p, subtrees, _) ->
          let subtrees = Array.map of_term subtrees in
          prim p subtrees

    let to_term : t -> T.t =
     fun term ->
      let next =
        let c = Stdlib.ref (vars_upper_bound term) in
        fun () ->
          incr c ;
          c.contents
      in
      let rec to_term term =
        match !term with
        | Var v -> T.var v
        | Prim (p, subtrees) ->
            let subtrees = Array.map to_term subtrees in
            T.prim p subtrees
        | IVar ->
            let v = next () in
            term := Var v ;
            T.var v
      in
      to_term term

    let rec get_subterm_fwd : t -> Path.forward -> t =
     fun term path ->
      match path with
      | [] -> term
      | index :: l -> (
          match !term with
          | Prim (_, subterms) ->
              let len = Array.length subterms in
              if index >= len then raise (Term.Get_subterm_oob (path, len))
              else get_subterm_fwd subterms.(index) l
          | Var _ -> raise (Term.Get_subterm_oob (path, 0))
          | IVar -> assert false)
  end

  module _ : Intf.Term_core with type prim = P.t = struct
    include Internal_term
  end

  type term = Internal_term.t

  type iref = Internal_term.t

  type subst = (iref * Internal_term.t) list

  type 'a node =
    { mutable head : subst;
      mutable subtrees : 'a node Vec.vector;
      mutable data : 'a option
    }

  type 'a t = { nodes : 'a node Vec.vector; root : Internal_term.t }

  let box_of_data pp_data data =
    let open PrintBox in
    match data with
    | None -> text "<>"
    | Some data -> text (Format.asprintf "%a" pp_data data)

  let box_of_subst subst =
    let open PrintBox in
    frame
    @@ vlist
         ~bars:true
         (List.map
            (fun (v, t) ->
              hlist [Internal_term.to_tree v; Internal_term.to_tree t])
            subst)

  let box_of_subst_with_data pp_data subst data =
    let open PrintBox in
    frame
    @@ hlist
         [ vlist
             ~bars:true
             (List.map
                (fun (v, t) ->
                  hlist [Internal_term.to_tree v; Internal_term.to_tree t])
                subst);
           box_of_data pp_data data ]

  let pp_subst fmtr subst = PrintBox_text.pp fmtr (box_of_subst subst)

  let rec to_box pp_data node =
    let open PrintBox in
    tree
      ~indent:4
      (hlist
         [ box_of_subst_with_data pp_data node.head node.data;
           text (string_of_int (Vec.length node.subtrees)) ])
      (List.map (to_box pp_data) (Vec.to_list node.subtrees))

  and box_of_subtrees pp_data vec =
    let open PrintBox in
    align
      ~h:`Center
      ~v:`Center
      (hlist (List.map (to_box pp_data) (Vec.to_list vec)))

  let pp pp_data fmtr tree =
    PrintBox_text.pp fmtr (box_of_subtrees pp_data tree.nodes)

  let subst_is_empty = List.is_empty

  let generalize subst_term node_term residual_subst residual_node =
    let residual_subst = (node_term, subst_term) :: residual_subst in
    (* We need to wrap the term pointed to by [node_term] in a fresh ref cell;
       [node_term] will be pointing to either the [subst_term] or the fresh cell
       depending on which term is matched. *)
    let residual_node = (node_term, ref !node_term) :: residual_node in
    node_term := Internal_term.IVar ;
    (residual_subst, residual_node)

  (* [mscg subst_term node_term residual_subst residual_node] destructively updates
     [node_term] to correspond to the most specific common generalization of
     [subst_term] and [node_term]. Both remainders are added to the residuals.

     Pre-condition: [subst_term] contains no [IVar]
     Post-condition: generalized sub-terms of [node_term] are set to [Internal_term.IVar] and
     appear in the domain of both [residual_subst] and [residual_node]
  *)
  let rec mscg (subst_term : Internal_term.t) (node_term : Internal_term.t)
      (residual_subst : subst) (residual_node : subst) : subst * subst =
    match (!subst_term, !node_term) with
    | (Prim (prim1, args1), Prim (prim2, args2)) ->
        if P.equal prim1 prim2 then
          let (residual_subst, residual_node) =
            Seq.fold_left2
              (fun (residual_subst, residual_node) arg1 arg2 ->
                let (residual_subst, residual_node) =
                  mscg arg1 arg2 residual_subst residual_node
                in
                (residual_subst, residual_node))
              (residual_subst, residual_node)
              (Array.to_seq args1)
              (Array.to_seq args2)
          in
          (residual_subst, residual_node)
        else generalize subst_term node_term residual_subst residual_node
    | (Var v1, Var v2) ->
        if Int.equal v1 v2 then (residual_subst, residual_node)
        else generalize subst_term node_term residual_subst residual_node
    | (Var _, Prim _) | (Prim _, Var _) ->
        generalize subst_term node_term residual_subst residual_node
    | (IVar, _) -> assert false
    | ((Prim _ | Var _), IVar) ->
        (* [t1] is a variable or term, [t2] is an indicator variable *)
        (* [node_term] is already the mscg *)
        ((node_term, subst_term) :: residual_subst, residual_node)

  let top_symbol_disagree (t1 : Internal_term.t) (t2 : Internal_term.t) =
    match (!t1, !t2) with
    | (Prim (prim1, _), Prim (prim2, _)) -> not (P.equal prim1 prim2)
    | (Var v1, Var v2) -> not (Int.equal v1 v2)
    | (Prim _, Var _) | (Var _, Prim _) -> true
    | (IVar, IVar) -> assert false
    | _ -> false

  let create () = { nodes = Vec.create (); root = ref Internal_term.IVar }

  let non_trivial subst =
    not (List.exists (fun (_v, t) -> Internal_term.is_ivar t) subst)

  let reset subst = List.iter (fun (v, _) -> v := Internal_term.IVar) subst

  (* Note: [update_subst] is not robust to sharing sub-terms across inserted terms. *)
  let update_subst term f (tree : 'a t) =
    (* Format.printf "inserting@.%a@." Internal_term.pp term ; *)
    (* Format.printf "%a@." (pp Fmt.int) tree ; *)
    let rec insert_aux (subst : subst) (t : 'a node Vec.vector) i =
      (* Precondition: domain of [subst] is set *)
      (* Postcondition: domain of [subst] is unset *)
      (* Postcondition: domain of [(Vec.get t i).head] is unset *)
      (* Format.printf "subst: %a@." pp_subst subst ; *)
      if i >= Vec.length t then (
        (* Format.printf "End of vector@." ; *)
        Vec.push
          t
          { head = subst; subtrees = Vec.create (); data = Some (f None) } ;
        reset subst)
      else
        let ({ head; subtrees; data = _ } as ti) = Vec.get t i in
        let (general, partial_residual_subst, residual_node) =
          List.fold_left
            (fun (general, residual_subst, residual_node) ((v, t) as binding) ->
              (*
                  the pair [(v, t)] is a pair of references to term descriptors:
                    v = ref desc1
                    t = ref desc2
                  By assumption [v] is either the root of the index, or appears as a [IVar] subterm
                  in the right-hand side of a substitution stored in the index. During insertion,
                  this [IVar] may be set to a subterm to be matched against [t], which points to a term
                  that appeared in the position of [v] in one previously inserted term.
                *)
              (* Format.printf "examining binding (%a, %a)@." Internal_term.pp v Internal_term.pp t ; *)
              assert (not (Internal_term.is_ivar t)) ;
              if Internal_term.is_ivar v then
                (* variable is unset hence not in domain of [subst], binding goes to [residual_node] *)
                (general, residual_subst, binding :: residual_node)
              else if top_symbol_disagree v t then (
                (* Toplevel mismatch. *)
                let desc = !v in
                v := IVar ;
                (* TODO: examine `generalize` and align *)
                ( general,
                  (v, ref desc) :: residual_subst,
                  binding :: residual_node ))
              else
                let (residual_subst, residual_node) =
                  mscg v t residual_subst residual_node
                in
                let () = assert (not (Internal_term.is_ivar t)) in
                v := IVar ;
                ((v, t) :: general, residual_subst, residual_node))
            ([], [], [])
            head
        in

        (* let () = *)
        (*   Format.printf "head@." ; *)
        (*   Format.printf "%a@." pp_subst head ; *)
        (*   Format.printf "general@." ; *)
        (*   Format.printf "%a@." pp_subst general ; *)
        (*   Format.printf "residual_subst@." ; *)
        (*   Format.printf "%a@." pp_subst residual_subst ; *)
        (*   Format.printf "residual_node@." ; *)
        (*   Format.printf "%a@." pp_subst residual_node *)
        (* in *)

        (*
           At this point:
           - subst = residual_subst \circ general
           - head  = residual_node \circ general
           - bindings in [general] are of the form [(IVar, t)] where [t != IVar]
           - bindings in [head] that were mapped in [subst] are of the form [(IVar, t)]
         *)
        let () =
          assert (
            List.for_all
              (fun (v, t) ->
                Internal_term.is_ivar v && not (Internal_term.is_ivar t))
              general) ;

          assert (
            List.for_all
              (fun (v, t) ->
                Internal_term.is_ivar v && not (Internal_term.is_ivar t))
              head)
        in

        if subst_is_empty general then (
          (* [subst] is incompatible with [head], try next sibling
             TODO: we might optimize the search by indexing trees by their head constructor
             for a particular variable. This is reminiscent of a trie. The heuristic to choose
             which variable to split would be crucial. *)

          (* subst = residual_subst
             re-establish pre-condition for recursive call by reverting the
             state of variables in domain of [partial_residual_subst] *)
          (* let () = Format.printf "skipping@." in *)
          List.iter (fun (v, t) -> v := !t) partial_residual_subst ;
          insert_aux subst t (i + 1))
        else
          (* reset variables in head *)
          (* let () = List.iter (fun (v, _) -> v := Internal_term.IVar) head in *)
          (* let subst' = *)
          (*   List.filter (fun (v, _t) -> not (Internal_term.is_ivar v)) subst *)
          (* in *)
          (* let residual_subst = List.rev_append subst' residual_subst in *)
          let residual_subst =
            List.fold_left
              (fun residual_subst ((v, _t) as binding) ->
                if not (Internal_term.is_ivar v) then binding :: residual_subst
                else residual_subst)
              partial_residual_subst
              subst
          in
          let () = List.iter (fun (v, t) -> v := !t) residual_subst in
          (* let () = *)
          (*   Format.printf "reset head@." ; *)
          (*   Format.printf "%a@." pp_subst head ; *)
          (*   Format.printf "general@." ; *)
          (*   Format.printf "%a@." pp_subst general ; *)
          (*   Format.printf "residual_subst@." ; *)
          (*   Format.printf "%a@." pp_subst residual_subst ; *)
          (*   Format.printf "residual_node@." ; *)
          (*   Format.printf "%a@." pp_subst residual_node *)
          (* in *)
          if subst_is_empty residual_subst && subst_is_empty residual_node then
            (* exact match: general = head *)
            (* At this point:
               - [general] domain is unset, [head = general] and [subst = general] hence
                 post-condition is satisfied *)
            ti.data <- Some (f ti.data)
          else if subst_is_empty residual_subst then (
            (* Here, [subst = general], [head = residual_node \circ general]
               it follows that head refines [subst].
            *)
            ti.head <- general ;
            ti.subtrees <-
              Vec.of_array
                [| { head = residual_node;
                     subtrees = ti.subtrees;
                     data = ti.data
                   }
                |] ;
            ti.data <- None ;
            reset residual_node)
          else if subst_is_empty residual_node then
            (* Here, [head = general], [subst = residual_subst \circ general]
               it follows that [subst] refines [head].
            *)

            (* subst refines head *)
            (* Format.printf "instantiating@." ; *)
            (* Format.printf "%a@." pp_subst residual_subst ; *)
            insert_aux residual_subst subtrees 0
          else (
            (* [subst] has a nontrivial mscg
               - we replace [head] by [general] ([general] generalizes [head])
               - we introduce a new node below the current one labelled by [residual_node]
               - next to the node labelled by [residual_node] we introduce a leaf labelled by [residual_subst] *)
            ti.head <- residual_node ;
            let new_node_children =
              Vec.of_array
                [| ti;
                   { head = residual_subst;
                     subtrees = Vec.create ();
                     data = Some (f None)
                   }
                |]
            in
            let new_node =
              { head = general; subtrees = new_node_children; data = None }
            in
            Vec.set t i new_node ;
            reset residual_node ;
            reset residual_subst)
    in
    tree.root := !term ;
    insert_aux [(tree.root, term)] tree.nodes 0

  module Stats = struct
    let rec max_depth_node node =
      1
      + Vec.fold (fun acc node -> max acc (max_depth_node node)) 0 node.subtrees

    let max_depth index =
      Vec.fold (fun acc node -> max acc (max_depth_node node)) 0 index.nodes

    let rec max_width_node node =
      Vec.fold
        (fun acc node -> max acc (max_width_node node))
        (Vec.length node.subtrees)
        node.subtrees

    let max_width index =
      Vec.fold
        (fun acc node -> max acc (max_width_node node))
        (Vec.length index.nodes)
        index.nodes
  end

  module Internal_for_tests = struct
    module Int_set = Set.Make (Int)

    exception Not_well_scoped of Internal_term.t * Int_set.t

    exception Not_properly_unset

    exception Trivial_subst of subst

    let rec all_unset_node node =
      List.for_all (fun (v, _) -> Internal_term.is_ivar v) node.head
      && Vec.for_all all_unset_node node.subtrees

    let all_unset (index : 'a t) : bool = Vec.for_all all_unset_node index.nodes

    let rec well_scoped_subst subst in_scope acc =
      match subst with
      | [] -> Int_set.union acc in_scope
      | (v, t) :: rest ->
          let t_ivars = Internal_term.ivars t |> List.map (fun r -> r.uid) in
          if not (Int_set.mem v.uid in_scope) then
            raise (Not_well_scoped (v, in_scope))
          else
            let acc = Int_set.union acc (Int_set.of_list t_ivars) in
            well_scoped_subst rest in_scope acc

    let rec well_scoped_node node in_scope =
      let subst = node.head in
      let in_scope = well_scoped_subst subst in_scope Int_set.empty in
      if not (non_trivial subst) then raise (Trivial_subst subst) ;
      Vec.iter (fun node -> well_scoped_node node in_scope) node.subtrees

    let well_scoped index =
      let in_scope = Int_set.singleton index.root.uid in
      Vec.iter (fun node -> well_scoped_node node in_scope) index.nodes

    let check_invariants index =
      well_scoped index ;
      if not (all_unset index) then raise Not_properly_unset ;
      true
  end

  let update term f index = update_subst term f index
  (* ; Internal_for_tests.check_invariants index |> ignore *)

  let insert term data tree =
    update (Internal_term.of_term term) (fun _ -> data) tree

  let rec iter_node f node (root : Internal_term.t) =
    let subst = node.head in
    List.iter (fun (v, t) -> v := !t) subst ;
    (match node.data with None -> () | Some data -> f root data) ;
    Vec.iter (fun node -> iter_node f node root) node.subtrees ;
    reset subst

  let iter f (index : 'a t) =
    Vec.iter (fun node -> iter_node f node index.root) index.nodes

  let copy = Internal_term.copy
end
