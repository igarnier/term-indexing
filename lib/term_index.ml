module Vec = Containers.Vector

let debug_mode = false

(* References equipped with unique integers for debugging/printing purposes *)
module IRef : sig
  type 'a iref

  val ref : 'a -> 'a iref

  val ( ! ) : 'a iref -> 'a

  val ( := ) : 'a iref -> 'a -> unit

  val pp_ref : 'a Fmt.t -> 'a iref Fmt.t

  val uid : 'a iref -> int
end = struct
  type 'a iref = { mutable contents : 'a; uid : int }

  let fresh : unit -> int =
    let counter = ref 0 in
    fun () ->
      let uid = !counter in
      counter := !counter + 1 ;
      uid

  let ref x = { contents = x; uid = fresh () }

  let ( ! ) r = r.contents

  let ( := ) r x = r.contents <- x

  let pp_ref pp_data fmtr r =
    Format.fprintf fmtr "%d=%a" r.uid pp_data r.contents

  let uid r = r.uid
end

module IS = Set.Make (Int)

module Make
    (P : Intf.Signature)
    (T : Intf.Term with type prim = P.t and type t = P.t Term.term)
    (S : Intf.Subst with type term = T.t) : sig
  include
    Intf.Term_index
      with type term = T.t
       and type prim = P.t
       and type subst = S.t

  module Internal_for_tests : sig
    type subst

    val pp_subst : subst Fmt.t

    val of_term : 'a t -> term -> internal_term

    val check_invariants : 'a t -> bool
  end
end = struct
  open IRef

  type term = T.t

  type subst = S.t

  module Internal_term = struct
    type prim = P.t

    type var = int

    type desc =
      | Prim of prim * t array
      | Var of var * t
          (** External (user-inserted) variables. Contains a pointer
              to a representative term to be used during unification.
              It is a free variable if and only if it points to [IVar] or [EVar]. *)
      | IVar  (** Internal variables, used to implement sharing in the tree. *)
      | EVar
          (** Always wrapped in a [Var]. Distinguishes query external variables from
                  non-query external variables. *)

    and t = desc iref

    type var_table = (int, t) Hashtbl.t

    module Pp = struct
      let to_tree term =
        let rec to_tree : IS.t -> t -> PrintBox.t =
         fun set term ->
          if IS.mem (uid term) set then
            Format.kasprintf PrintBox.text "CYCLE(%d)" (uid term)
          else
            let set = IS.add (uid term) set in
            match !term with
            | Prim (prim, subtrees) ->
                PrintBox.tree
                  (Format.kasprintf PrintBox.text "%d:%a" (uid term) P.pp prim)
                  (Array.to_list (Array.map (to_tree set) subtrees))
            | Var (v, repr) ->
                PrintBox.tree
                  (Format.kasprintf PrintBox.text "%d:V(%d)" (uid term) v)
                  [to_tree set repr]
            | IVar -> PrintBox.asprintf "%d:ivar" (uid term)
            | EVar -> PrintBox.asprintf "%d:evar" (uid term)
        in
        to_tree IS.empty term

      let pp fmtr term =
        let tree = to_tree term in
        PrintBox_text.pp fmtr tree
    end

    include Pp

    let uid (t : t) = uid t

    let is_cyclic (term : t) =
      let rec loop : IS.t -> t -> bool =
       fun set term ->
        if IS.mem (uid term) set then true
        else
          let set = IS.add (uid term) set in
          match !term with
          | Var (_, repr) -> (
              match !repr with EVar | IVar -> false | _ -> loop set repr)
          | Prim (_, subtrees) ->
              Array.exists (fun term -> loop set term) subtrees
          | IVar -> false
          | EVar -> assert false
      in
      loop IS.empty term

    let is_ivar (t : t) = match !t with IVar -> true | _ -> false

    let prim p subterms = ref (Prim (p, subterms))

    let reduce fprim fvar term =
      let rec loop fprim fvar visited term =
        match !term with
        | Prim (prim, subterms) ->
            fprim prim (Array.map (loop fprim fvar visited) subterms)
        | Var (v, repr) -> (
            match !repr with
            | IVar | EVar -> fvar v None
            | Prim _ | Var _ ->
                if IS.mem (uid repr) visited then fvar v (Some repr)
                else fvar v None)
        | IVar | EVar -> assert false
      in
      loop fprim fvar IS.empty term

    let destruct fprim fvar (term : t) =
      match !term with
      | Prim (prim, subterms) -> fprim prim subterms
      | Var (v, repr) -> (
          match !repr with
          | IVar | EVar -> fvar v None
          | Prim _ | Var _ -> fvar v (Some repr))
      | IVar | EVar -> assert false

    (* Precondition: input is a [Var]
       Postcondition: returns the representative term and the variable *)
    let rec get_repr (var : t) =
      match !var with
      | Var (_, repr) -> (
          match !repr with
          | IVar | EVar | Prim _ -> (repr, var)
          | Var (_, _) -> get_repr repr)
      | IVar | EVar | Prim _ -> assert false

    let ivars term =
      let rec loop term acc =
        match !term with
        | Var _ -> acc
        | Prim (_, subterms) ->
            Array.fold_left (fun acc term -> loop term acc) acc subterms
        | IVar -> term :: acc
        | EVar -> assert false
      in
      loop term []

    let rec of_term : var_table -> T.t -> t =
     fun table term ->
      match term.Hashcons.node with
      | Term.Var v -> (
          match Hashtbl.find_opt table v with
          | None ->
              (* Note that the [desc_ptr] is shared among all variables. *)
              let desc_ptr = ref IVar in
              Hashtbl.add table v desc_ptr ;
              ref (Var (v, desc_ptr))
          | Some desc_ptr -> ref (Var (v, desc_ptr)))
      | Term.Prim (p, subtrees, _) ->
          let subtrees = Array.map (fun t -> of_term table t) subtrees in
          prim p subtrees

    let to_term term =
      let rec to_term : IS.t -> t -> T.t =
       fun set term ->
        let set =
          if IS.mem (uid term) set then invalid_arg "cyclic term"
          else IS.add (uid term) set
        in
        match !term with
        | Var (v, _repr) -> T.var v
        | Prim (p, subtrees) ->
            let subtrees = Array.map (to_term set) subtrees in
            T.prim p subtrees
        | IVar | EVar -> assert false
      in
      to_term IS.empty term

    let get_subst : t -> S.t =
      let rec loop : S.t -> t -> S.t =
       fun subst term ->
        match !term with
        | Var (v, repr) -> (
            match !repr with
            | IVar | EVar -> subst
            | Prim _ | Var _ ->
                if S.eval v subst |> Option.is_some then subst
                else S.add v (to_term repr) subst)
        | Prim (_, subtrees) -> Array.fold_left loop subst subtrees
        | IVar -> subst
        | EVar -> assert false
      in
      fun term -> loop (S.empty ()) term
  end

  type internal_term = Internal_term.t

  type prim = P.t

  let is_cyclic = Internal_term.is_cyclic

  let to_term = Internal_term.to_term

  let get_subst = Internal_term.get_subst

  let reduce = Internal_term.reduce

  let destruct = Internal_term.destruct

  let pp_internal_term = Internal_term.pp

  type iref = internal_term

  type isubst = (iref * internal_term) list

  type 'a node =
    { mutable head : isubst;
      mutable subtrees : 'a node Vec.vector;
      mutable data : 'a option
    }

  type 'a t =
    { nodes : 'a node Vec.vector;  (** [nodes] is the first layer of trees *)
      root : internal_term;
          (** [root] is set to [IVar] outside of insertion or lookup operations.
              It is set to the term being inserted or the query term otherwise. *)
      var_table : Internal_term.var_table
          (** A table used during lookup operations *)
    }

  module Pp = struct
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
                hlist [Internal_term.Pp.to_tree v; Internal_term.Pp.to_tree t])
              subst)

    let box_of_subst_with_data pp_data subst data =
      let open PrintBox in
      frame
      @@ hlist
           [ vlist
               ~bars:true
               (List.map
                  (fun (v, t) ->
                    hlist
                      [Internal_term.Pp.to_tree v; Internal_term.Pp.to_tree t])
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
  end

  let pp = Pp.pp

  let pp_subst = Pp.pp_subst

  let of_term index term = Internal_term.of_term index.var_table term

  let subst_is_empty = function [] -> true | _ -> false

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
     appear in the domain of both [residual_subst] and [residual_node] *)
  let rec mscg (subst_term : internal_term) (node_term : internal_term)
      (residual_subst : isubst) (residual_node : isubst) : isubst * isubst =
    match (!subst_term, !node_term) with
    | (Prim (prim1, args1), Prim (prim2, args2)) ->
        if P.equal prim1 prim2 then
          mscg_array args1 args2 residual_subst residual_node 0
        else generalize subst_term node_term residual_subst residual_node
    | (Var (v1, _), Var (v2, _)) ->
        if Int.equal v1 v2 then (residual_subst, residual_node)
        else generalize subst_term node_term residual_subst residual_node
    | (Var _, Prim _) | (Prim _, Var _) ->
        generalize subst_term node_term residual_subst residual_node
    | (IVar, _) -> assert false
    | ((Prim _ | Var _), IVar) ->
        (* [t1] is a variable or term, [t2] is an indicator variable *)
        (* [node_term] is already the mscg *)
        ((node_term, subst_term) :: residual_subst, residual_node)
    | (EVar, _) | (_, EVar) -> assert false

  and mscg_array args1 args2 residual_subst residual_node i =
    if i = Array.length args1 then (residual_subst, residual_node)
    else
      let (residual_subst, residual_node) =
        mscg args1.(i) args2.(i) residual_subst residual_node
      in
      mscg_array args1 args2 residual_subst residual_node (i + 1)

  let top_symbol_disagree (t1 : internal_term) (t2 : internal_term) =
    match (!t1, !t2) with
    | (Prim (prim1, _), Prim (prim2, _)) -> not (P.equal prim1 prim2)
    | (Var (v1, _), Var (v2, _)) -> not (Int.equal v1 v2)
    | (Prim _, Var _) | (Var _, Prim _) -> true
    | (EVar, _) | (_, EVar) ->
        (* EVar can only appear under a Var *)
        assert false
    | (IVar, IVar) ->
        (* Cannot have a pair of free variables in a head subst during insertion *)
        assert false
    | (Prim _, IVar) | (Var _, IVar) | (IVar, Prim _) | (IVar, Var _) ->
        (* IVar can be instantiated *)
        false

  let create () =
    { nodes = Vec.create ();
      root = ref Internal_term.IVar;
      var_table = Hashtbl.create 11
    }

  let reset subst = List.iter (fun (v, _) -> v := Internal_term.IVar) subst

  (* Note: [update_subst] is not robust to sharing sub-terms across inserted terms. *)
  let update_subst term f (tree : 'a t) =
    let rec insert_aux (subst : isubst) (t : 'a node Vec.vector) i =
      (* Precondition: domain of [subst] is set *)
      (* Postcondition: domain of [subst] is unset *)
      (* Postcondition: domain of [(Vec.get t i).head] is unset *)
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
        (*
           At this point:
           - subst = residual_subst \circ general
           - head  = residual_node \circ general
           - bindings in [general] are of the form [(IVar, t)] where [t != IVar]
           - bindings in [head] that were mapped in [subst] are of the form [(IVar, t)]
         *)
        let () =
          if debug_mode then (
            assert (
              List.for_all
                (fun (v, t) ->
                  Internal_term.is_ivar v && not (Internal_term.is_ivar t))
                general) ;

            assert (
              List.for_all
                (fun (v, t) ->
                  Internal_term.is_ivar v && not (Internal_term.is_ivar t))
                head))
          else ()
        in

        if subst_is_empty general then (
          (* [subst] is incompatible with [head], try next sibling
             TODO: we might optimize the search by indexing trees by their head constructor
             for a particular variable. This is reminiscent of a trie. The heuristic to choose
             which variable to split would be crucial. *)

          (* subst = residual_subst
             re-establish pre-condition for recursive call by reverting the
             state of variables in domain of [partial_residual_subst] *)
          List.iter (fun (v, t) -> v := !t) partial_residual_subst ;
          insert_aux subst t (i + 1))
        else
          let residual_subst =
            List.fold_left
              (fun residual_subst ((v, _t) as binding) ->
                if not (Internal_term.is_ivar v) then binding :: residual_subst
                else residual_subst)
              partial_residual_subst
              subst
          in
          let () = List.iter (fun (v, t) -> v := !t) residual_subst in
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
    [@@@ocaml.warning "-32"]

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
    type subst = isubst

    let pp_subst = pp_subst

    exception Not_well_scoped of internal_term * IS.t

    exception Not_properly_unset

    exception Trivial_subst of subst

    let rec all_unset_node node =
      List.for_all (fun (v, _) -> Internal_term.is_ivar v) node.head
      && Vec.for_all all_unset_node node.subtrees

    let all_unset (index : 'a t) : bool = Vec.for_all all_unset_node index.nodes

    let non_trivial subst =
      not (List.exists (fun (_v, t) -> Internal_term.is_ivar t) subst)

    let rec well_scoped_subst subst in_scope acc =
      match subst with
      | [] -> IS.union acc in_scope
      | (v, t) :: rest ->
          let t_ivars = Internal_term.ivars t |> List.map (fun r -> uid r) in
          if not (IS.mem (uid v) in_scope) then
            raise (Not_well_scoped (v, in_scope))
          else
            let acc = IS.union acc (IS.of_list t_ivars) in
            well_scoped_subst rest in_scope acc

    let rec well_scoped_node node in_scope =
      let subst = node.head in
      let in_scope = well_scoped_subst subst in_scope IS.empty in
      if not (non_trivial subst) then raise (Trivial_subst subst) ;
      Vec.iter (fun node -> well_scoped_node node in_scope) node.subtrees

    let well_scoped index =
      let in_scope = IS.singleton (uid index.root) in
      Vec.iter (fun node -> well_scoped_node node in_scope) index.nodes

    let check_invariants index =
      well_scoped index ;
      if not (all_unset index) then raise Not_properly_unset ;
      true

    let of_term = of_term
  end

  let update term f index = update_subst term f index

  let insert term data tree =
    update (Internal_term.of_term tree.var_table term) (fun _ -> data) tree

  let update term f tree =
    update (Internal_term.of_term tree.var_table term) f tree

  (*
     TODO: could implement substitutions as pair of vectors
   *)

  module Unifiable_query = struct
    let rec unify undo_stack (term1 : internal_term) (term2 : internal_term) =
      match (!term1, !term2) with
      | (Prim (prim1, args1), Prim (prim2, args2)) ->
          if P.equal prim1 prim2 then unify_arrays undo_stack args1 args2 0
          else (undo_stack, false)
      | (Var (_, repr_ptr1), Var (_, repr_ptr2)) -> (
          if repr_ptr1 == repr_ptr2 then (undo_stack, true)
          else
            (* term1, term2 are [Var], hence precondition of [get_repr] is satisfied *)
            let (repr1, root_var1) = Internal_term.get_repr term1 in
            let (repr2, root_var2) = Internal_term.get_repr term2 in
            (* invariant: root_var1, root_var2 are Var pointing to Prim or IVar *)
            match (!repr1, !repr2) with
            | (Prim _, Prim _) -> unify undo_stack repr1 repr2
            | (Prim _, ((IVar | EVar) as desc2)) ->
                (* let term2 point to term1 *)
                repr2 := !root_var1 ;
                ((repr2, desc2) :: undo_stack, true)
            | (((IVar | EVar) as desc1), Prim _) ->
                (* let term1 point to term2 *)
                repr1 := !root_var2 ;
                ((repr1, desc1) :: undo_stack, true)
            | (((IVar | EVar) as desc1), (IVar | EVar)) ->
                (* It may be the case that root_var1 == root_var2, if we
                   perform the assignment then we'll introduce a cycle. *)
                if repr1 == repr2 then (undo_stack, true)
                else (
                  repr1 := !root_var2 ;
                  ((repr1, desc1) :: undo_stack, true))
            | (Var _, _) | (_, Var _) ->
                (* Impossible case *)
                assert false)
      | (Var (_, _), Prim _) -> (
          let (repr, _root_var) = Internal_term.get_repr term1 in
          match !repr with
          | (IVar | EVar) as desc ->
              repr := !term2 ;
              ((repr, desc) :: undo_stack, true)
          | Prim _ -> unify undo_stack repr term2
          | Var _ ->
              (* Impossible case *)
              assert false)
      | (Prim _, Var (_, _)) -> (
          let (repr, _root_var) = Internal_term.get_repr term2 in
          match !repr with
          | (IVar | EVar) as desc ->
              repr := !term1 ;
              ((repr, desc) :: undo_stack, true)
          | Prim _ -> unify undo_stack term1 repr
          | Var _ ->
              (* Impossible case *)
              assert false)
      | (IVar, ((Prim _ | Var _) as desc2)) ->
          term1 := desc2 ;
          ((term1, Internal_term.IVar) :: undo_stack, true)
      | (((Prim _ | Var _) as desc1), IVar) ->
          term2 := desc1 ;
          ((term2, IVar) :: undo_stack, true)
      | (IVar, IVar) ->
          (* The value of the variable does not matter. *)
          let fresh = Internal_term.(Var (-1, ref IVar)) in
          term1 := fresh ;
          term2 := fresh ;
          ((term1, IVar) :: (term2, IVar) :: undo_stack, true)
      | (EVar, _) | (_, EVar) -> assert false

    and unify_arrays undo_stack args1 args2 i =
      if i = Array.length args1 then (undo_stack, true)
      else
        let (undo_stack, success) = unify undo_stack args1.(i) args2.(i) in
        if success then unify_arrays undo_stack args1 args2 (i + 1)
        else (undo_stack, false)

    let rec unification_subst undo_stack subst =
      match subst with
      | [] -> (undo_stack, true)
      | (v, t) :: rest ->
          let (undo_stack, success) = unify undo_stack v t in
          if success then (
            let desc = !v in
            v := !t ;
            let undo_stack = (v, desc) :: undo_stack in
            unification_subst undo_stack rest)
          else (undo_stack, false)
  end

  let rec check_equality undo_stack (term1 : internal_term)
      (term2 : internal_term) =
    match (!term1, !term2) with
    | (Prim (prim1, args1), Prim (prim2, args2)) ->
        if P.equal prim1 prim2 then
          check_equality_arrays undo_stack args1 args2 0
        else (undo_stack, false)
    | (Var (_, repr1), Var (_, repr2)) ->
        if repr1 == repr2 then (undo_stack, true) else (undo_stack, false)
    | (Var (_, _), Prim _) -> (undo_stack, false)
    | (Prim _, Var (_, _)) -> (undo_stack, false)
    | (IVar, ((Prim _ | Var _) as desc2)) ->
        term1 := desc2 ;
        ((term1, Internal_term.IVar) :: undo_stack, true)
    | (((Prim _ | Var _) as desc1), IVar) ->
        term2 := desc1 ;
        ((term2, IVar) :: undo_stack, true)
    | (IVar, IVar) ->
        (* The value of the variable does not matter. *)
        let fresh = Internal_term.(Var (-1, ref IVar)) in
        term1 := fresh ;
        term2 := fresh ;
        ((term1, IVar) :: (term2, IVar) :: undo_stack, true)
    | (EVar, _) | (_, EVar) -> assert false

  and check_equality_arrays undo_stack args1 args2 i =
    if i = Array.length args1 then (undo_stack, true)
    else
      let (undo_stack, success) =
        check_equality undo_stack args1.(i) args2.(i)
      in
      if success then check_equality_arrays undo_stack args1 args2 (i + 1)
      else (undo_stack, false)

  module Specialize_query = struct
    let rec check_specialize undo_stack (term1 : internal_term)
        (term2 : internal_term) =
      match (!term1, !term2) with
      | (Prim (prim1, args1), Prim (prim2, args2)) ->
          if P.equal prim1 prim2 then
            check_specialize_arrays undo_stack args1 args2 0
          else (undo_stack, false)
      | (Var (_, repr1), Var (_, repr2)) -> (
          match !repr1 with
          | EVar ->
              (* Variable not instantiated; instantiate it with term2.
                 Two cases:
                 - [term1] belongs to the query term and [term2] belongs to the index.
                   In this case, mapping [term1] to [term2] is exactly what we want.
                 - [term1] belongs to the index and [term2] as well.
                   Since [repr1] is an unset [EVar], it must be the case that
                   the same variable is present in the query term.
                   If the check succeeds, it will necessarily be the case that
                   this variable is successfully checked against a term in the index.
                   The cases are:
              *)
              repr1 := !term2 ;
              ((repr1, Internal_term.EVar) :: undo_stack, true)
          | IVar ->
              (* non-query variables can't be instantiated when specializing *)
              (undo_stack, false)
          | Prim _ ->
              (* Variable already instantiated with a prim, cannot specialize
                 to another variable. *)
              (undo_stack, false)
          | Var (_, repr1') ->
              (* Variable was was already mapped to a term variable, check equality. *)
              (undo_stack, repr1' == repr2))
      | (Var (_, repr), Prim _) -> (
          match !repr with
          | EVar ->
              (* Variable not instantiated; instantiate it with term2. *)
              repr := !term2 ;
              ((repr, Internal_term.EVar) :: undo_stack, true)
          | IVar ->
              (* non-query variables can't be instantiated when specializing *)
              (undo_stack, false)
          | Prim _ ->
              (* Variable was already instantiated with a prim, check
                 that instances properly specialize. Note that [repr] is not
                 a query term and may contain [IVar] and [Var] nodes. *)
              check_equality undo_stack repr term2
          | Var _ ->
              (* Variable was was already mapped to a term variable *)
              (undo_stack, false))
      | (Prim _, Var (_, _)) -> (undo_stack, false)
      | (IVar, ((Prim _ | Var _) as desc2)) ->
          term1 := desc2 ;
          ((term1, IVar) :: undo_stack, true)
      | (IVar, IVar) ->
          (* The value of the variable does not matter. *)
          let fresh = Internal_term.(Var (-1, ref IVar)) in
          term1 := fresh ;
          term2 := fresh ;
          ((term1, IVar) :: (term2, IVar) :: undo_stack, true)
      | (((Prim _ | Var _) as desc1), IVar) ->
          term2 := desc1 ;
          ((term2, IVar) :: undo_stack, true)
      | (EVar, _) | (_, EVar) -> assert false

    and check_specialize_arrays undo_stack args1 args2 i =
      if i = Array.length args1 then (undo_stack, true)
      else
        let (undo_stack, success) =
          check_specialize undo_stack args1.(i) args2.(i)
        in
        if success then check_specialize_arrays undo_stack args1 args2 (i + 1)
        else (undo_stack, false)

    let rec check_specialize_subst undo_stack subst =
      match subst with
      | [] -> (undo_stack, true)
      | (v, t) :: rest ->
          let (undo_stack, success) = check_specialize undo_stack v t in
          if success then (
            let desc = !v in
            v := !t ;
            let undo_stack = (v, desc) :: undo_stack in
            check_specialize_subst undo_stack rest)
          else (undo_stack, false)
  end

  module Generalize_query = struct
    let rec check_generalize undo_stack (term1 : internal_term)
        (term2 : internal_term) =
      match (!term1, !term2) with
      | (Prim (prim1, args1), Prim (prim2, args2)) ->
          if P.equal prim1 prim2 then
            check_generalize_arrays undo_stack args1 args2 0
          else (undo_stack, false)
      | (Var (_, repr1), Var (_, repr2)) -> (
          match !repr2 with
          | (IVar | EVar) as desc2 ->
              (* Variable not instantiated; instantiate it with term1. *)
              (* Note that cycles may be introduced here. It's fine. *)
              repr2 := !term1 ;
              ((repr2, desc2) :: undo_stack, true)
          | Prim _ ->
              (* Variable already instantiated with a prim, cannot generalize
                 to a distinct variable. *)
              (undo_stack, false)
          | Var (_, repr2') ->
              (* Variable was was already mapped to a term variable, check equality. *)
              (undo_stack, repr2' == repr1))
      | (Prim _, Var (_, repr)) -> (
          match !repr with
          | (IVar | EVar) as desc ->
              (* Variable not instantiated; instantiate it with term1. *)
              repr := !term1 ;
              ((repr, desc) :: undo_stack, true)
          | Prim _ ->
              (* Variable was already instantiated with a prim, check equalitye.*)
              check_equality undo_stack term1 repr
          | Var _ ->
              (* Variable was was already mapped to a query variable. *)
              (undo_stack, false))
      | (Var (_, _), Prim _) -> (undo_stack, false)
      | (IVar, ((Prim _ | Var _) as desc2)) ->
          term1 := desc2 ;
          ((term1, IVar) :: undo_stack, true)
      | (IVar, IVar) ->
          (* The value of the variable does not matter. *)
          let fresh = Internal_term.(Var (-1, ref IVar)) in
          term1 := fresh ;
          term2 := fresh ;
          ((term1, IVar) :: (term2, IVar) :: undo_stack, true)
      | (((Prim _ | Var _) as desc1), IVar) ->
          term2 := desc1 ;
          ((term2, IVar) :: undo_stack, true)
      | (EVar, _) | (_, EVar) -> assert false

    and check_generalize_arrays undo_stack args1 args2 i =
      if i = Array.length args1 then (undo_stack, true)
      else
        let (undo_stack, success) =
          check_generalize undo_stack args1.(i) args2.(i)
        in
        if success then check_generalize_arrays undo_stack args1 args2 (i + 1)
        else (undo_stack, false)

    let rec check_generalize_subst undo_stack subst =
      match subst with
      | [] -> (undo_stack, true)
      | (v, t) :: rest ->
          let (undo_stack, success) = check_generalize undo_stack v t in
          if success then (
            let desc = !v in
            v := !t ;
            let undo_stack = (v, desc) :: undo_stack in
            check_generalize_subst undo_stack rest)
          else (undo_stack, false)
  end

  let rec iter_node f node (root : internal_term) =
    let subst = node.head in
    List.iter (fun (v, t) -> v := !t) subst ;
    (match node.data with None -> () | Some data -> f root data) ;
    Vec.iter (fun node -> iter_node f node root) node.subtrees ;
    reset subst

  let iter_transient f (index : 'a t) =
    Vec.iter (fun node -> iter_node f node index.root) index.nodes

  let iter f index = iter_transient (fun term v -> f (to_term term) v) index

  type query_kind = Unifiable | Specialize | Generalize

  let _pp_query_kind fmtr = function
    | Unifiable -> Fmt.string fmtr "Unifiable"
    | Specialize -> Fmt.string fmtr "Specialize"
    | Generalize -> Fmt.string fmtr "Generalize"

  (* precondition: the domain of node.head has no [IVar] *)
  let rec iter_query_node f node root qkind =
    let (undo_stack, success) =
      match qkind with
      | Unifiable -> Unifiable_query.unification_subst [] node.head
      | Specialize -> Specialize_query.check_specialize_subst [] node.head
      | Generalize -> Generalize_query.check_generalize_subst [] node.head
    in
    if success then (
      (match node.data with None -> () | Some data -> f root data) ;
      Vec.iter (fun node -> iter_query_node f node root qkind) node.subtrees)
    else () ;
    List.iter (fun (v, d) -> v := d) undo_stack

  let iter_query f (index : 'a t) (qkind : query_kind) (query : internal_term) =
    (* [query] is either a Prim or a Var. *)
    index.root := !query ;
    (* The toplevel substitution of the index has domain equal to [index.root]. *)
    Vec.iter (fun node -> iter_query_node f node index.root qkind) index.nodes ;
    index.root := IVar

  let iter_unifiable_transient f index query =
    iter_query f index Unifiable (of_term index query)

  let iter_unifiable f index =
    iter_unifiable_transient (fun term v -> f (to_term term) v) index

  let rec set_query_variables acc (term : Internal_term.t) =
    match !term with
    | Var (_, repr) ->
        repr := EVar ;
        (repr, Internal_term.IVar) :: acc
    | Prim (_, args) -> Array.fold_left set_query_variables acc args
    | IVar -> acc
    | EVar -> assert false

  let iter_specialize_transient f index query =
    let query_term = of_term index query in
    let undo = set_query_variables [] query_term in
    iter_query f index Specialize query_term ;
    List.iter (fun (v, d) -> v := d) undo

  let iter_specialize f index =
    iter_specialize_transient (fun term v -> f (to_term term) v) index

  let iter_generalize_transient f index query =
    let query_term = of_term index query in
    let undo = set_query_variables [] query_term in
    iter_query f index Generalize (of_term index query) ;
    List.iter (fun (v, d) -> v := d) undo

  let iter_generalize f index =
    iter_generalize_transient (fun term v -> f (to_term term) v) index
end
