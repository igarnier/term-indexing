module Vec = Containers.Vector

let debug_mode = false

module IS = Set.Make (Int)
module PB = PrintBox

module Make
    (P : Intf.Signature)
    (T : sig
      type prim = P.t

      type t

      type var := int

      (** [destruct ifprim ifvar t] performs case analysis on the term [t] *)
      val destruct : (prim -> t array -> 'a) -> (var -> 'a) -> t -> 'a

      (** [prim p ts] constructs a term with head equal to [p] and subterms equal to [ts]

      Raises [Invalid_argument] if the length of [ts] does not match the arity of [p]. *)
      val prim : prim -> t array -> t

      (** [var v] construcst a variable [v] *)
      val var : var -> t
    end) : sig
  include Intf.Term_index with type term = T.t and type prim = P.t

  module Internal_for_tests : sig
    type subst

    val pp_subst : subst Fmt.t

    val of_term : 'a t -> term -> iterm

    val check_invariants : 'a t -> bool
  end
end = struct
  type term = T.t

  type prim = P.t

  type desc = Prim of prim * iterm array | Var of int * iterm | IVar | EVar

  and iterm = { mutable desc : desc; uid : int }

  type var_table = (int, iterm) Hashtbl.t

  module Subst : sig
    type t

    val empty : unit -> t

    val is_empty : t -> bool

    val push : iterm -> iterm -> t -> t

    val reset : t -> unit

    val assign : t -> unit

    val fold : ('a -> iterm -> iterm -> 'a) -> 'a -> t -> 'a

    val for_all : (iterm -> iterm -> bool) -> t -> bool

    val iter_while : (iterm -> iterm -> bool) -> t -> bool

    val to_bindings : t -> (iterm * iterm) list
  end = struct
    type t = (iterm * iterm) list

    let empty () = []

    let is_empty = function [] -> true | _ -> false

    let push v t subst = (v, t) :: subst

    let reset subst = List.iter (fun (v, _) -> v.desc <- IVar) subst

    let assign subst = List.iter (fun (v, t) -> v.desc <- t.desc) subst

    let fold f acc subst =
      List.fold_left (fun acc (v, t) -> f acc v t) acc subst

    let for_all f subst = List.for_all (fun (v, t) -> f v t) subst

    let rec iter_while f subst =
      match subst with
      | [] -> true
      | (v, t) :: rest -> if f v t then iter_while f rest else false

    let to_bindings = Fun.id
  end

  type 'a node =
    | Node of { mutable head : Subst.t; subtrees : 'a node Vec.vector }
    | Leaf of { mutable head : Subst.t; mutable data : 'a }

  let head = function Node { head; _ } | Leaf { head; _ } -> head

  let[@ocaml.inline always] set_head node head =
    match node with
    | Node node -> node.head <- head
    | Leaf node -> node.head <- head

  type 'a t =
    { nodes : 'a node Vec.vector;  (** [nodes] is the first layer of trees *)
      root : iterm;
          (** [root] is set to [IVar] outside of insertion or lookup operations.
              It is set to the term being inserted or the query term otherwise. *)
      var_table : var_table  (** A table used during lookup operations *)
    }

  let uid { uid; _ } = uid

  let fresh : unit -> int =
    let counter = ref 0 in
    fun () ->
      let uid = !counter in
      counter := !counter + 1 ;
      uid

  let make desc = { uid = fresh (); desc }

  module Pp = struct
    let iterm_to_print_tree term =
      let rec to_tree : IS.t -> iterm -> PB.t =
       fun set term ->
        if IS.mem (uid term) set then
          Format.kasprintf PB.text "CYCLE(%d)" (uid term)
        else
          let set = IS.add (uid term) set in
          match term.desc with
          | Prim (prim, subtrees) ->
              PB.tree
                (Format.kasprintf PB.text "%d:%a" (uid term) P.pp prim)
                (Array.to_list (Array.map (to_tree set) subtrees))
          | Var (v, repr) ->
              PB.tree
                (Format.kasprintf PB.text "%d:V(%d)" (uid term) v)
                [to_tree set repr]
          | IVar -> PB.asprintf "%d:ivar" (uid term)
          | EVar -> PB.asprintf "%d:evar" (uid term)
      in
      to_tree IS.empty term

    let pp_iterm fmtr term =
      let tree = iterm_to_print_tree term in
      PrintBox_text.pp fmtr tree

    let box_of_data pp_data data =
      let open PB in
      text (Format.asprintf "%a" pp_data data)

    let box_of_subst subst =
      let open PB in
      frame
      @@ vlist
           ~bars:true
           (List.map
              (fun (v, t) ->
                hlist [iterm_to_print_tree v; iterm_to_print_tree t])
              (Subst.to_bindings subst))

    let box_of_subst_with_data pp_data subst data =
      let open PB in
      frame
      @@ hlist
           [ vlist
               ~bars:true
               (List.map
                  (fun (v, t) ->
                    hlist [iterm_to_print_tree v; iterm_to_print_tree t])
                  (Subst.to_bindings subst));
             box_of_data pp_data data ]

    let pp_subst fmtr subst = PrintBox_text.pp fmtr (box_of_subst subst)

    let rec to_box pp_data node =
      let open PB in
      match node with
      | Node node ->
          tree
            ~indent:4
            (hlist
               [ box_of_subst node.head;
                 text (string_of_int (Vec.length node.subtrees)) ])
            (List.map (to_box pp_data) (Vec.to_list node.subtrees))
      | Leaf node -> box_of_subst_with_data pp_data node.head node.data

    and box_of_subtrees pp_data vec =
      let open PB in
      align
        ~h:`Center
        ~v:`Center
        (hlist (List.map (to_box pp_data) (Vec.to_list vec)))

    let pp pp_data fmtr tree =
      PrintBox_text.pp fmtr (box_of_subtrees pp_data tree.nodes)
  end

  let pp = Pp.pp

  let pp_iterm = Pp.pp_iterm

  let pp_subst = Pp.pp_subst

  let is_cyclic (term : iterm) =
    let rec loop : IS.t -> iterm -> bool =
     fun set term ->
      if IS.mem (uid term) set then true
      else
        let set = IS.add (uid term) set in
        match term.desc with
        | Var (_, repr) -> (
            match repr.desc with EVar | IVar -> false | _ -> loop set repr)
        | Prim (_, subtrees) ->
            Array.exists (fun term -> loop set term) subtrees
        | IVar -> false
        | EVar -> assert false
    in
    loop IS.empty term

  let is_ivar (t : iterm) = match t.desc with IVar -> true | _ -> false

  let prim p subterms = make (Prim (p, subterms))

  let reduce fprim fvar term =
    let rec loop fprim fvar visited term =
      match term.desc with
      | Prim (prim, subterms) ->
          fprim prim (Array.map (loop fprim fvar visited) subterms)
      | Var (v, repr) -> (
          match repr.desc with
          | IVar | EVar -> fvar v None
          | Prim _ | Var _ ->
              if IS.mem (uid repr) visited then fvar v (Some repr)
              else fvar v None)
      | IVar | EVar -> assert false
    in
    loop fprim fvar IS.empty term

  let destruct fprim fvar term =
    match term.desc with
    | Prim (prim, subterms) -> fprim prim subterms
    | Var (v, repr) -> (
        match repr.desc with
        | IVar | EVar -> fvar v None
        | Prim _ | Var _ -> fvar v (Some repr))
    | IVar | EVar -> assert false

  (* Precondition: input is a [Var]
     Postcondition: returns the representative term and the variable *)
  let rec get_repr var =
    match var.desc with
    | Var (_, repr) -> (
        match repr.desc with
        | IVar | EVar | Prim _ -> (repr, var)
        | Var (_, _) -> get_repr repr)
    | IVar | EVar | Prim _ -> assert false

  let ivars term =
    let rec loop term acc =
      match term.desc with
      | Var _ -> acc
      | Prim (_, subterms) ->
          Array.fold_left (fun acc term -> loop term acc) acc subterms
      | IVar -> term :: acc
      | EVar -> assert false
    in
    loop term []

  let rec iterm_of_term : var_table -> T.t -> iterm =
   fun table term ->
    T.destruct
      (fun p subtrees ->
        let subtrees = Array.map (fun t -> iterm_of_term table t) subtrees in
        prim p subtrees)
      (fun v ->
        match Hashtbl.find_opt table v with
        | None ->
            (* Note that the [desc_ptr] is shared among all variables. *)
            let desc_ptr = make IVar in
            Hashtbl.add table v desc_ptr ;
            make (Var (v, desc_ptr))
        | Some desc_ptr -> make (Var (v, desc_ptr)))
      term

  let to_term term =
    let rec to_term : IS.t -> iterm -> T.t =
     fun set term ->
      let set =
        if IS.mem (uid term) set then invalid_arg "cyclic term"
        else IS.add (uid term) set
      in
      match term.desc with
      | Var (v, _repr) -> T.var v
      | Prim (p, subtrees) ->
          let subtrees = Array.map (to_term set) subtrees in
          T.prim p subtrees
      | IVar | EVar -> assert false
    in
    to_term IS.empty term

  let rec fold_subst f term acc =
    match term.desc with
    | Var (v, repr) -> (
        match repr.desc with
        | IVar | EVar -> acc
        | Prim _ | Var _ -> f v repr acc)
    | Prim (_, subtrees) ->
        Array.fold_left (fun acc term -> fold_subst f term acc) acc subtrees
    | IVar -> acc
    | EVar -> assert false

  let of_term index term = iterm_of_term index.var_table term

  let generalize subst_term node_term residual_subst residual_node =
    let residual_subst = Subst.push node_term subst_term residual_subst in
    (* We need to wrap the term pointed to by [node_term] in a fresh ref cell;
       [node_term] will be pointing to either the [subst_term] or the fresh cell
       depending on which term is matched. *)
    let residual_node =
      Subst.push node_term (make node_term.desc) residual_node
    in
    node_term.desc <- IVar ;
    (residual_subst, residual_node)

  (* [mscg subst_term node_term residual_subst residual_node] destructively updates
     [node_term] to correspond to the most specific common generalization of
     [subst_term] and [node_term]. Both remainders are added to the residuals.

     Pre-condition: [subst_term] contains no [IVar]
     Post-condition: generalized sub-terms of [node_term] are set to [IVar] and
     appear in the domain of both [residual_subst] and [residual_node] *)
  let rec mscg (subst_term : iterm) (node_term : iterm)
      (residual_subst : Subst.t) (residual_node : Subst.t) : Subst.t * Subst.t =
    match (subst_term.desc, node_term.desc) with
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
        (Subst.push node_term subst_term residual_subst, residual_node)
    | (EVar, _) | (_, EVar) -> assert false

  and mscg_array args1 args2 residual_subst residual_node i =
    if i = Array.length args1 then (residual_subst, residual_node)
    else
      let (residual_subst, residual_node) =
        mscg args1.(i) args2.(i) residual_subst residual_node
      in
      mscg_array args1 args2 residual_subst residual_node (i + 1)

  let top_symbol_disagree (t1 : iterm) (t2 : iterm) =
    match (t1.desc, t2.desc) with
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
    { nodes = Vec.create (); root = make IVar; var_table = Hashtbl.create 11 }

  module Scope = struct
    type undo_item = Undo of iterm * desc

    type t = { mutable undo : undo_item list }

    let make () = { undo = [] }

    let apply_undo handle =
      List.iter (fun (Undo (term, desc)) -> term.desc <- desc) handle.undo ;
      handle.undo <- []

    let set_desc handle term desc =
      let prev_desc = term.desc in
      handle.undo <- Undo (term, prev_desc) :: handle.undo ;
      term.desc <- desc
    [@@ocaml.inline]

    let undo_scope f =
      let handle = make () in
      let finalize () = apply_undo handle in
      match f handle with
      | res ->
          finalize () ;
          res
      | exception exn ->
          finalize () ;
          raise exn
    [@@ocaml.inline]
  end

  (* Note: [update_subst] is not robust to sharing sub-terms across inserted terms. *)
  let update_subst term f (tree : 'a t) =
    let rec insert_aux (subst : Subst.t) (t : 'a node Vec.vector) i =
      (* Precondition: domain of [subst] is set *)
      (* Postcondition: domain of [subst] is unset *)
      (* Postcondition: domain of [(Vec.get t i).head] is unset *)
      if i >= Vec.length t then (
        (* Format.printf "End of vector@." ; *)
        Vec.push t (Leaf { head = subst; data = f None }) ;
        Subst.reset subst)
      else
        let ti = Vec.get t i in
        (* let ({ head; subtrees; data = _ } as ti) = Vec.get t i in *)
        let undo_frame = Scope.make () in
        let (general, partial_residual_subst, residual_node) =
          Subst.fold
            (fun (general, residual_subst, residual_node) v t ->
              (*
                  the pair [(v, t)] is a pair of references to term descriptors:
                    v = ref desc1
                    t = ref desc2
                  By assumption [v] is either the root of the index, or appears as a [IVar] subterm
                  in the right-hand side of a substitution stored in the index. During insertion,
                  this [IVar] may be set to a subterm to be matched against [t], which points to a term
                  that appeared in the position of [v] in one previously inserted term.
                *)
              assert (not (is_ivar t)) ;
              if is_ivar v then
                (* variable is unset hence not in domain of [subst], binding goes to [residual_node] *)
                (general, residual_subst, Subst.push v t residual_node)
              else if top_symbol_disagree v t then (
                (* Toplevel mismatch. *)
                let desc = v.desc in
                Scope.set_desc undo_frame v IVar ;
                ( general,
                  Subst.push v (make desc) residual_subst,
                  Subst.push v t residual_node ))
              else
                let (residual_subst, residual_node) =
                  mscg v t residual_subst residual_node
                in
                let () = assert (not (is_ivar t)) in
                v.desc <- IVar ;
                (Subst.push v t general, residual_subst, residual_node))
            (Subst.empty (), Subst.empty (), Subst.empty ())
            (head ti)
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
              Subst.for_all (fun v t -> is_ivar v && not (is_ivar t)) general) ;
            assert (
              Subst.for_all (fun v t -> is_ivar v && not (is_ivar t)) (head ti)))
          else ()
        in

        if Subst.is_empty general then (
          (* [subst] is incompatible with [head], try next sibling
             TODO: we might optimize the search by indexing trees by their head constructor
             for a particular variable. This is reminiscent of a trie. The heuristic to choose
             which variable to split would be crucial. *)

          (* subst = residual_subst
             re-establish pre-condition for recursive call by reverting the
             state of variables in domain of [partial_residual_subst] *)
          Scope.apply_undo undo_frame ;
          insert_aux subst t (i + 1))
        else
          let residual_subst =
            Subst.fold
              (fun residual_subst v t ->
                if not (is_ivar v) then Subst.push v t residual_subst
                else residual_subst)
              partial_residual_subst
              subst
          in
          let () = Subst.assign residual_subst in
          if Subst.is_empty residual_subst && Subst.is_empty residual_node then
            (* exact match: general = head *)
            (* At this point:
               - [general] domain is unset, [head = general] and [subst = general] hence
                 post-condition is satisfied *)
            match ti with
            | Node _ -> assert false
            | Leaf node -> node.data <- f (Some node.data)
          else if Subst.is_empty residual_subst then (
            (* Here, [subst = general], [head = residual_node \circ general]
               it follows that [head] refines [subst]. *)
            match ti with
            | Node _ -> assert false
            | Leaf node ->
                node.head <- residual_node ;
                let new_node =
                  Node { head = general; subtrees = Vec.of_array [| ti |] }
                in
                Vec.set t i new_node ;
                Subst.reset residual_node)
          else if Subst.is_empty residual_node then
            (* Here, [head = general], [subst = residual_subst \circ general]
               it follows that [subst] refines [head]. *)
            (* subst refines head *)
            let subtrees =
              match ti with
              | Leaf node ->
                  let subtrees = Vec.create () in
                  let flat = Node { head = node.head; subtrees } in
                  Vec.set t i flat ;
                  subtrees
              | Node node -> node.subtrees
            in
            insert_aux residual_subst subtrees 0
          else (
            (* [subst] has a nontrivial mscg
               - we replace [head] by [general] ([general] generalizes [head])
               - we introduce a new node below the current one labelled by [residual_node]
               - next to the node labelled by [residual_node] we introduce a leaf labelled by [residual_subst] *)
            set_head ti residual_node ;
            let new_node_children =
              Vec.of_array
                [| ti; Leaf { head = residual_subst; data = f None } |]
            in
            let new_node =
              Node { head = general; subtrees = new_node_children }
            in
            Vec.set t i new_node ;
            Subst.reset residual_node ;
            Subst.reset residual_subst)
    in
    tree.root.desc <- term.desc ;
    insert_aux (Subst.push tree.root term (Subst.empty ())) tree.nodes 0

  module Stats = struct
    [@@@ocaml.warning "-32"]

    let rec max_depth_node node =
      match node with
      | Leaf _ -> 1
      | Node node ->
          1
          + Vec.fold
              (fun acc node -> max acc (max_depth_node node))
              0
              node.subtrees

    let max_depth index =
      Vec.fold (fun acc node -> max acc (max_depth_node node)) 0 index.nodes

    let rec max_width_node node =
      match node with
      | Leaf _ -> 0
      | Node node ->
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
    type subst = Subst.t

    let pp_subst = pp_subst

    exception Not_well_scoped of iterm * IS.t

    exception Not_properly_unset

    exception Trivial_subst of subst

    let rec all_unset_node node =
      match node with
      | Leaf node -> Subst.for_all (fun v _ -> is_ivar v) node.head
      | Node node ->
          Subst.for_all (fun v _ -> is_ivar v) node.head
          && Vec.for_all all_unset_node node.subtrees

    let all_unset (index : 'a t) : bool = Vec.for_all all_unset_node index.nodes

    let non_trivial subst = not (List.exists (fun (_v, t) -> is_ivar t) subst)

    let rec well_scoped_subst subst in_scope acc =
      match subst with
      | [] -> IS.union acc in_scope
      | (v, t) :: rest ->
          let t_ivars = ivars t |> List.map (fun r -> uid r) in
          if not (IS.mem (uid v) in_scope) then
            raise (Not_well_scoped (v, in_scope))
          else
            let acc = IS.union acc (IS.of_list t_ivars) in
            well_scoped_subst rest in_scope acc

    let rec well_scoped_node node in_scope =
      let subst = head node in
      let in_scope =
        well_scoped_subst (Subst.to_bindings subst) in_scope IS.empty
      in
      if not (non_trivial (Subst.to_bindings subst)) then
        raise (Trivial_subst subst) ;
      match node with
      | Leaf _ -> ()
      | Node node ->
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
    update (iterm_of_term tree.var_table term) (fun _ -> data) tree

  let update term f tree = update (iterm_of_term tree.var_table term) f tree

  (*
     TODO: could implement substitutions as pair of vectors
   *)

  module Unifiable_query = struct
    let rec unify scope (term1 : iterm) (term2 : iterm) =
      match (term1.desc, term2.desc) with
      | (Prim (prim1, args1), Prim (prim2, args2)) ->
          if P.equal prim1 prim2 then unify_arrays scope args1 args2 0
          else false
      | (Var (_, repr_ptr1), Var (_, repr_ptr2)) -> (
          if repr_ptr1 == repr_ptr2 then true
          else
            (* term1, term2 are [Var], hence precondition of [get_repr] is satisfied *)
            let (repr1, root_var1) = get_repr term1 in
            let (repr2, root_var2) = get_repr term2 in
            (* invariant: root_var1, root_var2 are Var pointing to Prim or IVar *)
            match (repr1.desc, repr2.desc) with
            | (Prim _, Prim _) -> unify scope repr1 repr2
            | (Prim _, (IVar | EVar)) ->
                (* let term2 point to term1 *)
                Scope.set_desc scope repr2 root_var1.desc ;
                true
            | ((IVar | EVar), Prim _) ->
                (* let term1 point to term2 *)
                Scope.set_desc scope repr1 root_var2.desc ;
                true
            | ((IVar | EVar), (IVar | EVar)) ->
                (* It may be the case that root_var1 == root_var2, if we
                   perform the assignment then we'll introduce a cycle. *)
                if repr1 == repr2 then true
                else (
                  Scope.set_desc scope repr1 root_var2.desc ;
                  true)
            | (Var _, _) | (_, Var _) ->
                (* Impossible case *)
                assert false)
      | (Var (_, _), Prim _) -> (
          let (repr, _root_var) = get_repr term1 in
          match repr.desc with
          | IVar | EVar ->
              Scope.set_desc scope repr term2.desc ;
              true
          | Prim _ -> unify scope repr term2
          | Var _ ->
              (* Impossible case *)
              assert false)
      | (Prim _, Var (_, _)) -> (
          let (repr, _root_var) = get_repr term2 in
          match repr.desc with
          | IVar | EVar ->
              Scope.set_desc scope repr term1.desc ;
              true
          | Prim _ -> unify scope term1 repr
          | Var _ ->
              (* Impossible case *)
              assert false)
      | (IVar, ((Prim _ | Var _) as desc2)) ->
          Scope.set_desc scope term1 desc2 ;
          true
      | (((Prim _ | Var _) as desc1), IVar) ->
          Scope.set_desc scope term2 desc1 ;
          true
      | (IVar, IVar) ->
          (* The value of the variable does not matter. *)
          let fresh = Var (-1, make IVar) in
          Scope.set_desc scope term1 fresh ;
          Scope.set_desc scope term2 fresh ;
          true
      | (EVar, _) | (_, EVar) -> assert false

    and unify_arrays scope args1 args2 i =
      if i = Array.length args1 then true
      else
        let success = unify scope args1.(i) args2.(i) in
        if success then unify_arrays scope args1 args2 (i + 1) else false

    let unification_subst scope subst =
      Subst.iter_while
        (fun v t ->
          if unify scope v t then (
            Scope.set_desc scope v t.desc ;
            true)
          else false)
        subst
  end

  let rec check_equality scope (term1 : iterm) (term2 : iterm) =
    match (term1.desc, term2.desc) with
    | (Prim (prim1, args1), Prim (prim2, args2)) ->
        if P.equal prim1 prim2 then check_equality_arrays scope args1 args2 0
        else false
    | (Var (_, repr1), Var (_, repr2)) -> if repr1 == repr2 then true else false
    | (Var (_, _), Prim _) -> false
    | (Prim _, Var (_, _)) -> false
    | (IVar, ((Prim _ | Var _) as desc2)) ->
        Scope.set_desc scope term1 desc2 ;
        true
    | (((Prim _ | Var _) as desc1), IVar) ->
        Scope.set_desc scope term2 desc1 ;
        true
    | (IVar, IVar) ->
        (* The value of the variable does not matter. *)
        let fresh = Var (-1, make IVar) in
        Scope.set_desc scope term1 fresh ;
        Scope.set_desc scope term2 fresh ;
        true
    | (EVar, _) | (_, EVar) -> assert false

  and check_equality_arrays scope args1 args2 i =
    if i = Array.length args1 then true
    else
      let success = check_equality scope args1.(i) args2.(i) in
      if success then check_equality_arrays scope args1 args2 (i + 1) else false

  module Specialize_query = struct
    let rec check_specialize scope (term1 : iterm) (term2 : iterm) =
      match (term1.desc, term2.desc) with
      | (Prim (prim1, args1), Prim (prim2, args2)) ->
          if P.equal prim1 prim2 then
            check_specialize_arrays scope args1 args2 0
          else false
      | (Var (_, repr1), Var (_, repr2)) -> (
          match repr1.desc with
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
              Scope.set_desc scope repr1 term2.desc ;
              true
          | IVar ->
              (* non-query variables can't be instantiated when specializing *)
              false
          | Prim _ ->
              (* Variable already instantiated with a prim, cannot specialize
                 to another variable. *)
              false
          | Var (_, repr1') ->
              (* Variable was was already mapped to a term variable, check equality. *)
              repr1' == repr2)
      | (Var (_, repr), Prim _) -> (
          match repr.desc with
          | EVar ->
              (* Variable not instantiated; instantiate it with term2. *)
              Scope.set_desc scope repr term2.desc ;
              true
          | IVar ->
              (* non-query variables can't be instantiated when specializing *)
              false
          | Prim _ ->
              (* Variable was already instantiated with a prim, check
                 that instances properly specialize. Note that [repr] is not
                 a query term and may contain [IVar] and [Var] nodes. *)
              check_equality scope repr term2
          | Var _ ->
              (* Variable was was already mapped to a term variable *)
              false)
      | (Prim _, Var (_, _)) -> false
      | (IVar, ((Prim _ | Var _) as desc2)) ->
          Scope.set_desc scope term1 desc2 ;
          true
      | (IVar, IVar) ->
          (* The value of the variable does not matter. *)
          let fresh = Var (-1, make IVar) in
          Scope.set_desc scope term1 fresh ;
          Scope.set_desc scope term2 fresh ;
          true
      | (((Prim _ | Var _) as desc1), IVar) ->
          Scope.set_desc scope term2 desc1 ;
          true
      | (EVar, _) | (_, EVar) -> assert false

    and check_specialize_arrays scope args1 args2 i =
      if i = Array.length args1 then true
      else
        let success = check_specialize scope args1.(i) args2.(i) in
        if success then check_specialize_arrays scope args1 args2 (i + 1)
        else false

    let check_specialize_subst scope subst =
      Subst.iter_while
        (fun v t ->
          if check_specialize scope v t then (
            Scope.set_desc scope v t.desc ;
            true)
          else false)
        subst
  end

  module Generalize_query = struct
    let rec check_generalize scope (term1 : iterm) (term2 : iterm) =
      match (term1.desc, term2.desc) with
      | (Prim (prim1, args1), Prim (prim2, args2)) ->
          if P.equal prim1 prim2 then
            check_generalize_arrays scope args1 args2 0
          else false
      | (Var (_, repr1), Var (_, repr2)) -> (
          match repr2.desc with
          | IVar | EVar ->
              (* Variable not instantiated; instantiate it with term1. *)
              (* Note that cycles may be introduced here. It's fine. *)
              Scope.set_desc scope repr2 term1.desc ;
              true
          | Prim _ ->
              (* Variable already instantiated with a prim, cannot generalize
                 to a distinct variable. *)
              false
          | Var (_, repr2') ->
              (* Variable was was already mapped to a term variable, check equality. *)
              repr2' == repr1)
      | (Prim _, Var (_, repr)) -> (
          match repr.desc with
          | IVar | EVar ->
              (* Variable not instantiated; instantiate it with term1. *)
              Scope.set_desc scope repr term1.desc ;
              true
          | Prim _ ->
              (* Variable was already instantiated with a prim, check equality.*)
              check_equality scope term1 repr
          | Var _ ->
              (* Variable was was already mapped to a query variable. *)
              false)
      | (Var (_, _), Prim _) -> false
      | (IVar, ((Prim _ | Var _) as desc2)) ->
          Scope.set_desc scope term1 desc2 ;
          true
      | (IVar, IVar) ->
          (* The value of the variable does not matter. *)
          let fresh = Var (-1, make IVar) in
          Scope.set_desc scope term1 fresh ;
          Scope.set_desc scope term2 fresh ;
          true
      | (((Prim _ | Var _) as desc1), IVar) ->
          Scope.set_desc scope term2 desc1 ;
          true
      | (EVar, _) | (_, EVar) -> assert false

    and check_generalize_arrays scope args1 args2 i =
      if i = Array.length args1 then true
      else
        let success = check_generalize scope args1.(i) args2.(i) in
        if success then check_generalize_arrays scope args1 args2 (i + 1)
        else false

    let check_generalize_subst scope subst =
      Subst.iter_while
        (fun v t ->
          if check_generalize scope v t then (
            Scope.set_desc scope v t.desc ;
            true)
          else false)
        subst
  end

  let rec iter_node f node (root : iterm) =
    match node with
    | Leaf node ->
        Subst.assign node.head ;
        f root node.data ;
        Subst.reset node.head
    | Node node ->
        Subst.assign node.head ;
        Vec.iter (fun node -> iter_node f node root) node.subtrees ;
        Subst.reset node.head

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
    Scope.undo_scope @@ fun scope ->
    let success =
      match qkind with
      | Unifiable -> Unifiable_query.unification_subst scope (head node)
      | Specialize -> Specialize_query.check_specialize_subst scope (head node)
      | Generalize -> Generalize_query.check_generalize_subst scope (head node)
    in
    if success then
      match node with
      | Leaf node -> f root node.data
      | Node node ->
          Vec.iter (fun node -> iter_query_node f node root qkind) node.subtrees
    else ()

  let iter_query f (index : 'a t) (qkind : query_kind) (query : iterm) =
    (* [query] is either a Prim or a Var. *)
    Scope.undo_scope @@ fun scope ->
    Scope.set_desc scope index.root query.desc ;
    (* The toplevel substitution of the index has domain equal to [index.root]. *)
    Vec.iter (fun node -> iter_query_node f node index.root qkind) index.nodes

  let iter_unifiable_transient f index query =
    iter_query f index Unifiable (of_term index query)

  let iter_unifiable f index =
    iter_unifiable_transient (fun term v -> f (to_term term) v) index

  let rec set_query_variables scope term =
    match term.desc with
    | Var (_, repr) -> Scope.set_desc scope repr EVar
    | Prim (_, args) -> Array.iter (fun t -> set_query_variables scope t) args
    | IVar -> ()
    | EVar -> assert false

  let iter_specialize_transient f index query =
    let query_term = of_term index query in
    Scope.undo_scope @@ fun scope ->
    set_query_variables scope query_term ;
    iter_query f index Specialize query_term

  let iter_specialize f index =
    iter_specialize_transient (fun term v -> f (to_term term) v) index

  let iter_generalize_transient f index query =
    let query_term = of_term index query in
    Scope.undo_scope @@ fun scope ->
    set_query_variables scope query_term ;
    iter_query f index Generalize (of_term index query)

  let iter_generalize f index =
    iter_generalize_transient (fun term v -> f (to_term term) v) index
end
