module Vec = Containers.Vector

(** The module type of substitutions *)
module type S = sig
  (** The type of terms *)
  type term

  type 'a var_map

  type var := int

  (** The type of substitutions *)
  type t

  val of_seq : (var * term) Seq.t -> t

  val to_seq : t -> (var * term) Seq.t

  val to_seq_keys : t -> var Seq.t

  val pp : Format.formatter -> t -> unit

  (** [identity ()] is the identity substitution.  *)
  val identity : unit -> t

  (** [is_identity subst] checks whether [equal subst identity] *)
  val is_identity : t -> bool

  val equal : t -> t -> bool

  (** [ub subst] is an upper bound on the absolute value of variables appearing in [subst]
      (either in the domain or the range of the substitution). *)
  val ub : t -> Int_option.t

  (** [underlying_map subst] returns the underlying map of the substitution. *)
  val underlying_map : t -> term var_map

  (** [eval v subst] returns [Some t] if [v] is mapped to the term [t] in [subst]
      or [None] if [v] is not in the domain of [subst]. *)
  val eval : var -> t -> term option

  (** Exception-raising variant of {!eval}.
      @raise Not_found if [v] is not in the domain of [subst]. *)
  val eval_exn : var -> t -> term

  (** [add v t subst] adds a mapping from [v] to [t] in [subst].
      If [v] is already in the domain of [subst], the previous mapping is replaced.

      @raise Invalid_argument if [t] is a variable equal to [v] *)
  val add : var -> term -> t -> t

  (** [unsafe_add] does as {!add} but doen't check for validity of the mapping. *)
  val unsafe_add : var -> term -> t -> t

  (** [lift subst term] applies the substitution [subst] to [term].
      Note that [lift] does not perform an occur check: do not use it with
      substitutions that are not well-founded. *)
  val lift : t -> term -> term

  (** [union f s1 s2] computes the union of [s1] and [s2], using [f] to merge
      terms associated to the same variable. *)
  val union : (var -> term -> term -> term option) -> t -> t -> t

  (** [Unification] contains facilities to perform first-order term unification *)
  module Unification : sig
    (** [state] is the type of unification state. *)
    type state

    (** [Cannot_unify] is raised by {!unify} when a unifier cannot be found. *)
    exception Cannot_unify

    (** [empty ()] is an empty unification state. *)
    val empty : unit -> state

    (** [unify t1 t2 state] unifies terms [t1] and [t2] in state [state] and returns
        an updated {!state}.

        @raise Cannot_unify if no solution was found. *)
    val unify : term -> term -> state -> state

    (** [unify_subst s state] unifies [s] with substitution state [state]
        and returns an updated {!state}. *)
    val unify_subst : t -> state -> state

    (** [generalize t1 t2 subst] extends [subst] into a substitution such that [lift t1 subst = t2] or
        raises [Cannot_unify] if it cannot proceed to this extension.CCArray

        @raise Cannot_unify if no solution was found. *)
    val generalize : term -> term -> t -> t

    (** [subst state] returns the substitution underlying the unification state. *)
    val subst : state -> t
  end
end

(** The module type of substitution trees *)
module type Tree_S = sig
  (** The type of substitutions *)
  type subst

  (** The type of terms, which act as keys of substitution trees *)
  type term

  (** The type of variables *)
  type var

  (** The type of substitution trees with values of type ['a] *)
  type 'a t

  val create : unit -> 'a t

  (** [insert term data index] adds a mapping from a canonicalized version of [term] to [data] in [index],
      and returns the canonicalized term. *)
  val insert : term -> 'a -> 'a t -> term

  (** [iter f index] iterates [f] on the bindings of [index]. *)
  val iter : (term -> 'a -> unit) -> 'a t -> unit

  module Internal_for_tests : sig
    val indicator : int -> int

    val is_indicator_variable : int -> bool

    val gen_indicator : unit -> unit -> int

    val index : int -> int

    val is_index_variable : int -> bool

    val gen_index : unit -> unit -> int

    val query : int -> int

    val is_query_variable : int -> bool

    exception Invariant_violation of int list * subst * subst

    val check_invariants : 'a t -> bool

    (** [mscg term1 term2 freshgen] computes a triple [(result, residual1, residual2)] where
      [result] is the most spceific common generalization of [term1] and [term2],
      [residual1] is a substitution such that [result] is equal to [term1] after applying [residual1],
      and [residual2] is a substitution such that [result] is equal to [term2] after applying [residual2]. *)
    val mscg : term -> term -> (unit -> var) -> term * subst * subst

    (** [mscg_subst s1 s2 freshgen] computes a triple [(result, residual1, residual2)] where
      [result] is the most specific common generalization of [s1] and [s2],
      [residual1] is a substitution such that [result] is equal to [s1] after composing with [residual1],
      and [residual2] is a substitution such that [result] is equal to [s2] after composing [residual2]. *)
    val mscg_subst : subst -> subst -> (unit -> var) -> subst * subst * subst

    val ub : 'a t -> Int_option.t
  end
end

module Make
    (P : Intf.Signature)
    (M : Intf.Map with type key = int)
    (T : Term.S with type prim = P.t and type 'a var_map = 'a M.t) :
  S with type term = T.t and type 'a var_map = 'a T.var_map = struct
  type term = T.t

  type 'a var_map = 'a T.var_map

  type t = T.t M.t

  let identity = M.empty

  let is_identity = M.is_empty

  let to_seq = M.to_seq

  let to_seq_keys = M.to_seq_keys

  let pp fmtr subst =
    let pp_binding fmtr (v, t) =
      Format.fprintf fmtr "@[<hov 2>%a ->@ @[%a@]@]" T.pp (T.var v) T.pp t
    in
    (Fmt.brackets (Fmt.seq ~sep:Fmt.semi (Fmt.vbox pp_binding)))
      fmtr
      (to_seq subst)

  let equal s1 s2 = M.equal T.equal s1 s2

  let ub subst =
    Seq.fold_left
      (fun acc (v, t) -> Int_option.(max (of_int (abs v)) (max (T.ub t) acc)))
      Int_option.none
      (to_seq subst)

  let underlying_map subst = subst

  let eval = M.find_opt

  let eval_exn v subst =
    match M.find_opt v subst with None -> raise Not_found | Some t -> t

  let add k term subst =
    (match term.Hashcons.node with
    | Term.Var v' -> if Int.equal k v' then invalid_arg "add"
    | _ -> ()) ;
    M.add k term subst

  let unsafe_add k term subst = M.add k term subst

  let of_seq seq =
    Seq.fold_left (fun acc (v, t) -> add v t acc) (identity ()) seq

  (* /!\ no occur check, the substitution should be well-founded or this will stack overflow *)
  let rec lift subst (term : term) =
    match term.Hashcons.node with
    | Prim (prim, subterms, ub) ->
        (* Optimization: if the term is ground then no need to recurse. *)
        if Int_option.is_none ub then term
        else T.prim prim (Array.map (lift subst) subterms)
    | Var v -> (
        match eval v subst with None -> term | Some term -> lift subst term)

  let union = M.union

  module Unification = struct
    type state = { subst : t; uf : Uf.Map_based.t }

    exception Cannot_unify

    let subst { subst; _ } = subst

    let empty () = { subst = identity (); uf = Uf.Map_based.empty () }

    let get_repr var { subst; uf } =
      let repr = Uf.Map_based.find uf var in
      eval repr subst

    let rec unify (term1 : term) (term2 : term) (state : state) =
      if T.equal term1 term2 then state
      else
        match (term1.Hashcons.node, term2.Hashcons.node) with
        | ( Term.Prim (prim1, subterms1, _ub1),
            Term.Prim (prim2, subterms2, _ub2) ) ->
            if P.equal prim1 prim2 then
              (* invariant: [Array.length subterms1 = Array.length subterms2] *)
              unify_subterms subterms1 subterms2 state 0
            else raise Cannot_unify
        | (Term.Var v1, Term.Var v2) -> (
            (* v1 <> v2 *)
            let repr1_opt = get_repr v1 state in
            let repr2_opt = get_repr v2 state in
            let (vrepr, uf) = Uf.Map_based.union state.uf v1 v2 in
            match (repr1_opt, repr2_opt) with
            | (None, None) -> { state with uf }
            | (Some repr, None) | (None, Some repr) ->
                let subst = add vrepr repr state.subst in
                { uf; subst }
            | (Some repr1, Some repr2) ->
                let state = unify repr1 repr2 { state with uf } in
                { state with uf })
        | (Term.Var v, Term.Prim _) -> (
            let repr_opt = get_repr v state in
            match repr_opt with
            | None -> { state with subst = add v term2 state.subst }
            | Some repr -> unify repr term2 state)
        | (Term.Prim _, Term.Var v) -> (
            let repr_opt = get_repr v state in
            match repr_opt with
            | None -> { state with subst = add v term1 state.subst }
            | Some repr -> unify term1 repr state)

    and unify_subterms subterms1 subterms2 (state : state) i =
      if i = Array.length subterms1 then state
      else
        let t1 = subterms1.(i) and t2 = subterms2.(i) in
        let state = unify t1 t2 state in
        unify_subterms subterms1 subterms2 state (i + 1)

    let rec generalize (term1 : term) (term2 : term) subst =
      match (term1.Hashcons.node, term2.Hashcons.node) with
      | (Term.Prim (prim1, subterms1, _ub1), Term.Prim (prim2, subterms2, _ub2))
        ->
          if P.equal prim1 prim2 then
            (* invariant: [Array.length subterms1 = Array.length subterms2] *)
            generalize_subterms subterms1 subterms2 subst 0
          else raise Cannot_unify
      | (Term.Prim _, _) -> raise Cannot_unify
      | (Term.Var v, Term.Var v') when v = v' -> subst
      | (Term.Var v, _) -> (
          match eval v subst with
          | None -> add v term2 subst
          | Some t -> generalize t term2 subst)

    and generalize_subterms subterms1 subterms2 subst i =
      if i = Array.length subterms1 then subst
      else
        let t1 = subterms1.(i) and t2 = subterms2.(i) in
        let subst = generalize t1 t2 subst in
        generalize_subterms subterms1 subterms2 subst (i + 1)

    let unify_subst (subst : t) (state : state) =
      Seq.fold_left
        (fun state (v, t) ->
          let repr_opt = get_repr v state in
          match repr_opt with
          | None -> { state with subst = add v t state.subst }
          | Some repr ->
              let state = { state with subst = add v t state.subst } in
              unify repr t state)
        state
        (M.to_seq subst)
  end
end

module Make_index
    (P : Intf.Signature)
    (M : Intf.Map with type key = int)
    (T : Term.S with type prim = P.t and type 'a var_map = 'a M.t)
    (S : S with type term = T.t and type 'a var_map = 'a T.var_map) =
struct
  type term = T.t

  type subst = S.t

  (* Invariant: keys of a substitution are indicator variables. *)
  type 'a tree = { fresh : int ref; nodes : 'a node Vec.vector }

  and 'a node =
    { mutable head : subst;
      (* We should be able to index nodes by the head constructor *)
      subtrees : 'a node Vec.vector;
      mutable data : 'a option
    }

  (* Invariants:
     - indicator variables are of the form 4k
     - variables contained in terms inserted by the user into the index are of the form 4k+1
     - variables contained in queries are canonicalized to be of the form 4k+2
     Hence, we have the property that these three sets are always disjoint.
  *)

  (** Substitution trees operate on terms where variables are split into two
      disjoint subsets: variables stemming from the terms inserted by the user
      and so-called 'indicator' variables, which constitute the domain of the
      substitutions and denote sharing among sub-trees.

      We define indicator variables as the strictly negative integers.
  *)
  let indicator x = x lsl 2

  let is_indicator_variable x = x land 3 = 0

  let gen_indicator () =
    let counter = ref 0 in
    fun () ->
      let v = !counter in
      counter := v + 4 ;
      v

  let index x = (x lsl 2) + 1

  let is_index_variable x = x land 3 = 1

  let gen_index () =
    let counter = ref 1 in
    fun () ->
      let v = !counter in
      counter := v + 4 ;
      v

  let query x = (x lsl 2) + 2

  let is_query_variable x = x land 3 = 2

  let gen_query_variable () =
    let counter = ref 2 in
    fun () ->
      let v = !counter in
      counter := v + 4 ;
      v

  let next x = x + 4

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

  and box_of_subst subst = PrintBox.text (Format.asprintf "%a" S.pp subst)

  and box_of_subtrees pp_data vec = Vec.to_list vec |> List.map (to_box pp_data)

  let pp_node pp_data fmtr node = PrintBox_text.pp fmtr (to_box pp_data node)

  let pp pp_data fmtr tree =
    PrintBox_text.pp fmtr (PrintBox.vlist (box_of_subtrees pp_data tree.nodes))

  let create () = { fresh = ref 0; nodes = Vec.create () }

  let generalize t1 t2 gen residual1 residual2 =
    let v = gen () in
    (T.var v, S.add v t1 residual1, S.add v t2 residual2)
  [@@ocaml.inline]

  (*
     invariant: domain of residuals are indexing variables. Newly
     added variables in residuals are disjoint from all existing variables.
  *)
  let rec mscg_aux (t1 : T.t) (t2 : T.t) gen (residual1 : subst)
      (residual2 : subst) =
    if T.equal t1 t2 then (t1, residual1, residual2)
    else
      (* Does it hold that t1 and t2 cannot be both indicator variables? *)
      match (t1.Hashcons.node, t2.Hashcons.node) with
      | (Term.Prim (prim1, subterms1, _), Term.Prim (prim2, subterms2, _)) ->
          if P.equal prim1 prim2 then
            let (subterms, residual1, residual2) =
              mscg_subterms subterms1 subterms2 gen residual1 residual2 [] 0
            in
            (T.prim prim1 subterms, residual1, residual2)
          else generalize t1 t2 gen residual1 residual2
      | (Term.Var v1, Term.Var v2) ->
          (* This clause is subsumed by the two next ones but we need it to ensure
             commutativity of [mscg_aux]. *)
          if is_indicator_variable v1 then (t1, residual1, S.add v1 t2 residual2)
          else if is_indicator_variable v2 then
            (t2, S.add v2 t1 residual1, residual2)
          else generalize t1 t2 gen residual1 residual2
      | (_, Term.Var v) ->
          if is_indicator_variable v then (t2, S.add v t1 residual1, residual2)
          else generalize t1 t2 gen residual1 residual2
      | (Term.Var v, _) ->
          if is_indicator_variable v then (t1, residual1, S.add v t2 residual2)
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

  let mscg t1 t2 =
    mscg_aux t1 t2 (gen_indicator ()) (S.identity ()) (S.identity ())

  let top_symbol_disagrees (t1 : T.t) (t2 : T.t) =
    match (t1.Hashcons.node, t2.Hashcons.node) with
    | (Term.Prim (prim1, _, _), Term.Prim (prim2, _, _)) ->
        not (P.equal prim1 prim2)
    | (Term.Var v1, Term.Var v2) -> v1 <> v2
    | (Term.Prim _, Term.Var _) | (Term.Var _, Term.Prim _) -> true

  let mscg_subst (s1 : subst) (s2 : subst) gen =
    let rec loop (s1 : (int * term) Seq.t) (s2 : (int * term) Seq.t)
        (residual1_acc : subst) (residual2_acc : subst) (result_acc : subst) =
      match (s1 (), s2 ()) with
      | (Seq.Nil, _) ->
          (result_acc, residual1_acc, add_to_subst residual2_acc s2)
      | (_, Seq.Nil) ->
          (result_acc, add_to_subst residual1_acc s1, residual2_acc)
      | (Seq.Cons ((v1, t1), s1'), Seq.Cons ((v2, t2), s2')) ->
          if v1 = v2 then
            if T.equal t1 t2 then
              (* optimization *)
              let result_acc = S.add v1 t1 result_acc in
              loop s1' s2' residual1_acc residual2_acc result_acc
            else if top_symbol_disagrees t1 t2 then
              (* If [top_symbol_disagrees t1 t2] then calling [mscg] would yield
                 a mapping from [v] (an indicator variable, by assumption) to a fresh indicator variable,
                 and in the residuals, mapping the fresh indicator variable to resp. [t1] and [t2]. We
                 avoid creating a new variable by directly mapping [v] to [t1] (resp. [t2])
              *)
              let residual1_acc = S.add v1 t1 residual1_acc in
              let residual2_acc = S.add v1 t2 residual2_acc in
              loop s1' s2' residual1_acc residual2_acc result_acc
            else
              let (res, residual1_acc, residual2_acc) =
                mscg_aux t1 t2 gen residual1_acc residual2_acc
              in
              let result_acc = S.add v1 res result_acc in
              loop s1' s2' residual1_acc residual2_acc result_acc
          else if v1 < v2 then
            loop s1' s2 (S.add v1 t1 residual1_acc) residual2_acc result_acc
          else
            (* v1 > v2 *)
            loop s1 s2' residual1_acc (S.add v2 t2 residual2_acc) result_acc
    and add_to_subst (subst : subst) rest =
      Seq.fold_left (fun acc (v, t) -> S.add v t acc) subst rest
    in
    loop
      (S.to_seq s1)
      (S.to_seq s2)
      (S.identity ())
      (S.identity ())
      (S.identity ())

  let try_set tree data may_overwrite =
    if may_overwrite then tree.data <- Some data
    else
      match tree.data with
      | None -> tree.data <- Some data
      | Some _ -> invalid_arg "try_set"

  let insert_subst (subst : subst) (data : 'a) (may_overwrite : bool)
      (tree : 'a tree) =
    let counter = tree.fresh in
    assert (not (S.is_identity subst)) ;
    (* We insert [subst] in the tree, possibly refining existing nodes. *)
    let rec insert_aux (subst : subst) (t : 'a node Vec.vector) i =
      if i >= Vec.length t then
        Vec.push t { head = subst; subtrees = Vec.create (); data = Some data }
      else
        let ({ head; subtrees; data = _ } as ti) = Vec.get t i in
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
          mscg_subst subst head (fun () ->
              counter := !counter + 1 ;
              indicator !counter)
        in
        if S.is_identity result then
          (* [subst] is incompatible with [head], try next sibling
             TODO: we might optimize the search by indexing trees by their head constructor for a particular variable.
             This is reminiscent of a trie. The heuristic to choose which variable to split would be crucial. *)
          insert_aux subst t (i + 1)
        else if S.equal result head then
          if
            (* [subst] instantiates (refines) [head]. *)
            (* Here, [residual1] may only define variables disjoint from [result]. *)
            S.is_identity residual1
          then (* [subst] = [result] = [head] *)
            try_set ti data may_overwrite
          else insert_aux residual1 subtrees 0
        else (
          (* [subst] has a nontrivial mscg
             - we replace [head] by [result] ([result] generalizes [head])
             - we introduce a new node below the current one labelled by [residual2]
             - next to the node labelled by [residual2] we introduce a leaf labelled by [residual1] *)
          assert (not (S.is_identity residual2)) ;
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

  let insert term data may_overwrite tree =
    let (_, term) = T.canon term (gen_index ()) in
    insert_subst
      (S.of_seq (Seq.return (indicator 0, term)))
      data
      may_overwrite
      tree ;
    term

  (*
     To reconstruct the substitution at a given node, we can rely on the fact that on
     a path from the root all substitutions have disjoint domains. From such a substitution,
     we can extract the term by evaluating the substitution.
   *)

  let disjoint_union s1 s2 =
    let exception Not_disjoint in
    try S.union (fun _ _ -> raise Not_disjoint) s1 s2 |> Option.some
    with Not_disjoint -> None

  let rec iter_node f subst node =
    let subst =
      match disjoint_union node.head subst with
      | None -> assert false
      | Some subst -> subst
    in
    (match node.data with
    | None -> ()
    | Some data ->
        let term = S.eval_exn (indicator 0) subst in
        f (S.lift subst term) data) ;
    Vec.iter (fun node -> iter_node f subst node) node.subtrees

  let iter f root = Vec.iter (iter_node f (S.identity ())) root.nodes

  (*
     query: subst with domain in indicator variables (initially domain = -1)
            and range in normal variables of kind "q"
     head: subst with domain in indicator variables
            and range in normal variables of kind "h"
     We need indicator variables, and normal variables of kind "q" and kind "h" to be
     considered disjoint and given a contiguous layout in the nonnegative integers (to use
     efficient union-find data structure).f

     let ub(q) = max over query of variables of kind q
       => assumption: variables of kind "q" are not negative
     let ub(h) = max over head of UNION(variables of kind h, indicator variables)
       => same assumption for variables of kind "h"

     layout ?:
     [0, ub(q)] for variables of kind q => query term not renamed
     [ub(q)+1, ub(q)+1+ub(h)-1] for variables of kind h
     [ub(q)+1+ub(h)+1, ub(q)+1+ub(h)+1+ub(h)] for indicator variables

     other proposal (but induces unused variables in union-find when ub(q) != ub(h) != indicator)
     0,_,_,3,_,_,6 ... i.e. variables of the form 3k for ub(q)
     _,1,_,_,4,_,_ ... i.e. variables of the form 3k+1 for ub(h)
     _,_,2,                                       3k+2 for indicator variables
     total size: 3 * max(ub(q), 2 * ub(h))
  *)

  let rec iter_unifiable_node f (nodes : 'a node Vec.vector) uf_state =
    Vec.iter
      (fun { head; subtrees; data } ->
        match S.Unification.unify_subst head uf_state with
        | exception S.Unification.Cannot_unify -> ()
        | uf_state ->
            let subst = S.Unification.subst uf_state in
            (match data with
            | None -> ()
            | Some data ->
                let term = S.eval_exn (indicator 0) subst in
                f (S.lift subst term) data) ;
            iter_unifiable_node f subtrees uf_state)
      nodes

  let iter_unifiable (query : term) f root =
    let (_, query) = T.canon query (gen_query_variable ()) in
    let query_subst = S.of_seq (Seq.return (indicator 0, query)) in
    let state =
      S.Unification.unify_subst query_subst (S.Unification.empty ())
    in
    iter_unifiable_node f root.nodes state

  (*
     TODO: iter_specialization, iter_generalization
   *)

  module Internal_for_tests = struct
    let indicator = indicator

    let is_indicator_variable = is_indicator_variable

    let gen_indicator = gen_indicator

    let index = index

    let is_index_variable = is_index_variable

    let gen_index = gen_index

    let query = query

    let is_query_variable = is_query_variable

    exception Invariant_violation of int list * subst * subst

    let check_invariants tree =
      let rec check_invariants path i node =
        let path = i :: path in
        let head = node.head in
        Vec.iteri
          (fun j node' ->
            let head' = node'.head in
            if not (Option.is_some (disjoint_union head head')) then (
              Format.printf "head = %a, head' = %a@." S.pp head S.pp head' ;
              raise (Invariant_violation (j :: path, head, head'))) ;
            check_invariants path j node')
          node.subtrees
      in
      Vec.iteri (check_invariants []) tree.nodes ;
      true

    let mscg = mscg

    let mscg_subst = mscg_subst
  end
end
