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

  val identity : unit -> t

  val is_identity : t -> bool

  val equal : t -> t -> bool

  (** [ub subst] is an upper bound on the absolute value of variables appearing in [subst]
      (either in the domain or the range of the substitution). *)
  val ub : t -> Int_option.t

  (** [map subst] returns the underlying map of the substitution. *)
  val map : t -> term var_map

  (** [eval v subst] returns [Some t] if [v] is mapped to the term [t] in [subst]
      or [None] if [v] is not in the domain of [subst]. *)
  val eval : var -> t -> term option

  (** Exception-raising variant of {!eval}.
      @raise Not_found if [v] is not in the domain of [subst]. *)
  val eval_exn : var -> t -> term

  (** [add v t subst] adds a mapping from [v] to [t] in [subst].
      If [v] is already in the domain of [subst], the previous mapping is replaced.
  *)
  val add : var -> term -> t -> t

  (** [lift subst term] applies the substitution [subst] to [term].
      Note that [lift] does not perform an occur check: do not use it with
      substitutions that are not well-founded. *)
  val lift : t -> term -> term

  (** [union s1 s2] computes the union of [s1] and [s2].
      Returns [None] if [s1] and [s2] do not have disjoint domains. *)
  val union : t -> t -> t option
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
  end
end

module Make
    (P : Intf.Signature)
    (M : Intf.Map with type key = int)
    (T : Term.S with type prim = P.t and type 'a var_map = 'a M.t) :
  S with type term = T.t and type 'a var_map = 'a T.var_map = struct
  type term = T.t

  type 'a var_map = 'a T.var_map

  type t = { subst : T.t M.t; ub : Int_option.t }

  let identity () = { subst = M.empty (); ub = Int_option.none }

  let is_identity : t -> bool = fun s -> M.is_empty s.subst

  let of_seq l : t =
    let ub =
      Seq.fold_left
        (fun acc (v, t) -> Int_option.(max (of_int (abs v)) (max (T.ub t) acc)))
        Int_option.none
        l
    in
    { subst = M.of_seq l; ub }

  let to_seq { subst; ub = _ } = M.to_seq subst

  let to_seq_keys { subst; ub = _ } = M.to_seq_keys subst

  let pp fmtr subst =
    let pp_binding fmtr (v, t) =
      Format.fprintf fmtr "@[<hov 2>%a ->@ @[%a@]@]" T.pp (T.var v) T.pp t
    in
    Format.fprintf
      fmtr
      "{@[@,%a@,@]}"
      (Format.pp_print_seq
         ~pp_sep:(fun fmtr () -> Format.fprintf fmtr "@.")
         pp_binding)
      (to_seq subst)

  let equal (s1 : t) (s2 : t) =
    Int_option.equal s1.ub s2.ub && M.equal T.equal s1.subst s2.subst

  let ub { ub; subst = _ } = ub

  let map { subst; ub = _ } = subst

  let eval v { subst; ub = _ } = M.find_opt v subst

  let eval_exn v { subst; ub = _ } =
    match M.find_opt v subst with None -> raise Not_found | Some t -> t

  let add var term { subst; ub } =
    let ub = Int_option.(max (of_int (abs var)) (max (T.ub term) ub)) in
    { subst = M.add var term subst; ub }

  (* /!\ no occur check, the substitution should be well-founded or this will stack overflow *)
  let rec lift subst (term : term) =
    match term.Hashcons.node with
    | Prim (prim, subterms, _) -> T.prim prim (Array.map (lift subst) subterms)
    | Var v -> (
        match eval v subst with None -> term | Some term -> lift subst term)

  (* exception Occurs_check *)
  (* let lift subst term = *)
  (*   let rec lift subst seen (term : term) = *)
  (*     match term.Hashcons.node with *)
  (*     | Prim (prim, subterms, _) -> *)
  (*         T.prim prim (Array.map (lift subst seen) subterms) *)
  (*     | Var v -> ( *)
  (*         if List.mem v seen then raise Occurs_check *)
  (*         else *)
  (*           match eval v subst with *)
  (*           | None -> term *)
  (*           | Some term -> lift subst (v :: seen) term) *)
  (*   in *)
  (*   try lift subst [] term *)
  (*   with Occurs_check -> *)
  (*     Format.eprintf "lift %a %a invalid@." pp subst T.pp term ; *)
  (*     raise Occurs_check *)

  let union s1 s2 =
    let exception Invalid_union in
    try
      let map = M.union (fun _ _ _ -> raise Invalid_union) s1.subst s2.subst in
      Some { subst = map; ub = Int_option.max s1.ub s2.ub }
    with Invalid_union -> None
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

  (* TODO: maintain upper bound on variables as we do with terms. *)
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
              then
                (* [subst] = [result] = [head] *)
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
      (S.of_seq (List.to_seq [(indicator 0, term)]))
      data
      may_overwrite
      tree ;
    term

  (*
     To reconstruct the substitution at a given node, we can rely on the fact that on
     a path from the root all substitutions have disjoint domains. From such a substitution,
     we can extract the term by evaluating the substitution.
   *)

  let rec iter_node f subst node =
    let subst =
      match S.union node.head subst with
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

  (* exception Not_unifiable *)

  (* let rec unify (query : subst) (head : subst) = *)
  (*   S.merge *)
  (*     (fun _v q h -> *)
  (*       match (q, h) with *)
  (*       | (None, None) -> None *)
  (*       | (Some _, None) -> None *)
  (*       | (None, Some _) -> None *)
  (*       | (Some qt, Some ht) -> unify_terms qt ht []) *)
  (*     query *)
  (*     head *)

  (* and unify_terms (qt : term) (ht : term) eqs = *)
  (*   match (qt.Hashcons.node, ht.Hashcons.node) with *)
  (*   | (Prim (qp, qvec, _), Prim (hp, hvec, _)) -> *)
  (*       if P.equal qp hp then ( *)
  (*         (\* assert (Array.length qvec = Array.length hvec) *\) *)
  (*         let eqs = ref eqs in *)
  (*         Array.iter2 (fun qt' ht' -> eqs := unify_terms qt' ht' !eqs) qvec hvec ; *)
  (*         unify_eqs eqs) *)
  (*       else raise Not_unifiable *)
  (*   | (Prim _, Var hv) -> *)
  (*       (\* [hv] is either an indicator variable or a variable *)
  (*          from a key. *\) *)
  (*       assert false *)
  (*   | _ -> assert false *)

  (* TODO *)
  (* let iter_unifiable_node query f tree = *)
  (*   (\* if head is unifiable with current state then *)
  (*      1) iterate on node.data if relevant *)
  (*      2) iterate on subtrees *\) *)
  (*   assert false *)

  (* let iter_unifiable query f { nodes; _ } = *)
  (*   Vec.iter (iter_unifiable_node query f) nodes *)

  let iter_unifiable_node (query : term) _f _root =
    (* Upper bound on the number of variables contained in the term. Used to (re)-dimension
       union-find. *)
    (* TODO: it's too annoying to compute the set of variables contained in the tree.
       Need PVec or something similar. *)
    let upper_bound = T.ub query in
    Int_option.max upper_bound

  let iter_unifiable (query : term) f root =
    iter_unifiable_node query f root.nodes

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
            if not (Option.is_some (S.union head head')) then (
              Format.printf "head = %a, head' = %a@." S.pp head S.pp head' ;
              raise (Invariant_violation (j :: path, head, head'))) ;
            check_invariants path j node')
          node.subtrees
      in
      Vec.iteri (check_invariants []) tree.nodes ;
      true
  end
end
