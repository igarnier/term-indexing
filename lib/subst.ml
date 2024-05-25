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

  (** [empty ()] is the empty substitution.  *)
  val empty : unit -> t

  (** [is_empty subst] checks whether [equal subst empty] *)
  val is_empty : t -> bool

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
      Note that [lift] does not perform an occur check: do not use with
      substitutions that are not well-founded. *)
  val lift : t -> term -> term

  (** [union s1 s2] computes the union of [s1] and [s2].

      @raise Invalid_argument if [s1] and [s2] have overlapping domains. *)
  val union : t -> t -> t

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

    (** [generalize t1 t2] checks that there exists a substitution [subst]
        such that [lift t1 subst = t2]. *)
    val generalize : term -> term -> bool

    (** [subst state] returns the substitution underlying the unification state. *)
    val subst : state -> t
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

  let empty = M.empty

  let is_empty = M.is_empty

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

  let of_seq seq = Seq.fold_left (fun acc (v, t) -> add v t acc) (empty ()) seq

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

    let empty () = { subst = empty (); uf = Uf.Map_based.empty () }

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

    let rec generalize (term1 : term) (term2 : term)
        (table : (int, term) Hashtbl.t) =
      match (term1.Hashcons.node, term2.Hashcons.node) with
      | (Term.Prim (prim1, subterms1, _ub1), Term.Prim (prim2, subterms2, _ub2))
        ->
          if P.equal prim1 prim2 then
            (* invariant: [Array.length subterms1 = Array.length subterms2] *)
            generalize_subterms subterms1 subterms2 table 0
          else false
      | (Term.Prim _, _) -> false
      | (Term.Var v, _) -> (
          match Hashtbl.find_opt table v with
          | None ->
              Hashtbl.add table v term2 ;
              true
          | Some t -> T.equal t term2)

    and generalize_subterms subterms1 subterms2 table i =
      if i = Array.length subterms1 then true
      else
        let t1 = subterms1.(i) and t2 = subterms2.(i) in
        generalize t1 t2 table
        && generalize_subterms subterms1 subterms2 table (i + 1)

    let generalize term1 term2 =
      let ub =
        Int_option.elim (Int_option.max (T.ub term1) (T.ub term2)) 0 Fun.id
      in
      generalize term1 term2 (Hashtbl.create (2 * ub))

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
