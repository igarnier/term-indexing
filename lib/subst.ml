module Vec = Containers.Vector

module Make
    (P : Intf.Signature)
    (M : Intf.Map with type key = int)
    (T : Intf.Term with type prim = P.t and type t = P.t Term.term) :
  Intf.Subst with type term = T.t = struct
  type term = T.t

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
      let repr_var = Uf.Map_based.find uf var in
      let repr_term = eval repr_var subst in
      (repr_term, repr_var)

    let rec unify_exn (term1 : term) (term2 : term) (state : state) =
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
            let (vrepr, uf) = Uf.Map_based.union state.uf v1 v2 in
            let (term1_opt, _) = get_repr v1 state in
            let (term2_opt, _) = get_repr v2 state in
            match (term1_opt, term2_opt) with
            | (None, None) -> { state with uf }
            | (Some repr, None) | (None, Some repr) ->
                let subst = add vrepr repr state.subst in
                { uf; subst }
            | (Some repr1, Some repr2) ->
                let state = unify_exn repr1 repr2 { state with uf } in
                { state with uf })
        | (Term.Var v, Term.Prim _) -> (
            let (term_opt, repr_var) = get_repr v state in
            match term_opt with
            | None -> { state with subst = add repr_var term2 state.subst }
            | Some term -> unify_exn term term2 state)
        | (Term.Prim _, Term.Var v) -> (
            let (term_opt, repr_var) = get_repr v state in
            match term_opt with
            | None -> { state with subst = add repr_var term1 state.subst }
            | Some term -> unify_exn term1 term state)

    and unify_subterms subterms1 subterms2 (state : state) i =
      if i = Array.length subterms1 then state
      else
        let t1 = subterms1.(i) and t2 = subterms2.(i) in
        let state = unify_exn t1 t2 state in
        unify_subterms subterms1 subterms2 state (i + 1)

    let unify term1 term2 state =
      try Some (unify_exn term1 term2 state) with Cannot_unify -> None

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

    let unify_subst_exn (subst : t) (state : state) =
      Seq.fold_left
        (fun state (v, t) ->
          let (term_opt, repr_var) = get_repr v state in
          match term_opt with
          | None -> { state with subst = add repr_var t state.subst }
          | Some term ->
              let state = { state with subst = add repr_var t state.subst } in
              unify_exn term t state)
        state
        (M.to_seq subst)

    let unify_subst (subst : t) (state : state) =
      try Some (unify_subst_exn subst state) with Cannot_unify -> None
  end
end
