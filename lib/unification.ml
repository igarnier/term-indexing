module Make
    (P : Intf.Signature)
    (T : Intf.Term_core with type prim = P.t)
    (S : Intf.Subst with type term = T.t) :
  Intf.Unification with type term = T.t and type subst = S.t = struct
  type term = T.t

  type subst = S.t

  type state = { subst : S.t; uf : Uf.Map_based.t }

  exception Cannot_unify

  let subst { subst; _ } = subst

  let empty () = { subst = S.empty (); uf = Uf.Map_based.empty () }

  let get_repr var { subst; uf } =
    let repr_var = Uf.Map_based.find uf var in
    let repr_term = S.eval repr_var subst in
    (repr_term, repr_var)

  let rec unify_exn (term1 : term) (term2 : term) (state : state) =
    if term1 == term2 then state
    else
      T.destruct2
        (fun prim1 subterms1 prim2 subterms2 ->
          if P.equal prim1 prim2 then
            (* invariant: [Array.length subterms1 = Array.length subterms2] *)
            unify_subterms subterms1 subterms2 state 0
          else raise Cannot_unify)
        (fun _prim _subterms v ->
          let (term_opt, repr_var) = get_repr v state in
          match term_opt with
          | None -> { state with subst = S.add repr_var term1 state.subst }
          | Some term -> unify_exn term1 term state)
        (fun v _prim _subterms ->
          let (term_opt, repr_var) = get_repr v state in
          match term_opt with
          | None -> { state with subst = S.add repr_var term2 state.subst }
          | Some term -> unify_exn term term2 state)
        (fun v1 v2 ->
          (* v1 <> v2 *)
          let (vrepr, uf) = Uf.Map_based.union state.uf v1 v2 in
          let (term1_opt, _) = get_repr v1 state in
          let (term2_opt, _) = get_repr v2 state in
          match (term1_opt, term2_opt) with
          | (None, None) -> { state with uf }
          | (Some repr, None) | (None, Some repr) ->
              let subst = S.add vrepr repr state.subst in
              { uf; subst }
          | (Some repr1, Some repr2) ->
              let state = unify_exn repr1 repr2 { state with uf } in
              { state with uf })
        term1
        term2

  and unify_subterms subterms1 subterms2 (state : state) i =
    if i = Array.length subterms1 then state
    else
      let t1 = subterms1.(i) and t2 = subterms2.(i) in
      let state = unify_exn t1 t2 state in
      unify_subterms subterms1 subterms2 state (i + 1)

  let unify term1 term2 state =
    try Some (unify_exn term1 term2 state) with Cannot_unify -> None

  let rec generalizes (term1 : term) (term2 : term)
      (table : (int, term) Hashtbl.t) =
    T.destruct
      (fun prim1 subterms1 ->
        T.destruct
          (fun prim2 subterms2 ->
            if P.equal prim1 prim2 then
              (* invariant: [Array.length subterms1 = Array.length subterms2] *)
              generalize_subterms subterms1 subterms2 table 0
            else false)
          (fun _v -> false)
          term2)
      (fun v ->
        match Hashtbl.find_opt table v with
        | None ->
            Hashtbl.add table v term2 ;
            true
        | Some t -> T.equal t term2)
      term1

  and generalize_subterms subterms1 subterms2 table i =
    if i = Array.length subterms1 then true
    else
      let t1 = subterms1.(i) and t2 = subterms2.(i) in
      generalizes t1 t2 table
      && generalize_subterms subterms1 subterms2 table (i + 1)

  let generalizes term1 term2 = generalizes term1 term2 (Hashtbl.create 11)

  let unify_subst_exn (subst : subst) (state : state) =
    Seq.fold_left
      (fun state (v, t) ->
        let (term_opt, repr_var) = get_repr v state in
        match term_opt with
        | None -> { state with subst = S.add repr_var t state.subst }
        | Some term ->
            let state = { state with subst = S.add repr_var t state.subst } in
            unify_exn term t state)
      state
      (S.to_seq subst)

  let unify_subst (subst : subst) (state : state) =
    try Some (unify_subst_exn subst state) with Cannot_unify -> None

  exception Occurs_check

  let unfold state term =
    let rec loop visited (state : state) (term : term) =
      T.destruct
        (fun prim subterms ->
          (* Optimization: if the term is ground then no need to recurse. *)
          if T.is_ground term then term
          else T.prim prim (Array.map (loop visited state) subterms))
        (fun v ->
          let repr = Uf.Map_based.find state.uf v in
          match S.eval repr state.subst with
          | None -> term
          | Some term ->
              if Int_set.mem repr visited then raise Occurs_check
              else
                let visited = Int_set.add repr visited in
                loop visited state term)
        term
    in
    loop Int_set.empty state term
end
