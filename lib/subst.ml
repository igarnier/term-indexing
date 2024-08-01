module Vec = Containers.Vector

module Make
    (P : Intf.Signature)
    (M : Intf.Map with type key = int)
    (T : Intf.Term_core with type prim = P.t) :
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

  let eval = M.find_opt

  let eval_exn v subst =
    match M.find_opt v subst with None -> raise Not_found | Some t -> t

  let add k term subst =
    T.destruct
      (fun _prim _subterms -> ())
      (fun v' -> if Int.equal k v' then invalid_arg "add")
      term ;
    M.add k term subst

  let unsafe_add k term subst = M.add k term subst

  let of_seq seq = Seq.fold_left (fun acc (v, t) -> add v t acc) (empty ()) seq

  (* /!\ no occur check, the substitution should be well-founded or this will stack overflow *)
  let rec lift subst (term : term) =
    T.destruct
      (fun prim subterms ->
        if T.is_ground term then term
        else
          T.prim prim (Array.map (fun subterm -> lift subst subterm) subterms))
      (fun v ->
        match eval v subst with None -> term | Some term -> lift subst term)
      term

  let union = M.union
end
