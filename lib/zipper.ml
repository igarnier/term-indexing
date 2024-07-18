module Make (P : Intf.Signature) (T : Intf.Term with type prim = P.t) :
  Intf.Zipper with type term = T.t = struct
  type term = T.t

  type t = T.t * Path.t * zip

  and zip =
    | Zipper_top
    | Zipper_prim1 of P.t * zip
    | Zipper_prim2_0 of P.t * T.t * zip
    | Zipper_prim2_1 of P.t * T.t * zip
    | Zipper_prim3_0 of P.t * T.t * T.t * zip
    | Zipper_prim3_1 of P.t * T.t * T.t * zip
    | Zipper_prim3_2 of P.t * T.t * T.t * zip
    | Zipper_prim of P.t * T.t array * T.t array * zip

  let of_term term = (term, Path.root, Zipper_top)

  let cursor (term, _, _) = term

  let path (_, path, _) = path

  let replace term (_term, path, zip) = (term, path, zip)

  let move_at (term, path, zip) (i : int) =
    T.destruct
      (fun prim subterms ->
        let arity = Array.length subterms in
        if arity = 0 then None
        else
          let path = Path.at_index i path in
          match (arity, i) with
          | (1, _) -> Some (subterms.(0), path, Zipper_prim1 (prim, zip))
          | (2, 0) ->
              Some (subterms.(0), path, Zipper_prim2_0 (prim, subterms.(1), zip))
          | (2, 1) ->
              Some (subterms.(1), path, Zipper_prim2_1 (prim, subterms.(0), zip))
          | (3, 0) ->
              Some
                ( subterms.(0),
                  path,
                  Zipper_prim3_0 (prim, subterms.(1), subterms.(2), zip) )
          | (3, 1) ->
              Some
                ( subterms.(1),
                  path,
                  Zipper_prim3_1 (prim, subterms.(0), subterms.(2), zip) )
          | (3, 2) ->
              Some
                ( subterms.(2),
                  path,
                  Zipper_prim3_2 (prim, subterms.(0), subterms.(1), zip) )
          | (arity, i) ->
              if i >= arity then None
              else
                let l = Array.sub subterms 0 i in
                let r = Array.sub subterms (i + 1) (arity - i - 1) in
                Some (subterms.(i), path, Zipper_prim (prim, l, r, zip)))
      (fun _ -> None)
      term

  let move_up (term, path, zip) =
    match (zip, path) with
    | (Zipper_top, _) -> None
    | (Zipper_prim1 (prim, zip), Path.At_index (_, path)) ->
        Some (T.prim prim [| term |], path, zip)
    | (Zipper_prim2_0 (prim, r, zip), Path.At_index (_, path)) ->
        Some (T.prim prim [| term; r |], path, zip)
    | (Zipper_prim2_1 (prim, l, zip), Path.At_index (_, path)) ->
        Some (T.prim prim [| l; term |], path, zip)
    | (Zipper_prim3_0 (prim, r, s, zip), Path.At_index (_, path)) ->
        Some (T.prim prim [| term; r; s |], path, zip)
    | (Zipper_prim3_1 (prim, l, s, zip), Path.At_index (_, path)) ->
        Some (T.prim prim [| l; term; s |], path, zip)
    | (Zipper_prim3_2 (prim, l, r, zip), Path.At_index (_, path)) ->
        Some (T.prim prim [| l; r; term |], path, zip)
    | (Zipper_prim (prim, l, r, zip), Path.At_index (_, path)) ->
        Some (T.prim prim (Array.concat [l; [| term |]; r]), path, zip)
    | (_, Path.Root) -> assert false

  let rec unzip term zip =
    match zip with
    | Zipper_top -> term
    | Zipper_prim1 (prim, zip) -> unzip (T.prim prim [| term |]) zip
    | Zipper_prim2_0 (prim, r, zip) -> unzip (T.prim prim [| term; r |]) zip
    | Zipper_prim2_1 (prim, l, zip) -> unzip (T.prim prim [| l; term |]) zip
    | Zipper_prim3_0 (prim, r, s, zip) ->
        unzip (T.prim prim [| term; r; s |]) zip
    | Zipper_prim3_1 (prim, l, s, zip) ->
        unzip (T.prim prim [| l; term; s |]) zip
    | Zipper_prim3_2 (prim, l, r, zip) ->
        unzip (T.prim prim [| l; r; term |]) zip
    | Zipper_prim (prim, l, r, zip) ->
        unzip (T.prim prim (Array.concat [l; [| term |]; r])) zip

  let to_term (term, _, zip) = unzip term zip
end
