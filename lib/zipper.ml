module Make (P : Intf.Signature) (T : Intf.Term with type prim = P.t) :
  Intf.Zipper with type term = T.t = struct
  type term = T.t

  type t = T.t * zip

  and zip =
    | Zipper_top
    | Zipper_prim1 of P.t * zip
    | Zipper_prim2_0 of P.t * T.t * zip
    | Zipper_prim2_1 of P.t * T.t * zip
    | Zipper_prim3_0 of P.t * T.t * T.t * zip
    | Zipper_prim3_1 of P.t * T.t * T.t * zip
    | Zipper_prim3_2 of P.t * T.t * T.t * zip
    | Zipper_prim of P.t * T.t array * T.t array * zip

  let rec compare ((t1, z1) : t) ((t2, z2) : t) =
    let c = T.compare t1 t2 in
    if c <> 0 then c else compare_zip z1 z2

  and compare_zip (z1 : zip) (z2 : zip) =
    if z1 == z2 then 0
    else
      match (z1, z2) with
      | (Zipper_top, Zipper_top) -> 0
      | (Zipper_top, _) -> -1
      | (_, Zipper_top) -> 1
      | (Zipper_prim1 (p1, z1), Zipper_prim1 (p2, z2)) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c else compare_zip z1 z2
      | (Zipper_prim1 _, _) -> -1
      | (_, Zipper_prim1 _) -> 1
      | (Zipper_prim2_0 (p1, t1, z1), Zipper_prim2_0 (p2, t2, z2)) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c
          else
            let c = T.compare t1 t2 in
            if c <> 0 then c else compare_zip z1 z2
      | (Zipper_prim2_0 _, _) -> -1
      | (_, Zipper_prim2_0 _) -> 1
      | (Zipper_prim2_1 (p1, t1, z1), Zipper_prim2_1 (p2, t2, z2)) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c
          else
            let c = T.compare t1 t2 in
            if c <> 0 then c else compare_zip z1 z2
      | (Zipper_prim2_1 _, _) -> -1
      | (_, Zipper_prim2_1 _) -> 1
      | (Zipper_prim3_0 (p1, t1, t2, z1), Zipper_prim3_0 (p2, u1, u2, z2)) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c
          else
            let c = T.compare t1 u1 in
            if c <> 0 then c
            else
              let c = T.compare t2 u2 in
              if c <> 0 then c else compare_zip z1 z2
      | (Zipper_prim3_0 _, _) -> -1
      | (_, Zipper_prim3_0 _) -> 1
      | (Zipper_prim3_1 (p1, t1, t2, z1), Zipper_prim3_1 (p2, u1, u2, z2)) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c
          else
            let c = T.compare t1 u1 in
            if c <> 0 then c
            else
              let c = T.compare t2 u2 in
              if c <> 0 then c else compare_zip z1 z2
      | (Zipper_prim3_1 _, _) -> -1
      | (_, Zipper_prim3_1 _) -> 1
      | (Zipper_prim3_2 (p1, t1, t2, z1), Zipper_prim3_2 (p2, u1, u2, z2)) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c
          else
            let c = T.compare t1 u1 in
            if c <> 0 then c
            else
              let c = T.compare t2 u2 in
              if c <> 0 then c else compare_zip z1 z2
      | (Zipper_prim3_2 _, _) -> -1
      | (_, Zipper_prim3_2 _) -> 1
      | (Zipper_prim (p1, l1, r1, z1), Zipper_prim (p2, l2, r2, z2)) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c
          else
            let c = term_array_compare l1 l2 in
            if c <> 0 then c
            else
              let c = term_array_compare r1 r2 in
              if c <> 0 then c else compare_zip z1 z2

  and term_array_compare (t1 : T.t array) (t2 : T.t array) =
    let len1 = Array.length t1 in
    let len2 = Array.length t2 in
    if len1 <> len2 then len1 - len2
    else
      let rec aux i =
        if i = len1 then 0
        else
          let c = T.compare t1.(i) t2.(i) in
          if c <> 0 then c else aux (i + 1)
      in
      aux 0

  let rec equal ((t1, z1) : t) ((t2, z2) : t) = T.equal t1 t2 && equal_zip z1 z2

  and equal_zip (z1 : zip) (z2 : zip) =
    z1 == z2
    ||
    match (z1, z2) with
    | (Zipper_top, Zipper_top) -> true
    | (Zipper_top, _) -> false
    | (_, Zipper_top) -> false
    | (Zipper_prim1 (p1, z1), Zipper_prim1 (p2, z2)) ->
        P.equal p1 p2 && equal_zip z1 z2
    | (Zipper_prim1 _, _) -> false
    | (_, Zipper_prim1 _) -> false
    | (Zipper_prim2_0 (p1, t1, z1), Zipper_prim2_0 (p2, t2, z2)) ->
        P.equal p1 p2 && T.equal t1 t2 && equal_zip z1 z2
    | (Zipper_prim2_0 _, _) -> false
    | (_, Zipper_prim2_0 _) -> false
    | (Zipper_prim2_1 (p1, t1, z1), Zipper_prim2_1 (p2, t2, z2)) ->
        P.equal p1 p2 && T.equal t1 t2 && equal_zip z1 z2
    | (Zipper_prim2_1 _, _) -> false
    | (_, Zipper_prim2_1 _) -> false
    | (Zipper_prim3_0 (p1, t1, t2, z1), Zipper_prim3_0 (p2, u1, u2, z2)) ->
        P.equal p1 p2 && T.equal t1 u1 && T.equal t2 u2 && equal_zip z1 z2
    | (Zipper_prim3_0 _, _) -> false
    | (_, Zipper_prim3_0 _) -> false
    | (Zipper_prim3_1 (p1, t1, t2, z1), Zipper_prim3_1 (p2, u1, u2, z2)) ->
        P.equal p1 p2 && T.equal t1 u1 && T.equal t2 u2 && equal_zip z1 z2
    | (Zipper_prim3_1 _, _) -> false
    | (_, Zipper_prim3_1 _) -> false
    | (Zipper_prim3_2 (p1, t1, t2, z1), Zipper_prim3_2 (p2, u1, u2, z2)) ->
        P.equal p1 p2 && T.equal t1 u1 && T.equal t2 u2 && equal_zip z1 z2
    | (Zipper_prim3_2 _, _) -> false
    | (_, Zipper_prim3_2 _) -> false
    | (Zipper_prim (p1, l1, r1, z1), Zipper_prim (p2, l2, r2, z2)) ->
        P.equal p1 p2 && term_array_equal l1 l2 && term_array_equal r1 r2
        && equal_zip z1 z2

  and term_array_equal (t1 : T.t array) (t2 : T.t array) =
    let len1 = Array.length t1 in
    let len2 = Array.length t2 in
    if Int.equal len1 len2 then Array.for_all2 T.equal t1 t2 else false

  let hash (term, zip) = Hashtbl.hash (T.hash term, zip)

  let of_term term = (term, Zipper_top)

  let cursor (term, _) = term

  let rec path_of_zip : zip -> int list -> int list =
   fun zip acc ->
    match zip with
    | Zipper_top -> acc
    | Zipper_prim1 (_, zip) -> path_of_zip zip (0 :: acc)
    | Zipper_prim2_0 (_, _, zip) -> path_of_zip zip (0 :: acc)
    | Zipper_prim2_1 (_, _, zip) -> path_of_zip zip (1 :: acc)
    | Zipper_prim3_0 (_, _, _, zip) -> path_of_zip zip (0 :: acc)
    | Zipper_prim3_1 (_, _, _, zip) -> path_of_zip zip (1 :: acc)
    | Zipper_prim3_2 (_, _, _, zip) -> path_of_zip zip (2 :: acc)
    | Zipper_prim (_, l, _, zip) ->
        let len = Array.length l in
        path_of_zip zip (len :: acc)

  let path (_, zip) = path_of_zip zip []

  let replace term (_term, zip) = (term, zip)

  let move_at_exn (term, zip) (i : int) =
    T.destruct
      (fun prim subterms ->
        let arity = Array.length subterms in
        if arity = 0 then invalid_arg "move_at_exn"
        else
          match (arity, i) with
          | (1, _) -> (subterms.(0), Zipper_prim1 (prim, zip))
          | (2, 0) -> (subterms.(0), Zipper_prim2_0 (prim, subterms.(1), zip))
          | (2, 1) -> (subterms.(1), Zipper_prim2_1 (prim, subterms.(0), zip))
          | (3, 0) ->
              ( subterms.(0),
                Zipper_prim3_0 (prim, subterms.(1), subterms.(2), zip) )
          | (3, 1) ->
              ( subterms.(1),
                Zipper_prim3_1 (prim, subterms.(0), subterms.(2), zip) )
          | (3, 2) ->
              ( subterms.(2),
                Zipper_prim3_2 (prim, subterms.(0), subterms.(1), zip) )
          | (arity, i) ->
              if i >= arity then invalid_arg "move_at_exn"
              else
                let l = Array.sub subterms 0 i in
                let r = Array.sub subterms (i + 1) (arity - i - 1) in
                (subterms.(i), Zipper_prim (prim, l, r, zip)))
      (fun _ -> assert false)
      term

  let move_at zipper (i : int) =
    try Some (move_at_exn zipper i) with Invalid_argument _ -> None

  let move_up (term, zip) =
    match zip with
    | Zipper_top -> None
    | Zipper_prim1 (prim, zip) -> Some (T.prim prim [| term |], zip)
    | Zipper_prim2_0 (prim, r, zip) -> Some (T.prim prim [| term; r |], zip)
    | Zipper_prim2_1 (prim, l, zip) -> Some (T.prim prim [| l; term |], zip)
    | Zipper_prim3_0 (prim, r, s, zip) ->
        Some (T.prim prim [| term; r; s |], zip)
    | Zipper_prim3_1 (prim, l, s, zip) ->
        Some (T.prim prim [| l; term; s |], zip)
    | Zipper_prim3_2 (prim, l, r, zip) ->
        Some (T.prim prim [| l; r; term |], zip)
    | Zipper_prim (prim, l, r, zip) ->
        Some (T.prim prim (Array.concat [l; [| term |]; r]), zip)

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

  let to_term (term, zip) = unzip term zip

  let rec fold f zipper acc =
    let acc = f zipper acc in
    T.destruct
      (fun _ subterms -> fold_subterms f subterms zipper acc 0)
      (fun _ -> acc)
      (cursor zipper)

  and fold_subterms f subterms zipper acc i =
    if i = Array.length subterms then acc
    else
      let acc = fold f (move_at_exn zipper i) acc in
      fold_subterms f subterms zipper acc (i + 1)

  let rec fold_variables f zipper acc =
    let term = cursor zipper in
    T.destruct
      (fun _ subterms ->
        let ub = T.ub term in
        if Int_option.is_none ub then acc
        else fold_variables_subterms f subterms zipper acc 0)
      (fun v -> f v zipper acc)
      term

  and fold_variables_subterms f subterms zipper acc i =
    if i = Array.length subterms then acc
    else
      let acc = fold_variables f (move_at_exn zipper i) acc in
      fold_variables_subterms f subterms zipper acc (i + 1)
end
