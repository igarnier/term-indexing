(* The implementation of the zipper is parameterized by a representation of its state.
   This allows us to shave a word per zipper allocation when we don't care about the state. *)
module type Zipper_impl = sig
  type term

  type state

  type 'ctxt t

  val focus : 'ctxt t -> term

  val ctxt : 'ctxt t -> 'ctxt

  val state : 'ctxt t -> state

  val make : term -> 'ctxt -> state -> 'ctxt t

  val set : state -> int -> term -> state

  val get : state -> int -> term option
end

module Make_gen
    (P : Intf.Signature)
    (T : Intf.Term with type prim = P.t)
    (S : Zipper_impl with type term = T.t) :
  Intf.Zipper with type term = T.t and type 'a with_state = 'a * S.state =
struct
  include S

  type t = ctxt S.t

  and ctxt =
    | Zipper_top
    | Zipper_prim1 of P.t * ctxt
    | Zipper_prim2_0 of P.t * T.t * ctxt
    | Zipper_prim2_1 of P.t * T.t * ctxt
    | Zipper_prim3_0 of P.t * T.t * T.t * ctxt
    | Zipper_prim3_1 of P.t * T.t * T.t * ctxt
    | Zipper_prim3_2 of P.t * T.t * T.t * ctxt
    | Zipper_prim of P.t * T.t array * T.t array * ctxt
    | Zipper_set of int * ctxt

  type 'a with_state = 'a * S.state

  let rec pp_ctxt k fmtr (ctxt : ctxt) =
    let open Format in
    match ctxt with
    | Zipper_top -> k fmtr ()
    | Zipper_prim1 (prim, ctxt) ->
        pp_ctxt
          (fun fmtr () -> fprintf fmtr "@[<hv 1>[%a %a]@]" P.pp prim k ())
          fmtr
          ctxt
    | Zipper_prim2_0 (prim, t1, ctxt) ->
        pp_ctxt
          (fun fmtr () ->
            fprintf fmtr "@[<hv 1>[%a %a@ %a]@]" P.pp prim k () T.pp_sexp t1)
          fmtr
          ctxt
    | Zipper_prim2_1 (prim, t0, ctxt) ->
        pp_ctxt
          (fun fmtr () ->
            fprintf fmtr "@[<hv 1>[%a %a@ %a]@]" P.pp prim T.pp_sexp t0 k ())
          fmtr
          ctxt
    | Zipper_prim3_0 (prim, t1, t2, ctxt) ->
        pp_ctxt
          (fun fmtr () ->
            fprintf
              fmtr
              "@[<hv 1>[%a %a@ %a@ %a]@]"
              P.pp
              prim
              k
              ()
              T.pp_sexp
              t1
              T.pp_sexp
              t2)
          fmtr
          ctxt
    | Zipper_prim3_1 (prim, t0, t2, ctxt) ->
        pp_ctxt
          (fun fmtr () ->
            fprintf
              fmtr
              "@[<hv 1>[%a %a@ %a@ %a]@]"
              P.pp
              prim
              T.pp_sexp
              t0
              k
              ()
              T.pp_sexp
              t2)
          fmtr
          ctxt
    | Zipper_prim3_2 (prim, t0, t1, ctxt) ->
        pp_ctxt
          (fun fmtr () ->
            fprintf
              fmtr
              "@[<hv 1>[%a %a@ %a@ %a]@]"
              P.pp
              prim
              T.pp_sexp
              t0
              T.pp_sexp
              t1
              k
              ())
          fmtr
          ctxt
    | Zipper_prim (prim, bef, aft, ctxt) ->
        pp_ctxt
          (fun fmtr () ->
            fprintf
              fmtr
              "@[<hv 1>[%a %a@ %a@ %a]@]"
              P.pp
              prim
              (pp_print_array
                 ~pp_sep:(fun fmtr () -> fprintf fmtr "@ ")
                 T.pp_sexp)
              bef
              k
              ()
              (pp_print_array
                 ~pp_sep:(fun fmtr () -> fprintf fmtr "@ ")
                 T.pp_sexp)
              aft)
          fmtr
          ctxt
    | Zipper_set (v, ctxt) ->
        pp_ctxt
          (fun fmtr () -> fprintf fmtr "@[<hv 1>[set %d@ %a]@]" v k ())
          fmtr
          ctxt

  let pp fmtr z =
    let ctxt = S.ctxt z in
    let focus = S.focus z in
    pp_ctxt
      (fun fmtr () -> Format.fprintf fmtr "[%a]" T.pp_sexp focus)
      fmtr
      ctxt

  let rec compare z1 z2 =
    let c = T.compare (focus z1) (focus z2) in
    if c <> 0 then c else compare_ctxt (ctxt z1) (ctxt z2)

  and compare_ctxt (z1 : ctxt) (z2 : ctxt) =
    if z1 == z2 then 0
    else
      match (z1, z2) with
      | (Zipper_top, Zipper_top) -> 0
      | (Zipper_top, _) -> -1
      | (_, Zipper_top) -> 1
      | (Zipper_prim1 (p1, z1), Zipper_prim1 (p2, z2)) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c else compare_ctxt z1 z2
      | (Zipper_prim1 _, _) -> -1
      | (_, Zipper_prim1 _) -> 1
      | (Zipper_prim2_0 (p1, t1, z1), Zipper_prim2_0 (p2, t2, z2)) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c
          else
            let c = T.compare t1 t2 in
            if c <> 0 then c else compare_ctxt z1 z2
      | (Zipper_prim2_0 _, _) -> -1
      | (_, Zipper_prim2_0 _) -> 1
      | (Zipper_prim2_1 (p1, t1, z1), Zipper_prim2_1 (p2, t2, z2)) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c
          else
            let c = T.compare t1 t2 in
            if c <> 0 then c else compare_ctxt z1 z2
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
              if c <> 0 then c else compare_ctxt z1 z2
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
              if c <> 0 then c else compare_ctxt z1 z2
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
              if c <> 0 then c else compare_ctxt z1 z2
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
              if c <> 0 then c else compare_ctxt z1 z2
      | (Zipper_prim _, _) -> -1
      | (_, Zipper_prim _) -> 1
      | (Zipper_set (v1, z1), Zipper_set (v2, z2)) ->
          let c = Int.compare v1 v2 in
          if c <> 0 then c else compare_ctxt z1 z2

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

  let rec equal z1 z2 =
    T.equal (focus z1) (focus z2) && equal_ctxt (ctxt z1) (ctxt z2)

  and equal_ctxt (z1 : ctxt) (z2 : ctxt) =
    z1 == z2
    ||
    match (z1, z2) with
    | (Zipper_top, Zipper_top) -> true
    | (Zipper_top, _) -> false
    | (_, Zipper_top) -> false
    | (Zipper_prim1 (p1, z1), Zipper_prim1 (p2, z2)) ->
        P.equal p1 p2 && equal_ctxt z1 z2
    | (Zipper_prim1 _, _) -> false
    | (_, Zipper_prim1 _) -> false
    | (Zipper_prim2_0 (p1, t1, z1), Zipper_prim2_0 (p2, t2, z2)) ->
        P.equal p1 p2 && T.equal t1 t2 && equal_ctxt z1 z2
    | (Zipper_prim2_0 _, _) -> false
    | (_, Zipper_prim2_0 _) -> false
    | (Zipper_prim2_1 (p1, t1, z1), Zipper_prim2_1 (p2, t2, z2)) ->
        P.equal p1 p2 && T.equal t1 t2 && equal_ctxt z1 z2
    | (Zipper_prim2_1 _, _) -> false
    | (_, Zipper_prim2_1 _) -> false
    | (Zipper_prim3_0 (p1, t1, t2, z1), Zipper_prim3_0 (p2, u1, u2, z2)) ->
        P.equal p1 p2 && T.equal t1 u1 && T.equal t2 u2 && equal_ctxt z1 z2
    | (Zipper_prim3_0 _, _) -> false
    | (_, Zipper_prim3_0 _) -> false
    | (Zipper_prim3_1 (p1, t1, t2, z1), Zipper_prim3_1 (p2, u1, u2, z2)) ->
        P.equal p1 p2 && T.equal t1 u1 && T.equal t2 u2 && equal_ctxt z1 z2
    | (Zipper_prim3_1 _, _) -> false
    | (_, Zipper_prim3_1 _) -> false
    | (Zipper_prim3_2 (p1, t1, t2, z1), Zipper_prim3_2 (p2, u1, u2, z2)) ->
        P.equal p1 p2 && T.equal t1 u1 && T.equal t2 u2 && equal_ctxt z1 z2
    | (Zipper_prim3_2 _, _) -> false
    | (_, Zipper_prim3_2 _) -> false
    | (Zipper_prim (p1, l1, r1, z1), Zipper_prim (p2, l2, r2, z2)) ->
        P.equal p1 p2 && term_array_equal l1 l2 && term_array_equal r1 r2
        && equal_ctxt z1 z2
    | (Zipper_set (v1, z1), Zipper_set (v2, z2)) ->
        Int.equal v1 v2 && equal_ctxt z1 z2
    | (Zipper_prim _, _) -> false
    | (_, Zipper_prim _) -> false

  and term_array_equal (t1 : T.t array) (t2 : T.t array) =
    let len1 = Array.length t1 in
    let len2 = Array.length t2 in
    if Int.equal len1 len2 then Array.for_all2 T.equal t1 t2 else false

  let of_term (term, state) = make term Zipper_top state

  let cursor z = focus z

  let rec path_of_ctxt : ctxt -> int list -> int list =
   fun zip acc ->
    match zip with
    | Zipper_top -> acc
    | Zipper_prim1 (_, zip) -> path_of_ctxt zip (0 :: acc)
    | Zipper_prim2_0 (_, _, zip) -> path_of_ctxt zip (0 :: acc)
    | Zipper_prim2_1 (_, _, zip) -> path_of_ctxt zip (1 :: acc)
    | Zipper_prim3_0 (_, _, _, zip) -> path_of_ctxt zip (0 :: acc)
    | Zipper_prim3_1 (_, _, _, zip) -> path_of_ctxt zip (1 :: acc)
    | Zipper_prim3_2 (_, _, _, zip) -> path_of_ctxt zip (2 :: acc)
    | Zipper_prim (_, l, _, zip) ->
        let len = Array.length l in
        path_of_ctxt zip (len :: acc)
    | Zipper_set (_v, zip) -> path_of_ctxt zip acc

  let path z = path_of_ctxt (ctxt z) []

  let replace term z = make term (ctxt z) (state z)

  let deref z =
    T.destruct
      (fun _ _ -> None)
      (fun v ->
        let state = state z in
        match get state v with
        | None -> None
        | Some term ->
            let ctxt = Zipper_set (v, ctxt z) in
            Some (make term ctxt state))
      (focus z)

  let rec move_at_exn (z : t) (i : int) : t =
    let ctxt = ctxt z in
    let state = state z in
    T.destruct
      (fun prim subterms ->
        let arity = Array.length subterms in
        if arity = 0 then invalid_arg "move_at_exn"
        else
          (* OPTIM: could use unsafe_get *)
          match (arity, i) with
          | (1, 0) -> make subterms.(0) (Zipper_prim1 (prim, ctxt)) state
          | (2, 0) ->
              make
                subterms.(0)
                (Zipper_prim2_0 (prim, subterms.(1), ctxt))
                state
          | (2, 1) ->
              make
                subterms.(1)
                (Zipper_prim2_1 (prim, subterms.(0), ctxt))
                state
          | (3, 0) ->
              make
                subterms.(0)
                (Zipper_prim3_0 (prim, subterms.(1), subterms.(2), ctxt))
                state
          | (3, 1) ->
              make
                subterms.(1)
                (Zipper_prim3_1 (prim, subterms.(0), subterms.(2), ctxt))
                state
          | (3, 2) ->
              make
                subterms.(2)
                (Zipper_prim3_2 (prim, subterms.(0), subterms.(1), ctxt))
                state
          | (arity, i) ->
              if i >= arity then invalid_arg "move_at_exn"
              else
                let l = Array.sub subterms 0 i in
                let r = Array.sub subterms (i + 1) (arity - i - 1) in
                make subterms.(i) (Zipper_prim (prim, l, r, ctxt)) state)
      (fun _v ->
        match deref z with
        | None -> invalid_arg "move_at_exn"
        | Some z -> move_at_exn z i)
      (focus z)

  let move_at zipper (i : int) =
    try Some (move_at_exn zipper i) with Invalid_argument _ -> None

  let move_up z : t option =
    let term = focus z in
    let state = state z in
    match ctxt z with
    | Zipper_top -> None
    | Zipper_prim1 (prim, ctxt) ->
        Some (make (T.prim prim [| term |]) ctxt state)
    | Zipper_prim2_0 (prim, r, ctxt) ->
        Some (make (T.prim prim [| term; r |]) ctxt state)
    | Zipper_prim2_1 (prim, l, ctxt) ->
        Some (make (T.prim prim [| l; term |]) ctxt state)
    | Zipper_prim3_0 (prim, r, s, ctxt) ->
        Some (make (T.prim prim [| term; r; s |]) ctxt state)
    | Zipper_prim3_1 (prim, l, s, ctxt) ->
        Some (make (T.prim prim [| l; term; s |]) ctxt state)
    | Zipper_prim3_2 (prim, l, r, ctxt) ->
        Some (make (T.prim prim [| l; r; term |]) ctxt state)
    | Zipper_prim (prim, l, r, ctxt) ->
        Some (make (T.prim prim (Array.concat [l; [| term |]; r])) ctxt state)
    | Zipper_set (v, ctxt) ->
        let state = set state v term in
        Some (make (T.var v) ctxt state)

  let rec unzip term ctxt state =
    match ctxt with
    | Zipper_top -> (term, state)
    | Zipper_prim1 (prim, ctxt) -> unzip (T.prim prim [| term |]) ctxt state
    | Zipper_prim2_0 (prim, r, ctxt) ->
        unzip (T.prim prim [| term; r |]) ctxt state
    | Zipper_prim2_1 (prim, l, ctxt) ->
        unzip (T.prim prim [| l; term |]) ctxt state
    | Zipper_prim3_0 (prim, r, s, ctxt) ->
        unzip (T.prim prim [| term; r; s |]) ctxt state
    | Zipper_prim3_1 (prim, l, s, ctxt) ->
        unzip (T.prim prim [| l; term; s |]) ctxt state
    | Zipper_prim3_2 (prim, l, r, ctxt) ->
        unzip (T.prim prim [| l; r; term |]) ctxt state
    | Zipper_prim (prim, l, r, ctxt) ->
        unzip (T.prim prim (Array.concat [l; [| term |]; r])) ctxt state
    | Zipper_set (v, ctxt) ->
        let state = set state v term in
        unzip (T.var v) ctxt state

  let to_term z = unzip (focus z) (ctxt z) (state z)

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
        if T.is_ground term then acc
        else fold_variables_subterms f subterms zipper acc 0)
      (fun v -> f v zipper acc)
      term

  and fold_variables_subterms f subterms zipper acc i =
    if i = Array.length subterms then acc
    else
      let acc = fold_variables f (move_at_exn zipper i) acc in
      fold_variables_subterms f subterms zipper acc (i + 1)
end
[@@ocaml.inline]

(* Simple, stateless zipper  *)
module Make (P : Intf.Signature) (T : Intf.Term with type prim = P.t) :
  Intf.Zipper with type term = T.t and type 'a with_state = 'a = struct
  module Impl : Zipper_impl with type state = unit and type term = T.t = struct
    type term = T.t

    type state = unit

    type 'ctxt t = { term : term; ctxt : 'ctxt }

    let focus z = z.term

    let ctxt z = z.ctxt

    let state _ = ()

    let make term ctxt () = { term; ctxt }

    let set () _ _ = ()

    let get () _ = None
  end

  include Make_gen (P) (T) (Impl)

  type 'a with_state = 'a

  let of_term term = of_term (term, ())

  let to_term z = to_term z |> fst
end

(* Simple, stateless zipper  *)
module Make_stateful
    (P : Intf.Signature)
    (T : Intf.Term with type prim = P.t)
    (S : Intf.Subst with type term = T.t) :
  Intf.Zipper with type term = T.t and type 'a with_state = 'a * S.t = struct
  module Impl : Zipper_impl with type state = S.t and type term = T.t = struct
    type term = T.t

    type state = S.t

    type 'ctxt t = { term : term; ctxt : 'ctxt; state : S.t }

    let focus z = z.term

    let ctxt z = z.ctxt

    let state z = z.state

    let make term ctxt state = { term; ctxt; state }

    (* TODO: normalize argument order, default empty state argument for make *)
    let set state k v = S.add k v state

    let get state k = S.get k state
  end

  include Make_gen (P) (T) (Impl)
end
