(* Pattern-matching terms. *)

exception Invalid_pattern

type focused = Focused

let _focused = Focused

type unfocused = Unfocused

let _unfocused = Unfocused

type 'f focus_tag =
  | Focused_tag : focused focus_tag
  | Unfocused_tag : unfocused focus_tag

type ('f1, 'f2, 'f) join =
  | UU : (unfocused, unfocused, unfocused) join
  | FU : (focused, unfocused, focused) join
  | UF : (unfocused, focused, focused) join
  | FF : (focused, focused, focused) join

type (_, _) pattern_desc =
  | Patt_prim : 'p prim_pred * ('p, 'f) pattern_list -> ('p, 'f) pattern_desc
  | Patt_var : int option -> ('p, unfocused) pattern_desc
  | Patt_any : ('p, unfocused) pattern_desc
  | Patt_focus : ('p, unfocused) pattern -> ('p, focused) pattern_desc

and ('p, 'f) pattern = { patt_desc : ('p, 'f) pattern_desc; patt_uid : int }

and (_, _) pattern_list =
  | Patt_list_empty : ('p, unfocused) pattern_list
  | Patt_list_any : ('p, unfocused) pattern_list
  | Patt_list_cons :
      ('p, 'f1) pattern * ('p, 'f2) pattern_list * ('f1, 'f2, 'f) join
      -> ('p, 'f) pattern_list

and 'p prim_pred = Patt_prim_equal of 'p | Patt_pred of ('p -> bool)

(* type 'p focused_pattern = ('p, focused) pattern *)

(* type 'p unfocused_pattern = ('p, unfocused) pattern *)

let rec get_focus : type f. ('p, f) pattern -> f focus_tag =
 fun { patt_desc; _ } ->
  match patt_desc with
  | Patt_prim (_prim, subpatts) -> get_focus_list subpatts
  | Patt_var _ -> Unfocused_tag
  | Patt_any -> Unfocused_tag
  | Patt_focus _ -> Focused_tag

and get_focus_list : type f. ('p, f) pattern_list -> f focus_tag =
 fun patt_list ->
  match patt_list with
  | Patt_list_empty -> Unfocused_tag
  | Patt_list_any -> Unfocused_tag
  | Patt_list_cons (_, _, wit) -> (
      match wit with
      | UU -> Unfocused_tag
      | FU -> Focused_tag
      | UF -> Focused_tag
      | FF -> Focused_tag)

module Make_raw
    (P : Intf.Signature)
    (T : Intf.Term with type prim = P.t and type t = P.t Term.term)
    (Z : Intf.Zipper with type term = T.t) =
struct
  type prim = P.t

  type zipper = Z.t

  type t = Ex_patt : (prim, 'f) pattern -> t [@@ocaml.unboxed]

  type matching = t list

  type plist = Ex_patt_list : (prim, 'f) pattern_list -> plist
  [@@ocaml.unboxed]

  type term = T.t

  let fold_range f acc bound =
    let rec loop f acc bound i =
      if Int.equal i bound then acc else loop f (f i acc) bound (i + 1)
    in
    loop f acc bound 0
  [@@ocaml.inline]

  let arity zipper =
    let term = Z.cursor zipper in
    T.destruct (fun _ subterms -> Array.length subterms) (fun _ -> 0) term

  let rec get_zippers_of_focuses :
      (prim, focused) pattern -> zipper -> zipper list -> zipper list =
   fun { patt_desc; _ } zipper acc ->
    match patt_desc with
    | Patt_prim (_, subterms) ->
        get_zippers_of_focuses_list subterms zipper 0 acc
    | Patt_focus _ -> zipper :: acc

  and get_zippers_of_focuses_list :
      (prim, focused) pattern_list ->
      zipper ->
      int ->
      zipper list ->
      zipper list =
   fun patt_list zipper index acc ->
    match patt_list with
    | Patt_list_cons (prim, tail, wit) -> (
        match wit with
        | FU ->
            let prim_zipper = Z.move_at_exn zipper index in
            get_zippers_of_focuses prim prim_zipper acc
        | UF -> get_zippers_of_focuses_list tail zipper (index + 1) acc
        | FF ->
            let prim_zipper = Z.move_at_exn zipper index in
            let acc = get_zippers_of_focuses prim prim_zipper acc in
            get_zippers_of_focuses_list tail zipper (index + 1) acc)

  let rec pattern_matches_aux : type f. (prim, f) pattern -> term -> bool =
   fun patt node ->
    match (patt.patt_desc, node.Hashcons.node) with
    | (Patt_focus patt, _) -> pattern_matches_aux patt node
    | (Patt_any, _) -> true
    | (Patt_var None, Var _j) -> true
    | (Patt_var (Some i), Var j) -> i = j
    | (Patt_var _, _) -> false
    | (Patt_prim _, Var _) -> false
    | (Patt_prim (hpred, subpatts), Prim (prim, subterms, _)) -> (
        match hpred with
        | Patt_prim_equal h ->
            if P.equal h prim then list_matches subpatts subterms 0 else false
        | Patt_pred pred ->
            if pred prim then list_matches subpatts subterms 0 else false)

  and list_matches : type f. (prim, f) pattern_list -> term array -> int -> bool
      =
   fun patts nodes index ->
    let remaining = Array.length nodes - index in
    match patts with
    | Patt_list_any -> true
    | Patt_list_empty -> remaining = 0
    | Patt_list_cons (p, lpatt, _) ->
        if remaining <= 0 then false
        else
          let n = Array.get nodes index in
          pattern_matches_aux p n && list_matches lpatt nodes (index + 1)

  let pattern_matches (patt : t) (node : term) =
    match patt with Ex_patt patt -> pattern_matches_aux patt node

  exception Found of t * zipper

  let first_match_aux matching zipper =
    let rec loop : matching -> zipper -> unit =
     fun matching zipper ->
      let arity = arity zipper in
      for i = 0 to arity - 1 do
        let zipper = Z.move_at_exn zipper i in
        loop matching zipper
      done ;
      let node = Z.cursor zipper in
      match List.find_opt (fun patt -> pattern_matches patt node) matching with
      | None -> ()
      | Some patt -> raise (Found (patt, zipper))
    in
    try
      loop matching zipper ;
      None
    with Found (patt, zipper) -> Some (patt, zipper)

  let rec all_matches_aux :
      matching -> zipper -> (t * zipper) list -> (t * zipper) list =
   fun matching zipper acc ->
    let arity = arity zipper in
    let acc =
      fold_range
        (fun index acc ->
          let zipper = Z.move_at_exn zipper index in
          all_matches_aux matching zipper acc)
        acc
        arity
    in
    let node = Z.cursor zipper in
    match List.find_opt (fun patt -> pattern_matches patt node) matching with
    | None -> acc
    | Some patt -> (patt, zipper) :: acc

  let refine_focused pattern zipper =
    match pattern with
    | Ex_patt patt -> (
        match get_focus patt with
        | Unfocused_tag -> []
        | Focused_tag -> get_zippers_of_focuses patt zipper [])

  let all_matches matching term =
    all_matches_aux matching (Z.of_term term) []
    |> List.concat_map (fun ((Ex_patt patt as pattern), zipper) ->
           match get_focus patt with
           | Unfocused_tag -> [zipper]
           | Focused_tag -> refine_focused pattern zipper)

  let first_match matching term =
    match first_match_aux matching (Z.of_term term) with
    | None -> []
    | Some ((Ex_patt patt as pattern), zipper) -> (
        match get_focus patt with
        | Unfocused_tag -> [zipper]
        | Focused_tag -> refine_focused pattern zipper)

  let uid_gen =
    let x = ref 0 in
    fun () ->
      let r = !x in
      incr x ;
      r

  let ex_patt patt_desc = Ex_patt { patt_desc; patt_uid = uid_gen () }

  let prim prim patts =
    match patts with
    | Ex_patt_list patts -> ex_patt (Patt_prim (Patt_prim_equal prim, patts))

  let prim_pred prim_pred patts =
    match patts with
    | Ex_patt_list patts -> ex_patt (Patt_prim (Patt_pred prim_pred, patts))

  let any_var = ex_patt (Patt_var None)

  let var id = ex_patt (Patt_var (Some id))

  let any = ex_patt Patt_any

  let focus patt =
    match patt with
    | Ex_patt patt -> (
        match get_focus patt with
        | Focused_tag -> raise Invalid_pattern
        | Unfocused_tag -> ex_patt (Patt_focus patt))

  let list_any = Ex_patt_list Patt_list_any

  let list_empty = Ex_patt_list Patt_list_empty

  let list_cons (Ex_patt patt) (Ex_patt_list patt_list) =
    match get_focus patt with
    | Focused_tag -> (
        match get_focus_list patt_list with
        | Focused_tag -> Ex_patt_list (Patt_list_cons (patt, patt_list, FF))
        | Unfocused_tag -> Ex_patt_list (Patt_list_cons (patt, patt_list, FU)))
    | Unfocused_tag -> (
        match get_focus_list patt_list with
        | Focused_tag -> Ex_patt_list (Patt_list_cons (patt, patt_list, UF))
        | Unfocused_tag -> Ex_patt_list (Patt_list_cons (patt, patt_list, UU)))

  let ( @. ) = list_cons

  let rec pp_patt : type f. Format.formatter -> (prim, f) pattern -> unit =
   fun fmtr patt ->
    match patt.patt_desc with
    | Patt_prim (Patt_prim_equal prim, subpatts) ->
        Format.fprintf fmtr "[%a](%a)" P.pp prim pp_patt_list subpatts
    | Patt_prim (Patt_pred _, subpatts) ->
        Format.fprintf fmtr "[opaque_pred](%a)" pp_patt_list subpatts
    | Patt_var None -> Format.fprintf fmtr "[var any]"
    | Patt_var (Some id) -> Format.fprintf fmtr "[var %d]" id
    | Patt_any -> Format.pp_print_string fmtr "_"
    | Patt_focus patt -> Format.fprintf fmtr "[> %a <]" pp_patt patt

  and pp_patt_list : type f. Format.formatter -> (prim, f) pattern_list -> unit
      =
   fun fmtr patts ->
    match patts with
    | Patt_list_empty -> Format.pp_print_string fmtr "[]"
    | Patt_list_any -> Format.pp_print_string fmtr "_"
    | Patt_list_cons (hd, tail, _) ->
        Format.fprintf fmtr "%a :: %a" pp_patt hd pp_patt_list tail

  let pp (fmtr : Format.formatter) (patt : t) =
    match patt with Ex_patt patt -> pp_patt fmtr patt

  let uid (Ex_patt patt) = patt.patt_uid
end

module Make : functor
  (P : Intf.Signature)
  (T : Intf.Term with type prim = P.t and type t = P.t Term.term)
  (Z : Intf.Zipper with type term = T.t)
  ->
  Intf.Pattern
    with type prim = P.t
     and type term = P.t Term.term
     and type zipper = Z.t =
  Make_raw

module Make_with_hash_consing
    (P : Intf.Signature)
    (T : Intf.Term with type prim = P.t and type t = P.t Term.term)
    (Z : Intf.Zipper with type term = T.t) : sig
  include
    Intf.Pattern
      with type prim = P.t
       and type term = P.t Term.term
       and type zipper = Z.t

  val all_matches_with_hash_consing : t -> term -> zipper list
end = struct
  include Make_raw (P) (T) (Z)

  type key = { patt_uid : int; node_tag : int }

  let table : (key, zipper list) Hashtbl.t = Hashtbl.create 7919

  let rec all_matches_aux : t -> term -> zipper -> zipper list -> zipper list =
   fun patt node zipper acc ->
    let patt_uid = uid patt in
    let node_tag = node.tag in
    match Hashtbl.find_opt table { patt_uid; node_tag } with
    | None ->
        let acc =
          fold_range
            (fun index acc ->
              let zipper = Z.move_at_exn zipper index in
              let subterm = Z.cursor zipper in
              all_matches_aux patt subterm zipper acc)
            acc
            (arity zipper)
        in
        if pattern_matches patt node then zipper :: acc else acc
    | Some res -> List.rev_append res acc

  let all_matches_with_hash_consing pattern term =
    match pattern with
    | Ex_patt patt -> (
        match get_focus patt with
        | Unfocused_tag -> all_matches_aux pattern term (Z.of_term term) []
        | Focused_tag ->
            let zippers = all_matches_aux pattern term (Z.of_term term) [] in
            List.fold_left
              (fun acc context_zipper ->
                get_zippers_of_focuses patt context_zipper acc)
              []
              zippers)
end
