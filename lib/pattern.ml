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
  | Patt_var : int -> ('p, unfocused) pattern_desc
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
    (T : Intf.Term with type prim = P.t and type t = P.t Term.term) =
struct
  type prim = P.t

  type path = Path.t

  type t = Ex_patt : (prim, 'f) pattern -> t [@@ocaml.unboxed]

  type matching = t list

  type plist = Ex_patt_list : (prim, 'f) pattern_list -> plist
  [@@ocaml.unboxed]

  type term = T.t

  let rec get_paths_of_focuses :
      (prim, focused) pattern -> Path.t -> Path.t list -> Path.t list =
   fun { patt_desc; _ } position acc ->
    match patt_desc with
    | Patt_prim (_, subterms) ->
        get_paths_of_focuses_list subterms position 0 acc
    | Patt_focus _ -> position :: acc

  and get_paths_of_focuses_list :
      (prim, focused) pattern_list ->
      Path.t ->
      int ->
      Path.t list ->
      Path.t list =
   fun patt_list position index acc ->
    match patt_list with
    | Patt_list_cons (prim, tail, wit) -> (
        match wit with
        | FU ->
            let prim_position = Path.at_index index position in
            get_paths_of_focuses prim prim_position acc
        | UF -> get_paths_of_focuses_list tail position (index + 1) acc
        | FF ->
            let prim_position = Path.at_index index position in
            let acc = get_paths_of_focuses prim prim_position acc in
            get_paths_of_focuses_list tail position (index + 1) acc)

  let rec pattern_matches_aux : type f. (prim, f) pattern -> term -> bool =
   fun patt node ->
    match (patt.patt_desc, node.Hashcons.node) with
    | (Patt_focus patt, _) -> pattern_matches_aux patt node
    | (Patt_any, _) -> true
    | (Patt_var i, Var j) -> i = j
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

  let rec all_matches_aux :
      matching -> term -> Path.t -> (t * Path.t) list -> (t * Path.t) list =
   fun matching node position acc ->
    let subterms =
      match node.Hashcons.node with
      | Prim (_, subterms, _) -> subterms
      | Var _ -> [||]
    in
    let (_, acc) =
      Array.fold_left
        (fun (index, acc) subterm ->
          let position = Path.at_index index position in
          (index + 1, all_matches_aux matching subterm position acc))
        (0, acc)
        subterms
    in
    match List.find_opt (fun patt -> pattern_matches patt node) matching with
    | None -> acc
    | Some patt -> (patt, position) :: acc

  let refine_focused pattern path =
    match pattern with
    | Ex_patt patt -> (
        match get_focus patt with
        | Unfocused_tag -> []
        | Focused_tag -> get_paths_of_focuses patt path [])

  let all_matches matching node =
    all_matches_aux matching node Path.root []
    |> List.concat_map (fun ((Ex_patt patt as pattern), position) ->
           match get_focus patt with
           | Unfocused_tag -> [position]
           | Focused_tag -> refine_focused pattern position)

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

  let var id = ex_patt (Patt_var id)

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
    | Patt_var id -> Format.fprintf fmtr "[var %d]" id
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
  ->
  Intf.Pattern
    with type prim = P.t
     and type path = Path.t
     and type term = P.t Term.term =
  Make_raw

module Make_with_hash_consing
    (P : Intf.Signature)
    (T : Intf.Term with type prim = P.t and type t = P.t Term.term) : sig
  include
    Intf.Pattern
      with type prim = P.t
       and type path = Path.t
       and type term = P.t Term.term

  val all_matches_with_hash_consing : t -> term -> path list
end = struct
  include Make_raw (P) (T)

  type key = { patt_uid : int; node_tag : int }

  let table : (key, path list) Hashtbl.t = Hashtbl.create 7919

  let rec all_matches_aux : t -> term -> Path.t -> Path.t list -> Path.t list =
   fun patt node position acc ->
    let patt_uid = uid patt in
    let node_tag = node.tag in
    match Hashtbl.find_opt table { patt_uid; node_tag } with
    | None ->
        let subterms =
          match node.Hashcons.node with
          | Var _ -> [||]
          | Prim (_, subterms, _) -> subterms
        in
        let (_, acc) =
          Array.fold_left
            (fun (index, acc) subterm ->
              let position = Path.at_index index position in
              (index + 1, all_matches_aux patt subterm position acc))
            (0, acc)
            subterms
        in
        if pattern_matches patt node then position :: acc else acc
    | Some res -> List.rev_append res acc

  let all_matches_with_hash_consing pattern node =
    match pattern with
    | Ex_patt patt -> (
        match get_focus patt with
        | Unfocused_tag -> all_matches_aux pattern node Path.root []
        | Focused_tag ->
            let paths = all_matches_aux pattern node Path.root [] in
            List.fold_left
              (fun acc context_path ->
                get_paths_of_focuses patt context_path acc)
              []
              paths)
end
