open Term_indexing

module Prim = struct
  type t = Add | Sub | Mul | Div | Neg | Float of float

  let compare (x : t) (y : t) = Stdlib.compare x y

  let equal (x : t) (y : t) = x = y

  let hash = Hashtbl.hash

  let pp fmtr = function
    | Add -> Format.fprintf fmtr "Add"
    | Sub -> Format.fprintf fmtr "Sub"
    | Mul -> Format.fprintf fmtr "Mul"
    | Div -> Format.fprintf fmtr "Div"
    | Neg -> Format.fprintf fmtr "Neg"
    | Float f -> Format.fprintf fmtr "%f" f

  let arity = function Add | Sub | Mul | Div -> 2 | Neg -> 1 | Float _ -> 0
end

module Var_map : Intf.Map with type key = int = struct
  include Map.Make (Int)

  let empty () = empty

  let to_seq_keys map = to_seq map |> Seq.map fst

  let union m1 m2 =
    union
      (fun _ _ _ -> invalid_arg "Var_map.union: maps have overlapping domains")
      m1
      m2
end

module Expr = Term.Make_hash_consed (Prim) (Var_map)
module Subst_mod = Subst.Make (Prim) (Var_map) (Expr)

(* ---------------------------------------- *)

(* Unifying signature for all term index implementations *)
module type Index_signature = sig
  type 'a t

  type term = Expr.t

  val create : unit -> 'a t

  val insert : term -> 'a -> 'a t -> unit

  val iter : (term -> 'a -> unit) -> 'a t -> unit

  val iter_unifiable : (term -> 'a -> unit) -> 'a t -> term -> unit

  val iter_generalize : (term -> 'a -> unit) -> 'a t -> term -> unit

  val iter_specialize : (term -> 'a -> unit) -> 'a t -> term -> unit

  val pp : 'a Fmt.t -> 'a t Fmt.t

  module Internal_for_tests : sig
    val check_invariants : 'a t -> bool
  end
end

module Index_raw = Slow_index.Make (Prim) (Var_map) (Expr) (Subst_mod)

module Index : Index_signature = struct
  include Index_raw

  let insert f data index = ignore (insert f data index)

  let iter_unifiable f index query = iter_unifiable f index query

  let iter_generalize f index query = iter_generalize f index query

  let iter_specialize f index query = iter_specialize f index query
end

module Index2_raw = Term_index.Make (Prim) (Expr) (Subst_mod)

module Index2 = struct
  include Index2_raw

  type term = Expr.t

  let iter f index = iter (fun iterm data -> f (to_term iterm) data) index

  let iter_unifiable f index query =
    iter_unifiable (fun iterm data -> f (to_term iterm) data) index query

  let iter_generalize f index query =
    iter_generalize (fun iterm data -> f (to_term iterm) data) index query

  let iter_specialize f index query =
    iter_specialize (fun iterm data -> f (to_term iterm) data) index query

  let insert f data index = ignore (insert f data index)
end

module Reference = Naive_index.Make (Prim) (Expr) (Subst_mod)
module Subst = Subst_mod

let add x y = Expr.prim Add [| x; y |]

let sub x y = Expr.prim Sub [| x; y |]

let mul x y = Expr.prim Mul [| x; y |]

let div x y = Expr.prim Div [| x; y |]

let neg x = Expr.prim Neg [| x |]

let float f = Expr.prim (Prim.Float f) [||]

let var s = Expr.var s

let mkgen () =
  let c = ref 0 in
  fun () ->
    let v = !c in
    c := !c + 1 ;
    v

let canon t = Expr.canon t (mkgen ()) |> snd

let alpha_eq t1 t2 =
  let t1 = canon t1 in
  let t2 = canon t2 in
  Expr.equal t1 t2

let alpha_eq_list l1 l2 =
  let l1 = List.map canon l1 |> List.sort Expr.compare in
  let l2 = List.map canon l2 |> List.sort Expr.compare in
  List.equal Expr.equal l1 l2

(* ---------------------------------------- *)

type native =
  | Add of native * native
  | Sub of native * native
  | Mul of native * native
  | Div of native * native
  | Neg of native
  | Var of int
  | Const of float
  | Cycle of int

let rec pp_native fmtr (term : native) =
  match term with
  | Add (l, r) -> Format.fprintf fmtr "@[(%a + %a)@]" pp_native l pp_native r
  | Sub (l, r) -> Format.fprintf fmtr "@[(%a - %a)@]" pp_native l pp_native r
  | Mul (l, r) -> Format.fprintf fmtr "@[(%a * %a)@]" pp_native l pp_native r
  | Div (l, r) -> Format.fprintf fmtr "@[(%a / %a)@]" pp_native l pp_native r
  | Neg e -> Format.fprintf fmtr "@[-%a@]" pp_native e
  | Var v -> Format.fprintf fmtr "@[v(%d)@]" v
  | Const f -> Format.fprintf fmtr "@[%f@]" f
  | Cycle i -> Format.fprintf fmtr "@[cy(%d)@]" i

(* -------------------- *)

let rec to_native : Expr.t -> native =
 fun { Hashcons.node = desc; _ } ->
  match desc with
  | Prim (Prim.Add, [| lhs; rhs |], _) -> Add (to_native lhs, to_native rhs)
  | Prim (Prim.Sub, [| lhs; rhs |], _) -> Sub (to_native lhs, to_native rhs)
  | Prim (Prim.Mul, [| lhs; rhs |], _) -> Mul (to_native lhs, to_native rhs)
  | Prim (Prim.Div, [| lhs; rhs |], _) -> Div (to_native lhs, to_native rhs)
  | Prim (Prim.Neg, [| e |], _) -> Neg (to_native e)
  | Prim (Float f, [||], _) -> Const f
  | Var v -> Var v
  | _ -> assert false

(* ---------------------------------------- *)

module Gen = QCheck2.Gen

let symbol =
  Gen.frequencya
    [| (20, `Float);
       (20, `Var);
       (10, `Neg);
       (10, `Add);
       (10, `Sub);
       (10, `Mul);
       (10, `Div)
    |]

(* This term generator is subtle around variables:
   - indicator variables generated at a given path are deterministic,
     this ensures that during mscg computation one cannot have the
     case of two distinct indicator variable (which cannot happen in practice)
   - indicator variables are disjoint from non-indicator variables, the latter
     are not deterministic
*)
let term_gen canonical_var : Expr.t Gen.t =
  let float_ =
    Gen.small_int |> Gen.map (fun i -> float (float_of_int i +. 0.5))
  in
  let try_var path =
    match canonical_var path with
    | None -> float_
    | Some i -> Gen.return (var i)
  in
  let l = Path.at_index 0 in
  let r = Path.at_index 1 in
  let open Gen in
  fix
    (fun self (path, n) ->
      if n = 0 then oneof [try_var path; float_]
      else
        symbol >>= function
        | `Add -> map2 add (self (l path, n - 1)) (self (r path, n - 1))
        | `Sub -> map2 sub (self (l path, n - 1)) (self (r path, n - 1))
        | `Mul -> map2 mul (self (l path, n - 1)) (self (r path, n - 1))
        | `Div -> map2 div (self (l path, n - 1)) (self (r path, n - 1))
        | `Neg -> map neg (self (l path, n - 1))
        | `Var ->
            bind bool (fun indicator ->
                if indicator then
                  (* We forbid toplevel indicator variables *)
                  if Path.equal path Path.root then float_ else try_var path
                else
                  small_nat >>= fun i ->
                  return (var (Index_raw.Internal_for_tests.index i)))
        | `Float -> float_)
    (Path.root, 5)

(* A naive generator *)
let gen =
  term_gen (fun path ->
      let hash = Path.hash path in
      Some (Index_raw.Internal_for_tests.indicator (hash mod 100)))

let memoize_enum : int -> Path.t -> int option =
 fun upper_bound ->
  let table = Hashtbl.create 10 in
  let c = ref 0 in
  fun path ->
    if !c >= upper_bound then None
    else
      match Hashtbl.find_opt table path with
      | None ->
          let next = !c in
          incr c ;
          let indic = Index_raw.Internal_for_tests.indicator next in
          Hashtbl.add table path indic ;
          assert (indic < Index_raw.Internal_for_tests.indicator upper_bound) ;
          Some indic
      | Some _ as res -> res

let subst_gen : Subst.t Gen.t =
  (* A random linear, acyclic substitution can be viewed as a list [(v_i, t_i)]
     such that:
     - each variable can appear at most once in the domain
     - if there is a binding [(v_k, t_k)] then [v_k] may only appear in [t_j]
       for [j > k].
     These two conditions ensure acyclicity.
     E.g.
     for i = 0, t_i contains no variables
     for i = 1, t_i may contain v_0
     etc
  *)
  let open Gen in
  let var_count = small_nat in
  let make_domain count = List.init count Fun.id in
  let domain_gen = Gen.map make_domain var_count in
  let term_gen i =
    let indicator = Index_raw.Internal_for_tests.indicator i in
    pair (return indicator) (term_gen (memoize_enum i))
  in
  Gen.bind domain_gen @@ fun list ->
  Gen.map
    (fun l -> Subst.of_seq (List.to_seq l))
    (flatten_l (List.map term_gen list))

let conv qctests = List.map QCheck_alcotest.to_alcotest qctests
