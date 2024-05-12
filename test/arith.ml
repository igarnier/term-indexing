open Lib_rewriting

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

module Var : Subst.Indicator with type t = int = struct
  type t = int

  let compare = Int.compare

  let equal = Int.equal

  let hash = Hashtbl.hash

  let pp = Format.pp_print_int

  let indicator x = -(x + 1)

  let is_indicator x = x < 0
end

module Var_map : Intf.Map with type key = int = struct
  include Map.Make (Var)

  let empty () = empty
end

module Expr = Term.Make_hash_consed (Prim) (Var) (Var_map)
module Subst_mod = Subst.Make (Prim) (Expr)
module Index = Subst.Make_index (Prim) (Var) (Expr) (Subst_mod)
module Subst = Subst_mod

let add x y = Expr.prim Add [| x; y |]

let sub x y = Expr.prim Sub [| x; y |]

let mul x y = Expr.prim Mul [| x; y |]

let div x y = Expr.prim Div [| x; y |]

let neg x = Expr.prim Neg [| x |]

let float f = Expr.prim (Prim.Float f) [||]

let var s = Expr.var s

(* ---------------------------------------- *)

type native =
  | Add of native * native
  | Sub of native * native
  | Mul of native * native
  | Div of native * native
  | Neg of native
  | Var of int
  | Const of float

let rec pp_native fmtr (term : native) =
  match term with
  | Add (l, r) -> Format.fprintf fmtr "@[(%a + %a)@]" pp_native l pp_native r
  | Sub (l, r) -> Format.fprintf fmtr "@[(%a - %a)@]" pp_native l pp_native r
  | Mul (l, r) -> Format.fprintf fmtr "@[(%a * %a)@]" pp_native l pp_native r
  | Div (l, r) -> Format.fprintf fmtr "@[(%a / %a)@]" pp_native l pp_native r
  | Neg e -> Format.fprintf fmtr "@[-%a@]" pp_native e
  | Var v -> Format.fprintf fmtr "@[%d@]" v
  | Const f -> Format.fprintf fmtr "@[%.3f@]" f

(* -------------------- *)

let rec to_native : Expr.t -> native =
 fun { Hashcons.node = desc; _ } ->
  match desc with
  | Prim (Prim.Add, [| lhs; rhs |]) -> Add (to_native lhs, to_native rhs)
  | Prim (Prim.Sub, [| lhs; rhs |]) -> Sub (to_native lhs, to_native rhs)
  | Prim (Prim.Mul, [| lhs; rhs |]) -> Mul (to_native lhs, to_native rhs)
  | Prim (Prim.Div, [| lhs; rhs |]) -> Div (to_native lhs, to_native rhs)
  | Prim (Prim.Neg, [| e |]) -> Neg (to_native e)
  | Prim (Float f, [||]) -> Const f
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

let term_gen canonical_var : Expr.t Gen.t =
  let float_ = Gen.map float (Gen.float_range (-1000.) 1000.) in
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
                else small_nat >>= fun i -> return (var i))
        | `Float -> float_)
    (Path.root, 5)

(* A naive generator *)
let gen = term_gen (fun path -> Some (Path.hash path))

let memoize_enum : int -> Path.t -> int option =
 fun n ->
  let table = Hashtbl.create 10 in
  let c = ref 0 in
  fun path ->
    if !c >= n then None
    else
      match Hashtbl.find_opt table path with
      | None ->
          let next = !c in
          incr c ;
          let indicator = -next - 1 in
          Hashtbl.add table path indicator ;
          Some indicator
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
    let indicator = -i - 1 in
    pair (return indicator) (term_gen (memoize_enum i))
  in
  Gen.bind domain_gen @@ fun list ->
  Gen.map Subst.of_list (flatten_l (List.map term_gen list))

let conv qctests = List.map QCheck_alcotest.to_alcotest qctests
