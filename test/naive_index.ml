(* This is a naive implementation of a term index used as a reference implementation. *)
open Term_indexing

module Make
    (P : Intf.Signature)
    (T : Intf.Term with type prim = P.t)
    (S : Intf.Subst with type term = T.t) =
struct
  type term = T.t

  type subst = S.t

  module M = Map.Make (struct
    type t = term

    let compare = T.compare
  end)

  type 'a t = 'a M.t ref

  let name = "reference"

  let create () : 'a t = ref M.empty

  let insert term value index = index := M.add term value !index

  let iter f index = M.iter (fun t v -> f t v) !index

  let iter_pred f index pred = M.iter (fun t v -> if pred t then f t v) !index

  let iter_unifiable f index query =
    let open S.Unification in
    M.iter
      (fun t v ->
        match unify query t (empty ()) with None -> () | Some _ -> f t v)
      !index

  let iter_generalize f index query =
    let open S.Unification in
    M.iter (fun t v -> if generalize t query then f t v else ()) !index

  let iter_specialize f index query =
    let open S.Unification in
    M.iter (fun t v -> if generalize query t then f t v else ()) !index

  let pp pp_elt : 'a t Fmt.t =
   fun fmtr index ->
    Format.fprintf
      fmtr
      "%a"
      Fmt.Dump.(list (pair T.pp_sexp pp_elt))
      (M.bindings !index)

  module Internal_for_tests = struct
    let check_invariants _ = true

    let pp_error _fmtr _exn = ()
  end
end
