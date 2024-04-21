open Lib_rewriting
open Monolith

module R = struct
  include Uf.Map_based

  let find uf x = try Some (find uf x) with Not_found -> None

  let union uf x y =
    try
      let uf = union uf x y in
      Some uf
    with _ -> None
end

module C = struct
  include Uf.Array_based

  let find uf x = try Some (find uf x) with _ -> None

  let union uf x y =
    try
      let uf = union uf x y in
      Some uf
    with _ -> None
end

(* -------------------------------------------------------------------------- *)

let element = declare_abstract_type ()

(* -------------------------------------------------------------------------- *)

(* Declare an abstract type [array] of persistent union-finds. *)

let uf = declare_abstract_type ()

(* -------------------------------------------------------------------------- *)

(* Declare the operations. *)

let () =
  let spec = unit ^> uf in
  declare "empty" spec R.empty C.empty ;

  let spec = uf ^> (element *** uf) in
  declare "fresh" spec R.fresh C.fresh ;

  let spec = uf ^> element ^> option element in
  declare "find" spec R.find C.find ;

  let spec = uf ^> element ^> element ^> option uf in
  declare "union" spec R.union C.union ;

  ()

(* -------------------------------------------------------------------------- *)

(* Start the engine! *)

let () =
  let fuel = 5 in
  main fuel
