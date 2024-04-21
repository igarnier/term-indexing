open Lib_rewriting
open Monolith
open Containers

(* Reference implementation *)
module R = struct
  let make = Vector.make

  let init = Vector.init

  let length = Vector.length

  let get = Vector.get

  let set vec index elt =
    let v = Vector.copy vec in
    Vector.set v index elt ;
    v

  let push vec elt =
    let v = Vector.copy vec in
    Vector.push v elt ;
    v

  let pop vec =
    let v = Vector.copy vec in
    let res = Vector.pop v in
    (res, v)

  let to_list = Vector.to_list

  let iter = Vector.iter

  let iteri = Vector.iteri

  let fold_left = Vector.fold
end
[@@ocaml.warning "-32"]

(* Concrete implementation *)
module C = Pvec

(* -------------------------------------------------------------------------- *)

(* Define [element] as an alias for the concrete type [int]. Equip it with a
   deterministic generator of fresh elements. There is no point in letting
   afl-fuzz choose elements in a nondeterministic way; that would be a waste
   of random bits. *)

let element = sequential ()

let index = int

(* -------------------------------------------------------------------------- *)

(* Declare an abstract type [array] of persistent arrays. *)

let array = declare_abstract_type ()

(* -------------------------------------------------------------------------- *)

(* Define wrappers that allow testing the higher-order functions. *)

(* Because we use [constant] rather than [define], the definition of the
   wrapper won't be printed by Monolith as part of an error scenario.
   This could easily be fixed, but I don't want to make the code longer. *)

(* [wrap_iter] converts [iter] into [to_list]. *)

let wrap_iter iter a =
  let xs = ref [] in
  iter (fun x -> xs := x :: !xs) a ;
  List.rev !xs

let wrap_iter = map_into wrap_iter (wrap_iter, constant "wrap_iter")

(* [wrap_iteri] is analogous, but produces a list of index-element pairs. *)

let wrap_iteri_f iteri a =
  let ixs = ref [] in
  iteri (fun i x -> ixs := (i, x) :: !ixs) a ;
  List.rev !ixs

let wrap_iteri = map_into wrap_iteri_f (wrap_iteri_f, constant "wrap_iteri")

(* [wrap_fold_left] converts [fold_left] into [rev . to_list]. *)

let wrap_fold_left fold_left a = fold_left (fun xs x -> x :: xs) [] a

let wrap_fold_left =
  map_into wrap_fold_left (wrap_fold_left, constant "wrap_fold_left")

let wrap_init init n =
  let is = ref [] in
  let f i =
    is := i :: !is ;
    i
  in
  let a = init n f in
  (List.rev !is, a)

let wrap_init = map_into wrap_init (wrap_init, constant "wrap_init")

(* -------------------------------------------------------------------------- *)

(* Declare the operations. *)

let () =
  let spec = lt 16 ^> element ^> array in
  declare "make" spec R.make C.make ;

  let spec = wrap_init (lt 16 ^> (list index *** array)) in
  declare "init" spec R.init C.init ;

  let spec = array ^> int in
  declare "length" spec R.length C.length ;

  let spec = array ^>> fun a -> lt (R.length a) ^> element in
  declare "get" spec R.get C.get ;

  let spec = array ^>> fun a -> lt (R.length a) ^> element ^> array in
  declare "set" spec R.set C.set ;

  (* let spec = array ^> element ^> array in *)
  (* declare "push" spec R.push C.push ; *)

  (* let spec = array ^> ((option element *** array)) in *)
  (* declare "pop" spec R.pop C.pop ; *)
  let spec = array ^> list element in
  declare "to_list" spec R.to_list C.to_list ;

  let spec = wrap_iter (array ^> list element) in
  declare "iter" spec R.iter C.iter ;

  let spec = wrap_iteri (array ^> list (index *** element)) in
  declare "iteri" spec R.iteri C.iteri ;

  let spec = wrap_fold_left (array ^> list element) in
  declare "fold_left" spec R.fold_left C.fold ;

  ()

(* -------------------------------------------------------------------------- *)

(* Start the engine! *)

let () =
  let fuel = 5 in
  main fuel
