(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* Persistent arrays implemented using Baker's trick.

   A persistent array is a usual array (node Array) or a change into
   another persistent array (node Diff). Invariant: any persistent array is a
   (possibly empty) linked list of Diff nodes ending on an Array node.

   As soon as we try to access a Diff, we reverse the linked list to move
   the Array node to the position we are accessing; this is achieved with
   the reroot function.
*)

(* Modified to use extensible arrays*)

(* TODO optim: we don't need full persistence, semi-persistence is enough *)

module Vec = Containers.Vector

type 'a arr = 'a Vec.vector

type 'a t = 'a data ref

and 'a data =
  | Array of 'a arr
  | Diff of int * 'a * 'a t
  | Pop of 'a t
  | Push of 'a option * 'a t

let make n v = ref (Array (Vec.make n v))

let init n f = ref (Array (Vec.init n f))

(* `reroot t` ensures that `t` becomes an `Array` node.
    This is written in CPS to avoid any stack overflow. *)
let rec rerootk t k =
  match !t with
  | Array _ -> k ()
  | Pop t' ->
      rerootk t' (fun () ->
          (match !t' with
          | Array a as n ->
              let popped = Vec.pop a in
              t := n ;
              t' := Push (popped, t)
          | Diff _ | Pop _ | Push _ -> assert false) ;
          k ())
  | Push (opt_v, t') ->
      rerootk t' (fun () ->
          (match !t' with
          | Array a as n ->
              Option.iter (fun v -> Vec.push a v) opt_v ;
              t := n ;
              t' := Pop t
          | Diff _ | Pop _ | Push _ -> assert false) ;
          k ())
  | Diff (i, v, t') ->
      rerootk t' (fun () ->
          (match !t' with
          | Array a as n ->
              let v' = Vec.get a i in
              Vec.set a i v ;
              t := n ;
              t' := Diff (i, v', t)
          | Diff _ | Pop _ | Push _ -> assert false) ;
          k ())

let reroot t = rerootk t (fun () -> ())

let get t i =
  match !t with
  | Array a -> Vec.get a i
  | Diff _ | Pop _ | Push _ -> (
      reroot t ;
      match !t with
      | Array a -> Vec.get a i
      | Diff _ | Pop _ | Push _ -> assert false)

let set t i v =
  reroot t ;
  match !t with
  | Array a as n ->
      let old = Vec.get a i in
      if old == v then t
      else (
        Vec.set a i v ;
        let res = ref n in
        t := Diff (i, old, res) ;
        res)
  | Diff _ | Pop _ | Push _ -> assert false

let pop t : 'a option * 'a t =
  reroot t ;
  match !t with
  | Array a as n ->
      let popped = Vec.pop a in
      let res = ref n in
      t := Push (popped, res) ;
      (popped, res)
  | Diff _ | Pop _ | Push _ -> assert false

let push t v : 'a t =
  reroot t ;
  match !t with
  | Array a as n ->
      Vec.push a v ;
      let res = ref n in
      t := Pop res ;
      res
  | Diff _ | Pop _ | Push _ -> assert false

(* CAVEAT: Do not use `with_array` with a function `f` that may reroot
   the persitent array `t` (for instance by accessing, even with `get`
   only, to other versions of `t`). *)
let with_array t f =
  reroot t ;
  match !t with Array a -> f a | Diff _ | Pop _ | Push _ -> assert false

let length t = with_array t Vec.length

let to_list t = with_array t Vec.to_list

let iter f t = with_array t (Vec.iter f)

let iteri f t = with_array t (Vec.iteri f)

let fold f acc t = with_array t (Vec.fold f acc)
