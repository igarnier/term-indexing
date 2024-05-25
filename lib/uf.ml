module type PersistentArray = sig
  type 'a t

  val empty : 'a t

  val get : 'a t -> int -> 'a option

  val set : 'a t -> int -> 'a -> 'a t

  val push : 'a t -> 'a -> 'a t
end

module Make (A : PersistentArray) : sig
  type t

  type elt = int

  val empty : unit -> t

  val find : t -> elt -> elt

  val union : t -> elt -> elt -> t
end = struct
  type t = { rank : int A.t; mutable parent : int A.t }

  type elt = int

  let empty () = { rank = A.empty; parent = A.empty }

  let rec find_aux f i =
    let fi = A.get f i |> Option.value ~default:i in
    if fi == i then (f, i)
    else
      let (f, r) = find_aux f fi in
      let f = A.set f i r in
      (f, r)

  let find (h : t) (x : int) =
    let (f, cx) = find_aux h.parent x in
    h.parent <- f ;
    cx

  let union (h : t) (x : elt) (y : elt) =
    let cx = find h x in
    let cy = find h y in
    if cx != cy then
      let rx = A.get h.rank cx |> Option.value ~default:0 in
      let ry = A.get h.rank cy |> Option.value ~default:0 in
      if rx > ry then { h with parent = A.set h.parent cy cx }
      else if rx < ry then { h with parent = A.set h.parent cx cy }
      else { rank = A.set h.rank cx (rx + 1); parent = A.set h.parent cy cx }
    else h
end

module Map_based = Make (struct
  type 'a t = 'a Int_map.t

  let empty = Int_map.empty

  let get a i = Int_map.find_opt i a

  let set a i v = Int_map.add i v a

  let push a v = Int_map.add (Int_map.cardinal a) v a
end)
