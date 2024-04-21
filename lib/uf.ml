module type PersistentArray = sig
  type 'a t

  val make : int -> 'a -> 'a t

  val get : 'a t -> int -> 'a

  val set : 'a t -> int -> 'a -> 'a t

  val push : 'a t -> 'a -> 'a t
end

module Make (A : PersistentArray) : sig
  type t

  type elt = int

  val empty : unit -> t

  val fresh : t -> elt * t

  val find : t -> elt -> elt

  val union : t -> elt -> elt -> t
end = struct
  type t = { next : int; rank : int A.t; mutable parent : int A.t }

  type elt = int

  let empty () = { next = 0; rank = A.make 0 0; parent = A.make 0 0 }

  let fresh (h : t) =
    let next = h.next in
    let rank = A.push h.rank 0 in
    let parent = A.push h.parent next in
    (next, { next = next + 1; rank; parent })

  let rec find_aux f i =
    let fi = A.get f i in
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
      let rx = A.get h.rank cx in
      let ry = A.get h.rank cy in
      if rx > ry then { h with parent = A.set h.parent cy cx }
      else if rx < ry then { h with parent = A.set h.parent cx cy }
      else
        { next = h.next;
          rank = A.set h.rank cx (rx + 1);
          parent = A.set h.parent cy cx
        }
    else h
end

module Array_based = Make (Pvec)

module Map_based = Make (struct
  type 'a t = 'a Int_map.t

  let init n f = Seq.init n (fun i -> (i, f i)) |> Int_map.of_seq

  let make n v = init n (fun _ -> v)

  let get a i = Int_map.find i a

  let set a i v = Int_map.add i v a

  let push a v = Int_map.add (Int_map.cardinal a) v a
end)
