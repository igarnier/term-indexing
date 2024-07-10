module type PersistentArray = sig
  type 'a t

  val empty : 'a t

  val get : 'a t -> int -> 'a option

  val set : 'a t -> int -> 'a -> 'a t

  val push : 'a t -> 'a -> 'a t

  val pp : 'a Fmt.t -> 'a t Fmt.t
end

module Make (A : PersistentArray) : sig
  type t

  type elt = int

  val empty : unit -> t

  val find : t -> elt -> elt

  val union : t -> elt -> elt -> elt * t

  val pp : t Fmt.t
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
      if rx > ry then (cx, { h with parent = A.set h.parent cy cx })
      else if rx < ry then (cy, { h with parent = A.set h.parent cx cy })
      else
        (cx, { rank = A.set h.rank cx (rx + 1); parent = A.set h.parent cy cx })
    else (cx, h)

  let pp fmtr uf = A.pp Fmt.int fmtr uf.parent
end

module Map_based = Make (struct
  type 'a t = 'a Int_map.t

  let empty = Int_map.empty

  let get a i = Int_map.find_opt i a

  let set a i v = Int_map.add i v a

  let push a v = Int_map.add (Int_map.cardinal a) v a

  let pp pp_v ppf a =
    let pp_elt ppf (i, v) = Fmt.pf ppf "%d: %a" i pp_v v in
    Fmt.pf ppf "{@[<hov>%a@]}" (Fmt.iter_bindings Int_map.iter pp_elt) a
end)
