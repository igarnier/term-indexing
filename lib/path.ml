(* Paths in terms. Note that paths are in reverse form, going from a node to the root. *)

type t = Root | At_index of int * t

(* OPTIM: benchmark using an int array (or dynarray to avoid two traversals?) *)
(* Forward paths, going from a root to a node. *)
type forward = int list

let root = Root

let at_index i path = At_index (i, path)

let rec concat ~above:path1 ~under:path2 =
  match path2 with
  | Root -> path1
  | At_index (i, p) -> at_index i (concat ~above:path1 ~under:p)

let rec compare path1 path2 =
  match (path1, path2) with
  | (Root, Root) -> 0
  | (Root, _) -> -1
  | (_, Root) -> 1
  | (At_index (i1, p1), At_index (i2, p2)) ->
      let c = Int.compare i1 i2 in
      if c = 0 then compare p1 p2 else c

let equal path1 path2 = compare path1 path2 = 0

let reverse path =
  let rec reverse : t -> forward -> forward =
   fun path acc ->
    match path with Root -> acc | At_index (i, path) -> reverse path (i :: acc)
  in
  reverse path []

let hash path = Hashtbl.hash path

let rec pp fmtr (path : t) =
  match path with
  | Root -> Format.fprintf fmtr "*"
  | At_index (i, up) -> Format.fprintf fmtr "%d -> %a" i pp up

let to_string (path : t) = Format.asprintf "%a" pp path
