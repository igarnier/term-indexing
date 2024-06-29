module Intf = Intf
module Path = Path
module Pattern = Pattern
module Subst = Subst
module Term = Term
module Term_index = Term_index
module Slow_index = Slow_index

module Make (P : Intf.Signature) : sig
  module Term : Intf.Term with type prim = P.t

  module Path : module type of Path

  module Pattern :
    Intf.Pattern
      with type prim = P.t
       and type path = Path.t
       and type term = Term.t

  module Subst : Intf.Subst with type term = Term.t

  module Index :
    Term_index.S
      with type prim = P.t
       and type term = Term.t
       and type subst = Subst.t
end = struct
  module Default_map = Term.Default_map
  module Term = Term.Make_hash_consed (P) (Default_map)
  module Path = Path
  module Pattern = Pattern.Make (P) (Term)
  module Subst = Subst.Make (P) (Default_map) (Term)
  module Index = Term_index.Make (P) (Term) (Subst)
end
