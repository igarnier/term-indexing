(** Hashable, totally ordered, printable types *)
module type Hashed = sig
  type t

  (** [compare] is a total order. *)
  val compare : t -> t -> int

  (** [equal s1 s2] tests whether [s1] and [s2] are equal. *)
  val equal : t -> t -> bool

  (** [hash s] is a hash of [s]. *)
  val hash : t -> int

  (** [pp fmt s] prints a representation of [s] to the formatter [fmt]. *)
  val pp : Format.formatter -> t -> unit
end

(** The type of signatures of first-order terms. *)
module type Signature = sig
  include Hashed

  (** [arity s] is the arity of [s], i.e. a term with head [s] must have exactly [arity s] sub-terms. *)
  val arity : t -> int
end

(** The module type of finite maps. *)
module type Map = sig
  (** The type of keys. *)
  type key

  (** The type of maps polymorphic in their values. *)
  type 'a t

  (** [empty ()] is the empty map. *)
  val empty : unit -> 'a t

  (** [is_empty m] is true if and only if [m] is empty. *)
  val is_empty : 'a t -> bool

  (** [find_opt k m] is [Some v] if [k] is bound to [v] in [m], and [None] otherwise. *)
  val find_opt : key -> 'a t -> 'a option

  (** [add k v m] is the map that binds [k] to [v] in [m]. If [k] is already bound, the previous binding is shadowed. *)
  val add : key -> 'a -> 'a t -> 'a t

  (** [equal eq m1 m2] is true if and only if [m1] and [m2] are equal according to [eq]. *)
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  (** [union m1 m2] is the union of [m1] and [m2].

      @raise Invalid_argument if [m1] and [m2] have overlapping domains.
  *)
  val union : 'a t -> 'a t -> 'a t

  (** [to_seq m] produces the {b persistent} sequence of elements of [m] in
      increasing key order. *)
  val to_seq : 'a t -> (key * 'a) Seq.t

  (** [of_seq_keys m] is the sequence of keys of [m] *)
  val to_seq_keys : 'a t -> key Seq.t

  (** [of_seq s] constructs a map from the elements of [s]. *)
  val of_seq : (key * 'a) Seq.t -> 'a t
end

(** The module type of patterns. *)
module type Pattern = sig
  (** The type of primitives, i.e. the symbols. Each value of type [prim] has a definite arity. *)
  type prim

  (** The type of paths in terms. *)
  type path

  (** The type of patterns. *)
  type t

  (** The type of patterns on lists of terms. *)
  type plist

  (** The type of terms. *)
  type term

  (** [pattern_matches patt t] checks whether the pattern [patt] matches the term [t] *)
  val pattern_matches : t -> term -> bool

  (** [all_matches patt t] returns all paths at which there is a subterm matching [patt] *)
  val all_matches : t -> term -> path list

  (** [focus_matches patt paths] returns the elements of [paths] that correspond to focused subterms of [patt]. *)
  val focus_matches : t -> path list -> path list

  (** [prim p plist] is a pattern matching a term with head bearing a primitive [p] and subterms matching the list pattern [plist]. *)
  val prim : prim -> plist -> t

  (** [prim_pred pred plist] is a pattern matching a term with primitive [p] such that [pred p] is [true], and subterms
      matching the list pattern [plist]. *)
  val prim_pred : (prim -> bool) -> plist -> t

  (** [var i] is a pattern matching a variable [i]. *)
  val var : int -> t

  (** [any] is a pattern matching any term. *)
  val any : t

  (** [focus patt] returns a pattern equivalent to [patt] except that a focus mark is added
      on all terms matched by [patt].

      @raise Invalid_pattern if [t] is already a focus. *)
  val focus : t -> t

  (** [list_any] is a list pattern matching any list of terms. *)
  val list_any : plist

  (** [list_empty] is a list pattern matching the empty list of terms. *)
  val list_empty : plist

  (** [list_cons hd tl] is a list pattern matching a list with head matching the pattern [hd] and tail
      matching the list pattern [tl]. *)
  val list_cons : t -> plist -> plist

  (** An alias for {!list_cons} *)
  val ( @. ) : t -> plist -> plist

  (** Pattern pretty-printing *)
  val pp : Format.formatter -> t -> unit

  (** [uid p] returns a unique integer attached to [p]. It is guaranteed that if two patterns
      have the same [uid], they are equal. *)
  val uid : t -> int
end

(** The module type of first-order terms *)
module type Term = sig
  (** The type of primitives, i.e. the symbols. Each value of type [prim] has a definite arity. *)
  type prim

  (** The type of terms *)
  type t

  type var := int

  (** The type of polymorphic maps indexed by variables *)
  type 'a var_map

  (** [equal t1 t2] is an O(1) equality function on terms *)
  val equal : t -> t -> bool

  (** [equal t1 t2] is an O(1) total order on terms. This is not a structural order *)
  val compare : t -> t -> int

  (** [hash t] is an O(1) hash function on terms *)
  val hash : t -> int

  (** [prim p ts] constructs a term with head equal to [p] and subterms equal to [ts]

      @raise Invalid_argument if the length of [ts] does not match the arity of [p]. *)
  val prim : prim -> t array -> t

  (** [var v] construcst a variable [v] *)
  val var : var -> t

  (** [ub t] is an upper bound on the absolute value of variables contained in [t].
      Equal to {!Int_option.none} if [t] does not contain variables. *)
  val ub : t -> Int_option.t

  (** [is_var t] is equal to [var v] if [equal t (var v)] or [None] if it is not the case *)
  val is_var : t -> var option

  (** [destruct t ifprim ifvar] performs case analysis on the term [t] *)
  val destruct : t -> (prim -> t array -> 'a) -> (var -> 'a) -> 'a

  (** [fold f acc term] folds [f] over the subterms of [t] *)
  val fold : (t -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  (** [fold_variables f acc t] folds [f] over the variables of [t] *)
  val fold_variables : (var -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  (** [map_variables f t] replaces all variables [var i] present in [t] by [f i]. *)
  val map_variables : (int -> t) -> t -> t

  (** [get_subterm_fwd t fpth] is the subterm of [t] at position defined by the forward path
      [fpth].

      @raise Get_subterm_oob if the path is out of bounds.
  *)
  val get_subterm_fwd : t -> Path.forward -> t

  (** [get_subterm t pth] is the subterm of [t] at position defined by the path [pth].

      @raise Get_subterm_oob if the path is out of bounds. *)
  val get_subterm : t -> Path.t -> t

  (** [subst ~term ~path f] replaces the subterm of [term] at position [path]
      by [f (get_subterm term path)]. *)
  val subst : term:t -> path:Path.t -> (t -> t) -> t

  (** [canon t gen] canonicalizes the term [t] using the variable generator [gen].
      Returns the canonicalized term as well as a map from old to canonicalized variables. *)
  val canon : t -> (unit -> var) -> var var_map * t

  (** Pretty-printing of terms. *)
  val pp : Format.formatter -> t -> unit
end

(** The module type of substitutions *)
module type Subst = sig
  (** The type of terms *)
  type term

  type 'a var_map

  type var := int

  (** The type of substitutions *)
  type t

  val of_seq : (var * term) Seq.t -> t

  val to_seq : t -> (var * term) Seq.t

  val to_seq_keys : t -> var Seq.t

  val pp : Format.formatter -> t -> unit

  (** [empty ()] is the empty substitution.  *)
  val empty : unit -> t

  (** [is_empty subst] checks whether [equal subst empty] *)
  val is_empty : t -> bool

  val equal : t -> t -> bool

  (** [ub subst] is an upper bound on the absolute value of variables appearing in [subst]
      (either in the domain or the range of the substitution). *)
  val ub : t -> Int_option.t

  (** [underlying_map subst] returns the underlying map of the substitution. *)
  val underlying_map : t -> term var_map

  (** [eval v subst] returns [Some t] if [v] is mapped to the term [t] in [subst]
      or [None] if [v] is not in the domain of [subst]. *)
  val eval : var -> t -> term option

  (** Exception-raising variant of {!eval}.
      @raise Not_found if [v] is not in the domain of [subst]. *)
  val eval_exn : var -> t -> term

  (** [add v t subst] adds a mapping from [v] to [t] in [subst].
      If [v] is already in the domain of [subst], the previous mapping is replaced.

      @raise Invalid_argument if [t] is a variable equal to [v] *)
  val add : var -> term -> t -> t

  (** [unsafe_add] does as {!add} but doen't check for validity of the mapping. *)
  val unsafe_add : var -> term -> t -> t

  (** [lift subst term] applies the substitution [subst] to [term].
      Note that [lift] does not perform an occur check: do not use with
      substitutions that are not well-founded. *)
  val lift : t -> term -> term

  (** [union s1 s2] computes the union of [s1] and [s2].

      @raise Invalid_argument if [s1] and [s2] have overlapping domains. *)
  val union : t -> t -> t

  (** [Unification] contains facilities to perform first-order term unification *)
  module Unification : sig
    (** [state] is the type of unification state. *)
    type state

    (** [Cannot_unify] is raised by {!unify} when a unifier cannot be found. *)
    exception Cannot_unify

    (** [empty ()] is an empty unification state. *)
    val empty : unit -> state

    (** [unify t1 t2 state] unifies terms [t1] and [t2] in state [state] and returns
        an updated {!state}.

        @raise Cannot_unify if no solution was found. *)
    val unify : term -> term -> state -> state

    (** [unify_subst s state] unifies [s] with substitution state [state]
        and returns an updated {!state}. *)
    val unify_subst : t -> state -> state

    (** [generalize t1 t2] checks that there exists a substitution [subst]
        such that [lift t1 subst = t2]. *)
    val generalize : term -> term -> bool

    (** [subst state] returns the substitution underlying the unification state. *)
    val subst : state -> t
  end
end

(** The module type of substitution trees *)
module type Term_index = sig
  (** The type of substitutions *)
  type subst

  (** The type of terms, which act as keys of substitution trees *)
  type term

  (** The type of substitution trees with values of type ['a] *)
  type 'a t

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

  val create : unit -> 'a t

  (** [update term f index] modifies the binding associated to [term] in [index].
      If a value [v] is already bound to [term] in [index], this value is replaced by [f (Some v)].
      In the other case, the value [f None] is bound to [term]. *)
  val update : term -> ('a option -> 'a) -> 'a t -> term

  (** [insert term data index] adds a mapping from a canonicalized version of [term] to [data] in [index],
      and returns the canonicalized term. If an existing binding to [term] already exists,
      it is overwritten. *)
  val insert : term -> 'a -> 'a t -> term

  (** [iter f index] iterates [f] on the bindings of [index]. *)
  val iter : (term -> 'a -> unit) -> 'a t -> unit

  (** [iter_unifiable f index query] iterates [f] on all bindings contained in [index]
      whose keys are unifiable with [query]. *)
  val iter_unifiable : (term -> 'a -> unit) -> 'a t -> term -> unit

  (** [iter_generalize f index query] iterates [f] on all bindings contained in [index]
      whose keys generalize [query]. *)
  val iter_generalize : (term -> 'a -> unit) -> 'a t -> term -> unit

  (** [iter_specialize f index query] iterates [f] on all bindings contained in [index]
      whose keys specialize [query]. *)
  val iter_specialize : (term -> 'a -> unit) -> 'a t -> term -> unit
end
