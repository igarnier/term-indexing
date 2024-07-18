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

      Raises [Invalid_argument] if [m1] and [m2] have overlapping domains.
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

  (** The type of matchings. A matching is a disjunction of patterns. *)
  type matching = t list

  (** The type of patterns on lists of terms. *)
  type plist

  (** The type of terms. *)
  type term

  (** [pattern_matches patt t] checks whether the pattern [patt] matches the term [t] *)
  val pattern_matches : t -> term -> bool

  (** [all_matches t matching] returns all paths at which there is a subterm satisfying [matching] *)
  val all_matches : matching -> term -> path list

  (** [first_match t matching] returns the first paths, if any, where there is a subterm satisfying [matching].

      If the matched pattern does not specify focused subterms, the result is at most a singleton list.
      If the matched pattern specifies focused subterms, the result is a list of paths, one for each focused subterm.
 *)
  val first_match : matching -> term -> path list

  (** [refine_focused patt paths] returns the refinements of [path] that correspond to focused subterms of [patt].
      If [patt] is does not specify focii, the result is the empty list.
 *)
  val refine_focused : t -> path -> path list

  (** [prim p plist] is a pattern matching a term with head bearing a primitive [p] and subterms matching the list pattern [plist]. *)
  val prim : prim -> plist -> t

  (** [prim_pred pred plist] is a pattern matching a term with primitive [p] such that [pred p] is [true], and subterms
      matching the list pattern [plist]. *)
  val prim_pred : (prim -> bool) -> plist -> t

  (** [any_var] is a pattern matching any variable. *)
  val any_var : t

  (** [var i] is a pattern matching a variable [i]. *)
  val var : int -> t

  (** [any] is a pattern matching any term. *)
  val any : t

  (** [focus patt] returns a pattern equivalent to [patt] except that a focus mark is added
      on all terms matched by [patt].

      Raises [Invalid_pattern] if [t] is already a focus. *)
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

(** [Term_core] specifies the core types and operations related to first-order terms. *)
module type Term_core = sig
  (** The type of primitives, i.e. the symbols. Each value of type [prim] has a definite arity. *)
  type prim

  (** The type of terms *)
  type t

  type var := int

  (** Pretty-printing of terms. *)
  val pp : Format.formatter -> t -> unit

  (** Pretty-printing of terms in s-exp format. *)
  val pp_sexp : Format.formatter -> t -> unit

  (** [prim p ts] constructs a term with head equal to [p] and subterms equal to [ts]

      Raises [Invalid_argument] if the length of [ts] does not match the arity of [p]. *)
  val prim : prim -> t array -> t

  (** [var v] construcst a variable [v] *)
  val var : var -> t

  (** [destruct ifprim ifvar t] performs case analysis on the term [t] *)
  val destruct : (prim -> t array -> 'a) -> (var -> 'a) -> t -> 'a

  (** [destruct2 fpp fpv fvp fvv t1 t2] performs case analysis on a pair of terms [t1], [t2] *)
  val destruct2 :
    (prim -> t array -> prim -> t array -> 'a) ->
    (prim -> t array -> int -> 'a) ->
    (int -> prim -> t array -> 'a) ->
    (int -> int -> 'a) ->
    t ->
    t ->
    'a

  (** [is_var t] is equal to [var v] if [equal t (var v)] or [None] if it is not the case *)
  val is_var : t -> var option

  (** [fold f acc term] folds [f] over the subterms of [t] *)
  val fold : (t -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  (** [get_subterm_fwd t fpth] is the subterm of [t] at position defined by the forward path
      [fpth].

      Raises [Get_subterm_oob] if the path is out of bounds.
  *)
  val get_subterm_fwd : t -> Path.forward -> t
end

(** The module type of first-order terms *)
module type Term = sig
  include Term_core

  (** The type of polymorphic maps indexed by variables *)
  type 'a var_map

  include Hashed with type t := t

  type var := int

  (** [ub t] is an upper bound on the absolute value of variables contained in [t].
      Equal to {!Int_option.none} if [t] does not contain variables. *)
  val ub : t -> Int_option.t

  (** [map_variables f t] replaces all variables [var i] present in [t] by [f i]. *)
  val map_variables : (int -> t) -> t -> t

  (** [get_subterm t pth] is the subterm of [t] at position defined by the path [pth].

      Raise [Get_subterm_oob] if the path is out of bounds. *)
  val get_subterm : t -> Path.t -> t

  (** [subst ~term ~path f] replaces the subterm of [term] at position [path]
      by [f (get_subterm term path)]. *)
  val subst : term:t -> path:Path.t -> (t -> t) -> t

  (** [fold_variables f acc t] folds [f] over the variables of [t] *)
  val fold_variables : (var -> Path.t -> 'b -> 'b) -> 'b -> t -> 'b

  (** [canon t gen] canonicalizes the term [t] using the variable generator [gen].
      Returns the canonicalized term as well as a map from old to canonicalized variables. *)
  val canon : t -> (unit -> var) -> var var_map * t

  (** [uid t] returns a unique integer attached to [t]. It is guaranteed that if two terms
      have the same [uid], they are equal. *)
  val uid : t -> int
end

(** The module type of substitutions *)
module type Subst = sig
  (** The type of terms *)
  type term

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

  (** [eval v subst] returns [Some t] if [v] is mapped to the term [t] in [subst]
      or [None] if [v] is not in the domain of [subst]. *)
  val eval : var -> t -> term option

  (** Exception-raising variant of {!eval}.
      Raises [Not_found] if [v] is not in the domain of [subst]. *)
  val eval_exn : var -> t -> term

  (** [add v t subst] adds a mapping from [v] to [t] in [subst].
      If [v] is already in the domain of [subst], the previous mapping is replaced.

      Raises [Invalid_argument] if [t] is a variable equal to [v] *)
  val add : var -> term -> t -> t

  (** [unsafe_add] does as {!add} but doen't check for validity of the mapping. *)
  val unsafe_add : var -> term -> t -> t

  (** [lift subst term] applies the substitution [subst] to [term].
      Note that [lift] does not perform an occur check: do not use with
      substitutions that are not well-founded. *)
  val lift : t -> term -> term

  (** [union s1 s2] computes the union of [s1] and [s2].

      Raises [Invalid_argument] if [s1] and [s2] have overlapping domains. *)
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
        an updated {!state}. *)
    val unify : term -> term -> state -> state option

    (** [unify_exn t1 t2 state] unifies terms [t1] and [t2] in state [state] and returns
        an updated {!state}.

        Raises [Cannot_unify] if no solution was found. *)
    val unify_exn : term -> term -> state -> state

    (** [unify_subst s state] unifies [s] with substitution state [state]
        and returns an updated {!state}. *)
    val unify_subst : t -> state -> state option

    (** [unify_subst s1 s2 state] unifies [s1] with [s2] in state [state]
        and returns an updated {!state}. *)
    val unify_subst_exn : t -> state -> state

    (** [generalize t1 t2] checks that there exists a substitution [subst]
        such that [lift t1 subst = t2]. *)
    val generalize : term -> term -> bool

    (** [subst state] returns the substitution underlying the unification state. *)
    val subst : state -> t
  end
end

module type Term_index = sig
  (** [prim] is the type of primitive symbols used in terms. *)
  type prim

  (** [term] is the type of first-order terms. *)
  type term

  (** [subst] is the type of substitutions, i.e. finite functions from variables to {!term}. *)
  type subst

  type var := int

  (** [internal_term] is the internal representation of terms in the index.

      Due to the details of the implementation, it might be the case that
      the result of querying the index is a term containing cycle. This might
      occur if for instance the querying term contains variables overlapping
      the terms contained in the index.

      The type [internal_term] is also used to represent substitutions. *)
  type internal_term

  (** [is_cyclic term] checks whether a term contains a cycle or not. *)
  val is_cyclic : internal_term -> bool

  (** [to_term term] creates a new term representing the internal term [term].

      Raises [Invalid_argument] if [term] contains a cycle. *)
  val to_term : internal_term -> term

  (** [get_subst term] extracts a substitution out of [term] *)
  val get_subst : internal_term -> subst

  (** [reduce fprim fvar term] reduces [term] by recursively
      applying [fprim] on primitives applications and [fvar] on variables.
      If the variable is associated to a term in a substitution, the term is
      passed to [fvar] as [Some term]. *)
  val reduce :
    (prim -> 'a array -> 'a) ->
    (var -> internal_term option -> 'a) ->
    internal_term ->
    'a

  (** [destruct ifprim ifvar t] performs case analysis on the term [t] *)
  val destruct :
    (prim -> internal_term array -> 'a) ->
    (var -> internal_term option -> 'a) ->
    internal_term ->
    'a

  val pp_internal_term : internal_term Fmt.t

  (** ['a t] is the type of term indexes mapping terms to values of type ['a]. *)
  type 'a t

  (** [pp pp_val] allows to pretty-print values of type ['a t] given [pp_val], a
      pretty-printer for values of type ['a]. *)
  val pp : 'a Fmt.t -> 'a t Fmt.t

  (** [create ()] creates an empty index. *)
  val create : unit -> 'a t

  (** The worst-case complexity of all operations below is proportional to the size
      of the index. Practical complexity depends heavily on the term distribution but
      should be much better. *)

  (** [insert term v index] associates the value [v] to [term] in [index]. *)
  val insert : term -> 'a -> 'a t -> unit

  (** [update term f index] associates the value [f None] to [term] if
      [term] is not already in [index], or [f (Some v)] if [v] is already
      bound to [term]. *)
  val update : term -> ('a option -> 'a) -> 'a t -> unit

  (** [iter f index] iterates [f] on all bindings of [index]. *)
  val iter : (term -> 'a -> unit) -> 'a t -> unit

  (** [iter_unfiable f index query] applies [f] on all terms unifiable with [query]. *)
  val iter_unifiable : (term -> 'a -> unit) -> 'a t -> term -> unit

  (** [iter_specialize f index query] applies [f] on all terms specializing [query]. *)
  val iter_specialize : (term -> 'a -> unit) -> 'a t -> term -> unit

  (** [iter_generalize f index query] applies [f] on all terms generalizing [query]. *)
  val iter_generalize : (term -> 'a -> unit) -> 'a t -> term -> unit

  (** The transient variants below are more efficient but must be used with care.
      The lifetime of the [internal_term]s ends when each call to the closure
      returns. Do not keep pointers to those [internal_term]s.  *)

  (** [iter_transient f index] iterates [f] on all bindings of [index].
      Note that the lifetime of the [internal_term] passed to [f] ends
      when [f] returns. *)
  val iter_transient : (internal_term -> 'a -> unit) -> 'a t -> unit

  (** [iter_unfiable_transient f index query] applies [f] on all terms unifiable with [query].
      Note that the lifetime of the [internal_term] passed to [f] ends
      when [f] returns. *)
  val iter_unifiable_transient :
    (internal_term -> 'a -> unit) -> 'a t -> term -> unit

  (** [iter_specialize_transient f index query] applies [f] on all terms specializing [query].
      Note that the lifetime of the [internal_term] passed to [f] ends
      when [f] returns. *)
  val iter_specialize_transient :
    (internal_term -> 'a -> unit) -> 'a t -> term -> unit

  (** [iter_generalize_transient f index query] applies [f] on all terms generalizing [query].
      Note that the lifetime of the [internal_term] passed to [f] ends
      when [f] returns. *)
  val iter_generalize_transient :
    (internal_term -> 'a -> unit) -> 'a t -> term -> unit
end
