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

module type Term_index = sig
  (** [prim] is the type of primitive symbols used in terms. *)
  type prim

  (** [term] is the type of first-order terms. *)
  type term

  type var := int

  (** [iterm] is the internal representation of terms in the index.

      Due to the details of the implementation, it might be the case that
      the result of querying the index is a term containing cycles. This might
      occur if for instance the querying term contains variables overlapping
      the terms contained in the index.

      The type [iterm] is also used to represent substitutions. *)
  type iterm

  (** [is_cyclic term] checks whether a term contains a cycle or not. *)
  val is_cyclic : iterm -> bool

  (** [to_term term] creates a new term representing the internal term [term].

      Raises [Invalid_argument] if [term] contains a cycle. *)
  val to_term : iterm -> term

  (** [fold_subst f acc term] folds over the substitution contained in [term]. This function
      is meant to be called on transient terms obtained during matching operations. *)
  val fold_subst : (var -> iterm -> 'a -> 'a) -> iterm -> 'a -> 'a

  (** [reduce fprim fvar term] reduces [term] by recursively
      applying [fprim] on primitives applications and [fvar] on variables.
      If the variable is associated to a term in a substitution, the term is
      passed to [fvar] as [Some term]. *)
  val reduce :
    (prim -> 'a array -> 'a) -> (var -> iterm option -> 'a) -> iterm -> 'a

  (** [destruct ifprim ifvar t] performs case analysis on the term [t] *)
  val destruct :
    (prim -> iterm array -> 'a) -> (var -> iterm option -> 'a) -> iterm -> 'a

  val pp_iterm : iterm Fmt.t

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
      The lifetime of the [iterm]s ends when each call to the closure
      returns. Do not keep pointers to those [iterm]s.  *)

  (** [iter_transient f index] iterates [f] on all bindings of [index].
      Note that the lifetime of the [iterm] passed to [f] ends
      when [f] returns. *)
  val iter_transient : (iterm -> 'a -> unit) -> 'a t -> unit

  (** [iter_unfiable_transient f index query] applies [f] on all terms unifiable with [query].
      Note that the lifetime of the [iterm] passed to [f] ends
      when [f] returns. *)
  val iter_unifiable_transient : (iterm -> 'a -> unit) -> 'a t -> term -> unit

  (** [iter_specialize_transient f index query] applies [f] on all terms specializing [query].
      Note that the lifetime of the [iterm] passed to [f] ends
      when [f] returns. *)
  val iter_specialize_transient : (iterm -> 'a -> unit) -> 'a t -> term -> unit

  (** [iter_generalize_transient f index query] applies [f] on all terms generalizing [query].
      Note that the lifetime of the [iterm] passed to [f] ends
      when [f] returns. *)
  val iter_generalize_transient : (iterm -> 'a -> unit) -> 'a t -> term -> unit
end
