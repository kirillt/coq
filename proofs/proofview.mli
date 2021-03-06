(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* The proofview datastructure is a pure datastructure underlying the notion
   of proof (namely, a proof is a proofview which can evolve and has safety
   mechanisms attached).
   The general idea of the structure is that it is composed of a chemical
   solution: an unstructured bag of stuff which has some relations with
   one another, which represents the various subnodes of the proof. Together
   with a comb: a datastructure that gives some order to some of these nodes,
   namely the (focused) open goals.
   The natural candidate for the solution is an {!Evd.evar_map}, that is
   a calculus of evars. The comb is then a list of goals (evars wrapped
   with some extra information, like possible name anotations).
   There is also need of a list of the evars which initialised the proofview
   to be able to return information about the proofview. *)

open Term

type proofview 


(* Returns a stylised view of a proofview for use by, for instance,
   ide-s. *)
(* spiwack: the type of [proofview] will change as we push more
   refined functions to ide-s. This would be better than spawning a
   new nearly identical function everytime. Hence the generic name. *)
(* In this version: returns the list of focused goals together with
   the [evar_map] context. *)
val proofview : proofview -> Goal.goal list * Evd.evar_map

(* Initialises a proofview, the argument is a list of environement, 
   conclusion types, creating that many initial goals. *)
val init : Evd.evar_map -> (Environ.env * Term.types) list -> proofview

(* Returns whether this proofview is finished or not. That is,
   if it has empty subgoals in the comb. There could still be unsolved
   subgoaled, but they would then be out of the view, focused out. *)
val finished : proofview -> bool

(* Returns the current value of the proofview partial proofs. *)
val return : proofview -> Evd.evar_map

val partial_proof : proofview -> constr list
val initial_goals : proofview -> (constr * types) list
val emit_side_effects : Declareops.side_effects -> proofview -> proofview

(*** Focusing operations ***)

(* [IndexOutOfRange] occurs in case of malformed indices
   with respect to list lengths. *)
exception IndexOutOfRange

(* Type of the object which allow to unfocus a view.*)
type focus_context

(* Returns a stylised view of a focus_context for use by, for
   instance, ide-s. *)
(* spiwack: the type of [focus_context] will change as we push more
   refined functions to ide-s. This would be better than spawning a
   new nearly identical function everytime. Hence the generic name. *)
(* In this version: returns the number of goals that are held *)
val focus_context : focus_context -> Goal.goal list * Goal.goal list

(* [focus i j] focuses a proofview on the goals from index [i] to index [j] 
   (inclusive). (i.e. goals number [i] to [j] become the only goals of the
   returned proofview).
   It returns the focus proof, and a context for the focus trace. *)
val focus : int -> int -> proofview -> proofview * focus_context

(* Unfocuses a proofview with respect to a context. *)
val unfocus : focus_context -> proofview -> proofview

(* The tactic monad:
   - Tactics are objects which apply a transformation to all
     the subgoals of the current view at the same time. By opposition
     to the old vision of applying it to a single goal. It allows 
     tactics such as [shelve_unifiable] or tactics to reorder
     the focused goals (not done yet).
     (* spiwack: the ordering of goals, though, is actually rather
        brittle. It would be much more interesting to find a more
        robust way to adress goals, I have no idea at this time 
        though*) 
     or global automation tactic for dependent subgoals (instantiating
     an evar has influences on the other goals of the proof in progress,
     not being able to take that into account causes the current eauto
     tactic to fail on some instances where it could succeed).
     Another benefit is that it is possible to write tactics that can
     be executed even if there are no focused goals.
   - Tactics form a monad ['a tactic], in a sense a tactic can be 
     seens as a function (without argument) which returns a value
     of type 'a and modifies the environement (in our case: the view).
     Tactics of course have arguments, but these are given at the 
     meta-level as OCaml functions.
     Most tactics in the sense we are used to return [()], that is
     no really interesting values. But some might pass information 
     around.
     (* spiwack: as far as I'm aware this doesn't really relate to
        F. Kirchner and C. Muñoz.
     *)
     The tactics seen in Coq's Ltac are (for now at least) only 
     [unit tactic], the return values are kept for the OCaml toolkit.
     The operation or the monad are [Proofview.tclUNIT] (which is the 
     "return" of the tactic monad) [Proofview.tclBIND] (which is
     the "bind") and [Proofview.tclTHEN] (which is a specialized
     bind on unit-returning tactics).
*)


type +'a tactic 

(* Applies a tactic to the current proofview. *)
(* the return boolean signals the use of an unsafe tactic, in which
   case it is [false]. *)
val apply : Environ.env -> 'a tactic -> proofview -> 'a
                                                   * proofview
                                                   * (bool*(Goal.goal list*Goal.goal list))

(*** tacticals ***)

(* Unit of the tactic monad *)
val tclUNIT : 'a -> 'a tactic

(* Bind operation of the tactic monad *)
val tclBIND : 'a tactic -> ('a -> 'b tactic) -> 'b tactic

(* Interprets the ";" (semicolon) of Ltac.
   As a monadic operation, it's a specialized "bind"
   on unit-returning tactic (meaning "there is no value to bind") *)
val tclTHEN : unit tactic -> 'a tactic -> 'a tactic

(* [tclIGNORE t] has the same operational content as [t],
   but drops the value at the end. *)
val tclIGNORE : 'a tactic -> unit tactic

(* [tclOR t1 t2 = t1] as long as [t1] succeeds. Whenever the successes
   of [t1] have been depleted and it failed with [e], then it behaves
   as [t2 e].  No interleaving at this point. *)
val tclOR : 'a tactic -> (exn -> 'a tactic) -> 'a tactic

(* [tclZERO] always fails *)
val tclZERO : exn -> 'a tactic

(* [tclORELSE t1 t2] behaves like [t1] if [t1] succeeds at least once
   or [t2 e] if [t1] fails with [e]. *)
val tclORELSE : 'a tactic -> (exn -> 'a tactic) -> 'a tactic

(* [tclIFCATCH a s f] is a generalisation of [tclORELSE]: if [a]
   succeeds at least once then it behaves as [tclBIND a s] otherwise, if [a]
   fails with [e], then it behaves as [f e]. *)
val tclIFCATCH : 'a tactic -> ('a -> 'b tactic) -> (exn -> 'b tactic) -> 'b tactic

(* [tclONCE t] fails if [t] fails, otherwise it has exactly one
   success. *)
val tclONCE : 'a tactic -> 'a tactic

(* [tclONCE e t] succeeds as [t] if [t] has exactly one
   success. Otherwise it fails.  It may behave differently than [t] as
   there may be extra non-logical effects used to discover that [t]
   does not have a second success. Moreover the second success may be
   conditional on the error recieved: [e] is used. *)
val tclEXACTLY_ONCE : exn -> 'a tactic -> 'a tactic

(* Focuses a tactic at a range of subgoals, found by their indices.
   The other goals are restored to the focus when the tactic is done.

   If the specified range doesn't correspond to existing goals, fails
   with [NoSuchGoals]. *)
exception NoSuchGoals
val tclFOCUS : int -> int -> 'a tactic -> 'a tactic

(* Focuses a tactic at a range of subgoals, found by their indices.
   The other goals are restored to the focus when the tactic is done.

   If the specified range doesn't correspond to existing goals, behaves
   like [tclUNIT ()]. *)
val tclTRYFOCUS : int -> int -> unit tactic -> unit tactic

(* Dispatch tacticals are used to apply a different tactic to each goal under
   consideration. They come in two flavours:
   [tclDISPATCH] takes a list of [unit tactic]-s and build a [unit tactic].
   [tclDISPATCHL] takes a list of ['a tactic] and returns an ['a list tactic].

   They both work by applying each of the tactic to the corresponding
   goal (starting with the first goal). In the case of [tclDISPATCHL],
   the tactic returns a list of the same size as the argument list (of
   tactics), each element being the result of the tactic executed in
   the corresponding goal.

   When the length of the tactic list is not the number of goal,
   raises [SizeMismatch] *)
exception SizeMismatch
val tclDISPATCH : unit tactic list -> unit tactic
val tclDISPATCHL : 'a tactic list -> 'a list tactic

(* [tclEXTEND b r e] is a variant to [tclDISPATCH], where the [r] tactic
    is "repeated" enough time such that every goal has a tactic assigned to it
    ([b] is the list of tactics applied to the first goals, [e] to the last goals, and [r]
    is applied to every goal in between. *)
val tclEXTEND : unit tactic list -> unit tactic -> unit tactic list -> unit tactic

(* [tclINDEPENDENT tac] runs [tac] on each goal successively, from the
   first one to the last one. Backtracking in one goal is independent of
   backtracking in another. *)
val tclINDEPENDENT : unit tactic -> unit tactic

(* [tclSENSITIVE] views goal-type tactics as a special kind of tactics.*)
val tclSENSITIVE : Goal.subgoals Goal.sensitive -> unit tactic 


(* [tclPROGRESS t] behaves has [t] as long as [t] progresses. *)
val tclPROGRESS : 'a tactic -> 'a tactic

(* [tclEVARMAP] doesn't affect the proof, it returns the current evar_map. *)
val tclEVARMAP : Evd.evar_map tactic

(* [tclENV] doesn't affect the proof, it returns the current
   environment.  It is not the environment of a particular goal,
   rather the "global" environment of the proof. The goal-wise
   environment is returned by {!Proofview.Goal.env}. *)
val tclENV : Environ.env tactic

(* Shelves all the goals under focus. The goals are placed on the
   shelf for later use (or being solved by side-effects). *)
val shelve : unit tactic

(* Shelves the unifiable goals under focus, i.e. the goals which
   appear in other goals under focus (the unfocused goals are not
   considered). *)
val shelve_unifiable : unit tactic

(* [unshelve l p] adds all the goals in [l] at the end of the focused
   goals of p *)
val unshelve : Goal.goal list -> proofview -> proofview


(* Gives up on the goal under focus. Reports an unsafe status. Proofs
   with given up goals cannot be closed. *)
val give_up : unit tactic

exception Timeout
(** [tclTIMEOUT n t] can have only one success.
    In case of timeout if fails with [tclZERO Timeout]. *)
val tclTIMEOUT : int -> 'a tactic -> 'a tactic

(** [mark_as_unsafe] signals that the current tactic is unsafe. *)
val mark_as_unsafe : unit tactic

val list_map : ('a -> 'b tactic) -> 'a list -> 'b list tactic

(*** Commands ***)

val in_proofview : proofview -> (Evd.evar_map -> 'a) -> 'a

(* spiwack: to help using `bind' like construct consistently. A glist
   is promissed to have exactly one element per goal when it is
   produced. *)
type 'a glist  = private 'a list

(* Notations for building tactics. *)
module Notations : sig

  (* tclBIND *)
  val (>=) : 'a tactic -> ('a -> 'b tactic) -> 'b tactic
  (* [t >>= k] is [t >= fun l -> tclDISPATCH (List.map k l)].
     The [t] is supposed to return a list of values of the size of the
     list of goals. [k] is then applied to each of this value in the
     corresponding goal. *)
  val (>>=) : 'a glist tactic -> ('a -> unit tactic) -> unit tactic
  (* [t >>== k] acts as [t] except that [k] returns a list of value
     corresponding to its produced subgoals. *)
  val (>>==) : 'a glist tactic -> ('a -> 'b glist tactic) -> 'b glist tactic

  (* tclTHEN *)
  val (<*>) : unit tactic -> 'a tactic -> 'a tactic
  (* tclOR *)
  val (<+>) : 'a tactic -> 'a tactic -> 'a tactic
end


(*** Compatibility layer with <= 8.2 tactics ***)
module V82 : sig
  type tac = Goal.goal Evd.sigma -> Goal.goal list Evd.sigma 
  val tactic : tac -> unit tactic

  (* normalises the evars in the goals, and stores the result in
     solution. *)
  val nf_evar_goals : unit tactic

  val tclEVARS : Evd.evar_map -> unit tactic

  val has_unresolved_evar : proofview -> bool

  (* Main function in the implementation of Grab Existential Variables.
     Resets the proofview's goals so that it contains all unresolved evars
     (in chronological order of insertion). *)
  val grab : proofview -> proofview

  (* Returns the open goals of the proofview together with the evar_map to 
     interprete them. *)
  val goals : proofview -> Goal.goal list Evd.sigma

  val top_goals : proofview -> Goal.goal list Evd.sigma
  
  (* returns the existential variable used to start the proof *)
  val top_evars : proofview -> Evd.evar list
    
  (* Implements the Existential command *)
  val instantiate_evar : int -> Constrexpr.constr_expr -> proofview -> proofview

  (* Caution: this function loses quite a bit of information. It
     should be avoided as much as possible.  It should work as
     expected for a tactic obtained from {!V82.tactic} though. *)
  val of_tactic : 'a tactic -> tac

  (* marks as unsafe if the argument is [false] *)
  val put_status : bool -> unit tactic

  (* exception for which it is deemed to be safe to transmute into
     tactic failure. *)
  val catchable_exception : exn -> bool
end

(* The module goal provides an interface for goal-dependent tactics. *)
(* spiwack: there are still parts of the code which depend on proofs/goal.ml.
   Eventually I'll try to remove it in favour of [Proofview.Goal] *)
module Goal : sig

  (* The type of goals *)
  type t

  (* [concl], [hyps], [env] and [sigma] given a goal [gl] return
     respectively the conclusion of [gl], the hypotheses of [gl], the
     environment of [gl] (i.e. the global environment and the hypotheses)
     and the current evar map. *)
  val concl : t -> Term.constr
  val hyps : t -> Context.named_context
  val env : t -> Environ.env
  val sigma : t -> Evd.evar_map

  (* [lift_sensitive s] returns the list corresponding to the evaluation
     of [s] on each of the focused goals *)
  val lift : 'a Goal.sensitive -> 'a glist tactic

  (* [return x] returns a copy of [x] per focused goal. *)
  val return : 'a -> 'a glist tactic

  (* [enter t] execute the goal-dependent tactic [t] in each goal
     independently. In particular [t] need not backtrack the same way in
     each goal. *)
  val enter : (t -> unit tactic) -> unit tactic
  (* [enterl t] works like [enter t] except that [t] returns a value
     in each of the produced subgoals. *)
  val enterl : (t -> 'a glist tactic) -> 'a glist tactic


  (* compatibility: avoid if possible *)
  val goal : t -> Goal.goal
end

(* The [NonLogical] module allows to execute side effects in tactics
   (non-logical side-effects are not discarded at failures). *)
module NonLogical : sig

  (* ['a t] is the monadic type of side-effect issuing commands. *)
  type +'a t

  (* ['a ref] is a type of references to assignables. *)
  type 'a ref

  (* The unit of the non-logical monad. *)
  val ret : 'a -> 'a t
  (* The bind of the non-logical monad. *)
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  (* [ignore c] drops the returned value, otherwise behaves like
     [c]. *)
  val ignore : 'a t -> unit t
  (* Specialised version of [bind] when the first argument return
     [()]. *)
  val seq : unit t -> 'a t -> 'a t

  (* [new_ref x] creates a reference containing [x]. *)
  val new_ref : 'a -> 'a ref t
  (* [set r x] assigns [x] to [r]. *)
  val set : 'a ref -> 'a -> unit t
  (* [get r] returns the value of [r] *)
  val get : 'a ref -> 'a t

  (* [read_line] reads one line on the standard input. *)
  val read_line : string t
  (* [print_char a] prints [a] to the standard output. *)
  val print_char : char -> unit t
  (* [print stm] prints [stm] to the standard output. *)
  val print : Pp.std_ppcmds -> unit t

  (* [raise e] raises an error [e] which cannot be caught by logical
     operation.*)
  val raise : exn -> 'a t
  (* [catch c h] runs the command [c] until it returns a value [v], in
     which case [catch c h] behaves like [c], or [c] raises an exception
     [e] in which case it continues with [h e]. *)
  val catch : 'a t -> (exn -> 'a t) -> 'a t
  (* [timeout t c] runs [c] for [t] seconds if [c] succeeds in time
     then [timeout t c] behaves like [c], otherwise it fails with
     [Proof_errors.Timeout]. *)
  val timeout : int -> 'a t -> 'a t


  (* [run c] performs [c]'s side effects for real. *)
  val run : 'a t -> 'a

end

(* [tclLIFT c] includes the non-logical command [c] in a tactic. *)
val tclLIFT : 'a NonLogical.t -> 'a tactic
