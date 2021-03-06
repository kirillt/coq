(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Decl_kinds
open Term
open Context
open Evd
open Environ
open Nametab
open Mod_subst
open Constrexpr
open Pp
open Globnames

type contexts = Parameters | Properties

type typeclass_error =
  | NotAClass of constr
  | UnboundMethod of global_reference * Id.t located (** Class name, method *)
  | NoInstance of Id.t located * constr list
  | UnsatisfiableConstraints of
    evar_map * (existential_key * Evar_kinds.t) option * Evar.Set.t option
    (** evar map, unresolvable evar, connex component *)
  | MismatchedContextInstance of contexts * constr_expr list * rel_context (** found, expected *)

exception TypeClassError of env * typeclass_error

val not_a_class : env -> constr -> 'a

val unbound_method : env -> global_reference -> Id.t located -> 'a

val no_instance : env -> Id.t located -> constr list -> 'a

val unsatisfiable_constraints : env -> evar_map -> evar option ->
  Evar.Set.t option -> 'a

val mismatched_ctx_inst : env -> contexts -> constr_expr list -> rel_context -> 'a

val unsatisfiable_exception : exn -> bool
