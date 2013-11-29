(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Term
open Context
open Evd
open Environ
open Constrexpr
open Globnames
(*i*)

type contexts = Parameters | Properties

type typeclass_error =
    | NotAClass of constr
    | UnboundMethod of global_reference * Id.t Loc.located (* Class name, method *)
    | NoInstance of Id.t Loc.located * constr list
    | UnsatisfiableConstraints of
      evar_map * (existential_key * Evar_kinds.t) option * Evar.Set.t option
    | MismatchedContextInstance of contexts * constr_expr list * rel_context (* found, expected *)

exception TypeClassError of env * typeclass_error

let typeclass_error env err = raise (TypeClassError (env, err))

let not_a_class env c = typeclass_error env (NotAClass c)

let unbound_method env cid id = typeclass_error env (UnboundMethod (cid, id))

let no_instance env id args = typeclass_error env (NoInstance (id, args))

let unsatisfiable_constraints env evd ev comp =
  match ev with
  | None ->
    let err = UnsatisfiableConstraints (evd, None, comp) in
    raise (TypeClassError (env, err))
  | Some ev ->
    let loc, kind = Evd.evar_source ev evd in
    let err = UnsatisfiableConstraints (evd, Some (ev, kind), comp) in
    Loc.raise loc (TypeClassError (env, err))

let mismatched_ctx_inst env c n m = typeclass_error env (MismatchedContextInstance (c, n, m))

let rec unsatisfiable_exception exn =
  match exn with
  | TypeClassError (_, UnsatisfiableConstraints _) -> true
  | _ -> false
