(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Declarations
open Environ
open Entries
open Pp
open Libnames
open Names
open Constrexpr
open Misctypes

(** Module internalization errors *)

type module_internalization_error =
  | NotAModuleNorModtype of string
  | IncorrectWithInModule
  | IncorrectModuleApplication

exception ModuleInternalizationError of module_internalization_error

(** Module expressions and module types are interpreted relatively to
   possible functor or functor signature arguments. When the input kind
   is ModAny (i.e. module or module type), we tries to interprete this ast
   as a module, and in case of failure, as a module type. The returned
   kind is never ModAny, and it is equal to the input kind when this one
   isn't ModAny. *)

val interp_module_ast :
  env -> module_kind -> module_ast -> module_struct_entry * module_kind
