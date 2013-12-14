(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*s Production of Java syntax. *)

open Pp
open Util
open Names
open Nameops
open Libnames
open Table
open Miniml
open Mlutil
open Common

(* PP Utilities *)

let pp_wrap2 l r body = str l ++ body ++ str r
let pp_wrap         c = pp_wrap2 c c
let pp_wrap_b         = pp_wrap2 "{" "}"
let pp_wrap_g         = pp_wrap2 "<" ">"
let pp_wrap_b_nl body = pp_wrap_b (pp_wrap "\n" body)

let pp_list sep l =
  match l with
  | [] -> mt ()
  | h::t -> h ++ prlist_strict (fun x -> str sep ++ x) t

let pp_list' sep f l = pp_list sep @@ List.map f l

let pr_lower_id id = str @@ String.uncapitalize @@ string_of_id id
let pr_upper_id id = str @@ String.capitalize   @@ string_of_id id

let basename = function
  | MPfile xs -> string_of_id @@ List.hd @@ repr_dirpath xs
  | _ -> assert false

let range l r =
  let rec work acc l r =
    if l <= r
       then work (l::acc) (succ l) r
       else acc
  in List.rev @@ work [] l r
  (* Could be `List.of_enum (l--r)' *)

let mktvar i = id_of_string @@ Char.escaped @@ Char.chr @@ Char.code 'a' + i - 1

(* Type utilities *)

let unfold_arrows typ =
  let rec work acc = function
    | Tarr (l,r) -> work (l::acc) r
    | x -> (List.rev acc,x)
  in work [] typ

let unfold_arrows' typ =
  let (args,typ) = unfold_arrows typ
  in List.concat [args;[typ]]

let rec count_variables typ =
  let work acc = function
    | Tglob (ref,args) -> count_variables' @@ args
    | Tarr _ as arrow -> count_variables' @@ unfold_arrows' arrow
    | Tvar i -> Pervasives.max acc i
    | _ -> assert false
  in work 0 typ

and count_variables' types =
  let rec work acc = function
    | typ::types' -> work (Pervasives.max acc @@ count_variables typ) types'
    | [] -> acc
  in work 0 types
  
(* Java utilities *)

let keywords =
  List.fold_right (fun s -> Idset.add (id_of_string s))
  [ (* TODO *) "public"; "protected"; "private"; "static"; "class" ]
  Idset.empty

let escape = String.map (fun c -> if c = '\'' then '_' else c) (* dirty *)

let pp_global kn ref = str @@ escape @@ if is_inline_custom ref then find_custom ref else Common.pp_global kn ref

let rec pp_type vars = function
    | Tglob (ref,args) -> pp_global Type ref ++
      if args = []
        then mt ()
        else pp_wrap_g @@ pp_list' "," (pp_type vars) args
    | Tvar i -> pr_upper_id @@ List.nth vars (pred i)
    | _ -> assert false

let pp_comment s = str "// " ++ s ++ fnl ()
let pp_comment_b = pp_wrap2 "/* " " */"

let pp_generic vars = if vars != [] then pp_wrap_g @@ pp_list' "," pr_upper_id vars else mt ()

let pp_enum name items =
  str "public static enum " ++ str name ++ str " " ++
  (pp_wrap_b @@ pp_wrap " " @@ pp_list ", " items)

let pp_class header body = header ++ str " " ++ pp_wrap_b_nl body

let pp_method modifier (typ,vars) name (args,names) body =
  let args = List.mapi (fun i typ -> (typ,names.(i))) args in
  let pp_args = pp_list' ", " (fun (typ,name) -> str "final " ++ pp_type vars typ ++ str (" "^name)) args
  in str modifier ++ str " " ++ pp_generic vars ++ str " " ++ pp_type vars typ ++ str " " ++
     str name ++ str "(" ++ pp_args ++ str ")" ++
     pp_wrap_b_nl body

(* Pretty-printing of expressions *)

let temporary_typemap = ref [] (* HACK *)
let search ref =
  let rec work = function
    | [] -> assert false
    | (ref',typ)::tl -> if ref = ref' then typ else work tl
  in work temporary_typemap.contents

let pp_expr env (typ,vars) term =
  let mkvar  i   = "var" ^ Pervasives.string_of_int i in
  let return i r = (succ i,(mkvar i, r)) in
  let rec pp_expr' k env typ =
    let mock       = return k @@ pp_type vars typ ++ (str @@ " " ^ (mkvar k) ^ " = null; /* not implemented yet */\n") in
    function
    | MLrel    i           -> let name = env.(pred i) in (k,(name,mt ()))
    | MLapp   (f,args)     ->
      (* So far, we can't check type of function against arguments;
         one of the solutions: to implement application one-by-one (via lambdas). *)
      (match f with
       | MLglob ref ->
         let (typs,typ)  = unfold_arrows @@ search ref (* HACK *) in
         let step (k',acc) (argtyp,argterm) = let res = pp_expr' k' env argtyp argterm in (fst res,(snd res)::acc) in
         let (k'',args') = List.fold_left step (k,[]) @@ List.combine typs args in
         let      args'' = List.rev     args'  in
         let names       = List.map fst args'' in
         let output      = pp_list "\n" @@ List.map snd args'' in
         let call        =
           pp_type vars typ ++ str (" " ^ mkvar k'' ^ " = ") ++
           pp_global Term ref ++
             str (".apply(") ++ pp_list' ", " str names ++ str ");\n"
         in  return k'' @@ output ++ call
       | x -> assert false
       (* TODO
         For lambdas I need:
           1) smart representation of lambdas as objects;
           2) get types for variables, etc.
             a) infer it manually
             b) look, what can suggest Coq source
       *)
       )
    | MLlam    _           -> mock (* collect_lams a ; push_vars (List.map id_of_mlid fl) env *)
    | MLletin (id,a1,a2)   -> mock (* push_vars [id_of_mlid id] env *)
    | MLglob   ref         -> mock
    | MLcons  (_,r,a)      -> mock (* assert (args=[]); *)
    | MLtuple  l           -> mock (* assert (args=[]); *)
    | MLcase  (typ,t,pv)   -> mock (* is_custom_match pv ; not (is_regular_match pv) ; if ids <> [] then named_lams (List.rev ids) e ; else dummy_lams (ast_lift 1 e) 1 ; find_custom_match pv *)
    | MLfix   (i,ids,defs) -> mock (* push_vars (List.rev (Array.to_list ids)) env *)
    | MLexn    s           -> mock
    | MLdummy              -> mock
    | MLmagic  a           -> mock
    | MLaxiom              -> mock
  in snd @@ pp_expr' 0 env typ term

(* Pretty-printing of inductive types *)

let pp_tags constructors =
  str "public Tag tag;\n" ++
  (pp_enum "Tag" @@ List.map (fun (r,_) -> pp_global Cons r) constructors)

let pp_constructor_field (i,typ) = str "public final " ++ typ () ++ str " field" ++ i ++ str ";\n"

let pp_constructor_args types = pp_list' ", " (fun (i,typ) -> typ () ++ str " arg" ++ i) types

let pp_constructor_class vars father suffix (r,types) =
  let types = List.mapi (fun i typ -> (str @@ Pervasives.string_of_int i, (fun _ -> pp_type vars typ))) types in
  let name  = pp_global Cons r
  in  pp_class (str "public static final class " ++ name ++ suffix ++ str " extends " ++ father ++ suffix) @@
  prlist_strict pp_constructor_field types ++
  str "public " ++ name ++ str "(" ++ pp_constructor_args types ++ str ") " ++
  (pp_wrap_b_nl @@
    (prlist_strict (fun (i,_) -> str "field" ++ i ++ str " = arg" ++ i ++ str ";\n") types) ++
    str "tag = Tag." ++ name ++ str ";")

let pp_inductive_class ki vars cs =
  let constructors = Array.to_list @@ Array.mapi (fun i c -> ConstructRef (ki,i+1),c) cs in
  let name = pp_global Type (IndRef ki) in
  let arg  = pp_generic vars
  in  pp_class (str "public static abstract class " ++ name ++ arg) @@
    pp_tags constructors ++ str "\n" ++
    (pp_list' "\n" (pp_constructor_class vars name arg) constructors)

let rec pp_inductive kn ind =
  let pp_logical packet =
    pp_comment_b @@
      (pr_id packet.ip_typename ++ str " : logical inductive") ++
      (str " with constructors : " ++ prvect_with_sep spc pr_id packet.ip_consnames) in
  let pp_one_ind ki vars cs =
    let vars = rename_tvars keywords vars in
    if Array.length cs = 0 then str "/* empty inductive */"
      else pp_inductive_class ki vars cs in
      (*TODO: generate toString()*)
  let pp_ind_packet ki packet =
    if is_custom (IndRef ki)
      then pp_comment_b @@ str "is_custom = true"
      else if packet.ip_logical
           then pp_logical packet
           else pp_one_ind ki packet.ip_vars packet.ip_types
  in pp_list "\n" @@
    List.mapi (fun i packet -> pp_ind_packet (kn,i) packet) @@
    Array.to_list ind.ind_packets

(* Pretty-printing of other declarations *)

let pp_typedecl ref vars typ =
  if is_inline_custom ref
    then mt ()
    else pp_class (str "public static class " ++ pp_global Type ref ++
                   str " extends " ++ pp_type vars typ) @@ str ""

let pp_function ref def  typ =
  temporary_typemap := (ref,typ)::temporary_typemap.contents; (* HACK *)
  if is_inline_custom ref
    then mt ()
    else match typ with
         | Tarr (l,r) ->
           if is_custom ref
             then assert false
             else let (args,typ) = unfold_arrows typ in
                  let  vars      = List.map mktvar @@ range 1 @@ count_variables' @@ typ::args in 
                  let  names     = (Array.of_list @@ List.mapi (fun i _ -> "arg" ^ Pervasives.string_of_int i) args) in
                  let (res,code) = pp_expr names (typ,vars) @@ snd @@ collect_lams def
                  in pp_class (str "public static class " ++ pp_global Term ref) @@
                     pp_method "public static" (typ,vars) "apply" (args,names) @@
                       code ++ str ("return " ^ res ^ ";")
         | _ -> assert false (* TODO: try to implement *)

let pp_decl = function
  | Dtype (ref , vars, typ  ) -> pp_typedecl ref vars typ
  | Dterm (ref , def , typ  ) -> pp_function ref def  typ
  | Dfix  (refs, defs, types) -> pp_list' "\n" (fun i -> let k = pred i in pp_function refs.(k) defs.(k) types.(k)) @@ range 1 @@ Array.length refs
  | Dind  (kn  , ind        ) -> pp_inductive kn ind (* special case: ind.ind_kind = Singleton *)

let pp_struct =
  let pp_element = function
    | (l,SEdecl d) -> pp_decl d
    | _ -> assert false in
  let pp_elements (mp,sel) =
    push_visible mp [];
    let output = pp_list' "\n" pp_element sel in
    pop_visible ();
    pp_class (str @@ "public interface " ^ basename mp) @@
      output
  in
  pp_list' "\n" pp_elements

let java_descr = {
  keywords = keywords;
  file_suffix = ".java";
  preamble = (fun _ _ _ -> mt ());
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ -> mt ());
  pp_sig = (fun _ -> mt ());
  pp_decl = pp_decl;
}
