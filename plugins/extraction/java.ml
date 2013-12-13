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

let mkvar i = id_of_string @@ Char.escaped @@ Char.chr @@ Char.code 'a' + i - 1

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

let pp_global kn ref = str @@ if is_inline_custom ref then find_custom ref else Common.pp_global kn ref

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

let pp_method_args vars args = pp_list' ", " (fun (typ,name) -> str "final " ++ pp_type vars typ ++ str (" "^name)) args

let pp_method modifier typ name args body =
  let vars = List.map mkvar @@ range 1 @@ count_variables' @@ typ::args in 
  let args = List.mapi (fun i typ -> (typ,"arg"^(Pervasives.string_of_int i))) args
  in str modifier ++ str " " ++ pp_generic vars ++ str " " ++ pp_type vars typ ++ str " " ++
     str name ++ str "(" ++ pp_method_args vars args ++ str ")" ++
     pp_wrap_b_nl body

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let pp_abst = function
  | [] -> (mt ())
  | l  -> (str "\\" ++
             prlist_with_sep (fun () -> (str " ")) pr_id l ++
             str " ->" ++ spc ())

let expr_needs_par = function
  | MLlam _  -> true
  | MLcase _ -> false (* now that we use the case ... of { ... } syntax *)
  | _        -> false

let rec pp_expr par env args =
  let apply st = pp_apply st par args
  and apply2 st = pp_apply2 st par args in
  function
    | MLrel n ->
	let id = get_db_name n env in apply (pr_id id)
    | MLapp (f,args') ->
	let stl = List.map (pp_expr true env []) args' in
        pp_expr par env (stl @ args) f
    | MLlam _ as a ->
      	let fl,a' = collect_lams a in
	let fl,env' = push_vars (List.map id_of_mlid fl) env in
	let st = (pp_abst (List.rev fl) ++ pp_expr false env' [] a') in
	apply2 st
    | MLletin (id,a1,a2) ->
	let i,env' = push_vars [id_of_mlid id] env in
	let pp_id = pr_id (List.hd i)
	and pp_a1 = pp_expr false env [] a1
	and pp_a2 = pp_expr (not par && expr_needs_par a2) env' [] a2 in
	let pp_def =
	  str "let {" ++ cut () ++
	  hov 1 (pp_id ++ str " = " ++ pp_a1 ++ str "}")
	in
	apply2 (hv 0 (hv 0 (hv 1 pp_def ++ spc () ++ str "in") ++
		       spc () ++ hov 0 pp_a2))
    | MLglob r ->
	apply (pp_global Term r)
    | MLcons (_,r,a) as c ->
        assert (args=[]);
        begin match a with
	  | _ when is_native_char c -> pp_native_char c
	  | [] -> pp_global Cons r
	  | [a] ->
	    pp_par par (pp_global Cons r ++ spc () ++ pp_expr true env [] a)
	  | _ ->
	    pp_par par (pp_global Cons r ++ spc () ++
			prlist_with_sep spc (pp_expr true env []) a)
	end
    | MLtuple l ->
        assert (args=[]);
        pp_boxed_tuple (pp_expr true env []) l
    | MLcase (_,t, pv) when is_custom_match pv ->
        if not (is_regular_match pv) then
	  error "Cannot mix yet user-given match and general patterns.";
	let mkfun (ids,_,e) =
	  if ids <> [] then named_lams (List.rev ids) e
	  else dummy_lams (ast_lift 1 e) 1
	in
	let pp_branch tr = pp_expr true env [] (mkfun tr) ++ fnl () in
	let inner =
	  str (find_custom_match pv) ++ fnl () ++
	  prvect pp_branch pv ++
	  pp_expr true env [] t
	in
	apply2 (hov 2 inner)
    | MLcase (typ,t,pv) ->
        apply2
	  (v 0 (str "case " ++ pp_expr false env [] t ++ str " of {" ++
		fnl () ++ pp_pat env pv))
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix_term par env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s ->
	(* An [MLexn] may be applied, but I don't really care. *)
	pp_par par (str "Prelude.error" ++ spc () ++ qs s)
    | MLdummy ->
	str "__" (* An [MLdummy] may be applied, but I don't really care. *)
    | MLmagic a ->
	pp_apply (str "unsafeCoerce") par (pp_expr true env [] a :: args)
    | MLaxiom -> pp_par par (str "Prelude.error \"AXIOM TO BE REALIZED\"")

and pp_cons_pat par r ppl =
  pp_par par (pp_global Cons r ++ space_if (ppl<>[]) ++ prlist_with_sep spc identity ppl)

and pp_gen_pat par ids env = function
  | Pcons (r,l) -> pp_cons_pat par r (List.map (pp_gen_pat true ids env) l)
  | Pusual r -> pp_cons_pat par r (List.map pr_id ids)
  | Ptuple l -> pp_boxed_tuple (pp_gen_pat false ids env) l
  | Pwild -> str "_"
  | Prel n -> pr_id (get_db_name n env)

and pp_one_pat env (ids,p,t) =
  let ids',env' = push_vars (List.rev_map id_of_mlid ids) env in
  hov 2 (str " " ++
	 pp_gen_pat false (List.rev ids') env' p ++
	 str " ->" ++ spc () ++
	 pp_expr (expr_needs_par t) env' [] t)

and pp_pat env pv =
  prvecti
    (fun i x ->
       pp_one_pat env pv.(i) ++
       if i = Array.length pv - 1 then str "}" else
	 (str ";" ++ fnl ()))
    pv

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix_term par env i (ids,bl) args = assert false (* TODO: wrap usual functions into class? *)
(*
  pp_par par
    (v 0
       (v 1 (str "let {" ++ fnl () ++
	     prvect_with_sep (fun () -> str ";" ++ fnl ())
	       (fun (fi,ti) -> pp_function_term env (pr_id fi) ti)
	       (array_map2 (fun a b -> a,b) ids bl) ++
	     str "}") ++
        fnl () ++ str "in " ++ pp_apply (pr_id ids.(i)) false args))
*)

and pp_function_term env name def = assert false
(*let bl,def = collect_lams def in*)
    (*let bl,env' = push_vars (List.map id_of_mlid bl) env in*)
(*(name ++ pr_binding (List.rev bl) ++*)
 (*str " =" ++ fnl () ++ str "  " ++*)
 (*hov 2 (pp_expr false env' [] def))*)

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

let pp_typedecl ref vars typ =
  if is_inline_custom ref
    then mt ()
    else pp_class (str "public static class " ++ pp_global Type ref ++
                   str " extends " ++ pp_type vars typ) @@ str ""

let pp_function ref def  typ =
  if is_inline_custom ref
    then mt ()
    else match typ with
         | Tarr (l,r) ->
           if is_custom ref
             then assert false
             else let (args,typ) = unfold_arrows typ in
                  pp_class (str "public static class " ++ pp_global Term ref) @@
                    pp_method "public static" typ "apply" args @@
                      str "return null; " ++ pp_comment_b (str "TODO") (* pp_function_term (empty_env ()) name def) *) 
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
      output ++ str "\n"
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
