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
let pp_wrap_a         = pp_wrap2 "(" ")"
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

let drop n xs =
  let rec work = function
    | (0,   []) -> []
    | (_,   []) -> assert false (* TODO throw exception *)
    | (0,   xs) -> xs
    | (i,x::xs) -> work ((pred i),xs)
  in work (n,xs)

let mktvar i = id_of_string @@ Char.escaped @@ Char.chr @@ Char.code 'a' + i - 1

(* Type utilities *)

let unfold_arrows typ =
  let rec work acc = function
    | Tarr (l,r) -> work (l::acc) r
    | x -> (List.rev acc,x)
  in work [] typ

let unfold_arrows_n n typ =
  let rec work acc = function
    | 0,(Tarr (l,r) as x) -> (List.rev acc,x)
    | i,Tarr (l,r) -> work (l::acc) (pred i,r)
    | 0,x -> (List.rev acc,x)
    | _,_ -> assert false
  in work [] (n,typ)

let unfold_arrows' typ =
  let (args,typ) = unfold_arrows typ
  in List.concat [args;[typ]]

let fold_to_arrow types =
  match List.rev types with
  | last::rest -> List.fold_left (fun arrow typ -> Tarr (typ,arrow)) last rest
  | [] -> assert false

(* TODO: replace with type_maxvar *)
let rec count_variables typ =
  let work acc = function
    | Tglob (ref,args) -> count_variables' @@ args
    | Tarr _ as arrow -> count_variables' @@ unfold_arrows' arrow
    | Tvar i -> Pervasives.max acc i
    | _ -> assert false
  in assert (type_maxvar typ = work 0 typ) ; type_maxvar typ

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

let pp_generic vars = if vars == [] then mt () else pp_wrap_g @@ pp_list' "," pr_upper_id vars

let rec pp_type vars =
  let pp_parameters args =
    if args = []
      then mt ()
      else pp_wrap_g @@ pp_list' "," (pp_type vars) args
  in function
    | Tglob (ref,args) -> pp_global Type ref ++ pp_parameters args
    | Tarr  (l,r) -> str "Function" ++ pp_parameters [l;r]
    | Tvar   i -> (try pr_upper_id @@ List.nth vars (pred i) with Failure "nth" -> str @@ "?" ^ Pervasives.string_of_int i)
    | Tvar'  i -> pp_type vars @@ Tvar i (* TODO: not sure about that *)
    | Tmeta  m ->
      (match m.contents with
       | Some typ -> (* str "/* Tmeta */ " ++ *) pp_type vars typ
       | None -> str "/* Tmeta (empty) */")
    | _ -> assert false

let pp_comment s = str "// " ++ s ++ fnl ()
let pp_comment_b = pp_wrap2 "/* " " */"

let pp_enum name items =
  str "public static enum " ++ str name ++ str " " ++
  (pp_wrap_b @@ pp_wrap " " @@ pp_list ", " items)

let pp_class header body = header ++ str " " ++ pp_wrap_b_nl body

let pp_method binded modifier (typ,vars) name (argtyps,argnames) body =
  let args = List.map (fun (argtyp,argname) -> (argtyp,argname)) @@ List.combine argtyps argnames in
  let pp_args = pp_list' ", " (fun (typ,name) -> str "final " ++ pp_type vars typ ++ str (" "^name)) args
  in str modifier ++ (if not binded && vars != [] then str " " ++ pp_generic vars else mt ()) ++ str " " ++ pp_type vars typ ++ str " " ++
     str name ++ str "(" ++ pp_args ++ str ")" ++
     pp_wrap_b_nl body

(* Pretty-printing of expressions *)

let pp_expr env (typ,vars) term =
  let pp_consname typ ref =
    (* DIRTY: Replace it with proper creation of submodule for inductive type, so e.g. Datatypes.S will become Datatypes.nat.S *)
    let raw_name     = string_of_ppcmds @@ pp_type vars typ in
    let i            = try String.index raw_name '<' with Not_found -> String.length raw_name in
    let l            = String.length raw_name in
    let base         = String.sub raw_name 0 i in
    let generic      = String.sub raw_name i (l - i) in
    let raw_consname = string_of_ppcmds @@ pp_global Cons ref in
    let i'           = try succ @@ String.index raw_consname '.' with Not_found -> 0 in
    let l'           = String.length raw_consname in
    let consname     = String.sub raw_consname i' (l' - i')
    in str @@ base ^ "." ^ consname ^ generic in
  let pp_casetag ref =
    (* DIRTY *)
    let raw_name = string_of_ppcmds @@ pp_global Cons ref
    in try let i = succ @@ String.index raw_name '.'
           in str @@ String.sub raw_name i @@ (String.length raw_name) - i
       with Not_found -> str raw_name in
  let mkvar  i   = "var" ^ Pervasives.string_of_int i in
  let return i r = (succ i,(mkvar i, r)) in
  let wrap l r (k,(n,out)) = (k,(n, str l ++ out ++ str r)) in
  let rec pp_expr' k env maybetyp =
    let mock' msg = return k @@ pp_type vars (Option.default (assert false) maybetyp) ++ (str @@ " " ^ (mkvar k) ^ " = null; /* not implemented yet" ^ (if String.length msg < 1 then "" else ": " ^ msg) ^ " */\n") in
    function
    (* I use here my own names for some expressions instead of given ids;
      make sure that all such ids aren't used (in my cases there were only relative variables). *)
    | MLrel    i             ->
      let debug = mt () (* str ("/* " ^ Pervasives.string_of_int (pred i) ^ " / ") ++ pp_list' "; " str env ++ str " */ " *) in
      let name =
        try List.nth env (pred i)
        with Failure "nth" ->
          "FAIL_" ^ Pervasives.string_of_int i ^
           "_of_" ^ Pervasives.string_of_int (List.length env)
      in (k,(name, debug (*mt ()*))) 
    | MLapp   (f,args)       ->
      let restyp = Option.default ((*assert false*)Tvar 1) maybetyp in
      (match f with
       | MLglob ref ->
         let step (k',acc) arg = let res = pp_expr' k' env None arg in (fst res,(snd res)::acc) in
         let (k'',args')  = List.fold_left step (k,[]) args in
         let      args''  = List.rev     args'  in
         let names        = List.map fst args'' in
         let output       = pp_list "" @@ List.map snd args'' in
         let call         =
           str "final " ++ pp_type vars restyp ++ str (" " ^ mkvar k'' ^ " = ") ++
           pp_global Term ref ++
             str (".apply") ++ (pp_wrap_a @@ pp_list' ", " str names) ++ str ";\n"
         in return k'' @@ output ++ call
       | _ -> (* TODO *)
         let (k1,(fname,fcode)) = pp_expr' k env None f in
         let step (k',acc) arg = let res = pp_expr' k' env None arg in (fst res,(snd res)::acc) in
         let (k2,args') = List.fold_left step (k1,[]) args in
         let     args'' = List.rev     args'  in
         let names      = List.map fst args'' in
         let output     = pp_list "" @@ fcode :: (List.map snd args'') in
         let call       =
           str "final " ++ pp_type vars restyp ++ str (" " ^ mkvar k2 ^ " = ") ++
           str fname ++
             (pp_list' "" str @@ List.map (fun name -> ".apply(" ^ name ^ ")") names) ++ str ";\n"
         in return k2 @@ output ++ call
       )
    | MLlam (_,term)       ->
      (* TODO: problems with new type-variables: java can't express them *)
      let rec work = function
        | Some (Tarr (l,r) as arrow) ->
          let arrow' = pp_type vars arrow in
          let (k',arg) = (succ k, mkvar k) in
          let (k2,(name,code)) = pp_expr' k' (arg::env) None term
          in return k2 @@ str "final " ++ arrow' ++ str (" " ^ mkvar k2 ^ " = new ") ++
            (pp_class (arrow' ++ str "()") @@
               str "@Override\n" ++
               (pp_method true "public" (r,vars) "apply" ([l],[arg]) @@
                  code ++ (str @@ "return " ^ name ^ ";"))) ++ str ";"
        | Some (Tmeta m) -> work m.contents (* TODO: need I map with vars like in pp_type? *)
        | Some _ -> mock' "strange lambda type"
        | None -> mock' "no type of lambda"
       in work maybetyp
    | MLletin (_,t1,t2)      ->
      let (k',(name1,output1)) = pp_expr' k env None t1 in
      let env' = name1::env in
      let (k'',(name2,output2)) = pp_expr' k' env' (* TODO after debug: maybetyp *) None t2
      in (k'',(name2,output1 ++ output2))
    | MLglob   ref           -> return k @@ str "final " ++ pp_type vars (Option.default ((*assert false*)Tvar 2) maybetyp) ++ (str @@ " " ^ (mkvar k) ^ " = ") ++ pp_global Term ref ++ str ".lambda();\n"
    | MLcons  (typ,ref,args) ->
      let step (k',acc) arg = let res = pp_expr' k' env None arg in (fst res,(snd res)::acc) in
      let (k'',args')  = List.fold_left step (k,[]) args in
      let      args''  = List.rev     args'  in
      let names        = List.map fst args'' in
      let output       = pp_list "" @@ List.map snd args'' in
      let call         =
        str "final " ++ pp_type vars typ ++ str (" " ^ mkvar k'' ^ " = ") ++
        str "new " ++ pp_consname typ ref ++
          str ("(") ++ pp_list' ", " str names ++ str ");\n"
      in return k'' @@ output ++ call
    | MLtuple (terms)        -> mock' "MLtuple" (* assert (args=[]); *)
    | MLcase  (typ,term,brs) ->
      (* Other way (maybe better) is to generate eliminators *)
      let restyp = Option.default ((*assert false*)Tvar 3) maybetyp in
      let (k1,resvar) = (succ k, mkvar k) in
      let (k2,(name,output)) = pp_expr' k1 env None term in
      let case (k,output) = function
        | (ids,Pusual ref,term) ->
          let (k' ,casted) = (succ k, mkvar k) in
          let env' = List.fold_left (fun acc i -> (casted ^ ".field" ^ Pervasives.string_of_int i)::acc) env @@ List.mapi (fun i _ -> i) ids in
          let (k'',(name',output')) = pp_expr' k' env' None term in
          let castedtyp = pp_consname typ ref in
          let body = str "final " ++ castedtyp ++ str (" " ^ casted ^ " = ((") ++ castedtyp ++ str(")" ^ name ^ ");\n") ++ output' ++ str (resvar ^ " = " ^ name' ^ ";\n")
          in (k'', output ++ (pp_class (str "case " ++ pp_casetag ref ++ str ":") @@ body ++ str "break;") ++ str "\n")
        | (ids,Pcons (ref,ps),term) -> assert false
        | (ids,Ptuple (ps),term) -> assert false
        | (ids,Prel i,term) -> assert false
        | (ids,Pwild,term) ->
          let (k',(name',output')) = pp_expr' k env None term
          in (k', output' ++ (pp_class (str "default:") @@ str (resvar ^ " = " ^ name' ^ ";\n")))
      in
      let (k3,cases_raw) = List.fold_left case (k2,mt ()) @@ Array.to_list brs in
      let cases = str @@ let t = string_of_ppcmds cases_raw in String.sub t 0 @@ pred @@ String.length t (* DIRTY *) in
      let switch = output ++ pp_type vars restyp ++ str ((* TODO *) " " ^ resvar ^ " = null;\n") ++ pp_class (str "switch (((" ++ pp_type vars typ ++ str (")" ^ name ^ ").tag)")) cases ++ str "\n" 
      in (succ k3,(resvar,switch))
      (* is_custom_match brs; not (is_regular_match brs) ; if ids <> [] then named_lams (List.rev ids) e ; else dummy_lams (ast_lift 1 e) 1 ; find_custom_match brs *)
    | MLtyped (term,typ)     ->
      (match maybetyp with
       | Some typ' -> pp_expr' k env (Some typ') term
       | None -> pp_expr' k env (Some typ) term)
    | MLfix   (i,ids,defs)   -> mock' "MLfix" (* push_vars (List.rev (Array.to_list ids)) env *)
    | MLexn    s             -> mock' "MLexn"
    | MLdummy                -> mock' "MLdummy"
    | MLmagic  a             -> mock' "MLmagic"
    | MLaxiom                -> mock' "MLaxiom"
  in snd @@ pp_expr' 0 env (Some typ) term

(* Pretty-printing of inductive types *)

let pp_tags constructors =
  str "public Tag tag;\n" ++
  (pp_enum "Tag" @@ List.map (fun (r,_) -> pp_global Cons r) constructors)

let pp_constructor_field (i,typ) = str "public final " ++ typ () ++ str " field" ++ i ++ str ";\n"

let pp_constructor_args types = pp_list' ", " (fun (i,typ) -> typ () ++ str " arg" ++ i) types

let pp_constructor_class vars father suffix (ref,types) =
  let types  = List.mapi (fun i typ -> (str @@ Pervasives.string_of_int i, (fun _ -> pp_type vars typ))) types in
  let fields = List.mapi (fun i _ -> "field" ^ Pervasives.string_of_int i) types in
  let name   = pp_global Cons ref
  in  pp_class (str "public static final class " ++ name ++ suffix ++ str " extends " ++ father ++ suffix) @@
    prlist_strict pp_constructor_field types ++
    str "public " ++ name ++ str "(" ++ pp_constructor_args types ++ str ") " ++
    (pp_wrap_b_nl @@
      (prlist_strict (fun (i,_) -> str "field" ++ i ++ str " = arg" ++ i ++ str ";\n") types) ++
      str "tag = Tag." ++ name ++ str ";") ++
    (str ("\n@Override\n" ^ "public String toString()") ++
     (pp_wrap_b_nl @@ str "return \"" ++ name ++ str "\"" ++
           (pp_list' "" (fun field -> str @@ " + \" \" + " ^ field ^ ".toString()") fields) ++ str ";"))

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

let pp_function ref def typ =
  if is_inline_custom ref
    then mt ()
    else match typ with
         | Tarr (l,r) as arrow ->
           if is_custom ref
             then assert false
             else let fname           = pp_global Term ref in
                  let (args,raw_term) = collect_lams def in
                  let (types,typ) = unfold_arrows_n (List.length args) arrow in
                  let term = match raw_term with
                    | MLtyped (term',typ') -> term'
                    | _ -> raw_term in
                  let  vars       = List.map mktvar @@ range 1 @@ count_variables' @@ typ::types in
                  let  names      = List.mapi (fun i _ -> "arg" ^ Pervasives.string_of_int i) types in
                  let
                    rec pp_lambda_return x = str "return " ++ pp_lambda_object x
                    and pp_lambda_object = function
                      | (_,[]) -> fname ++ str ".apply" ++ (pp_wrap_a @@ pp_list' ", " str names) ++ str ";"
                      | (Tarr _ as arrow, names) ->
                        str "new " ++ pp_type vars arrow ++ (
                          pp_class (str "()") @@ pp_lambda_method (arrow,names)) ++ str ";"
                      | _ -> assert false
                    and pp_lambda_method = function
                      | (Tarr (l,r),name::rest) ->
                        str "@Override\n" ++
                        (pp_method true "public" (r,vars) "apply" ([l],[name]) @@
                          str "return " ++ pp_lambda_object (r,rest))
                      | _ -> assert false in
                  let (res,code) = pp_expr (List.rev names) (typ,vars) term
                  in pp_class (str "public static class " ++ fname) @@
                     (pp_method false "public static" (typ,vars) "apply" (types,names) @@
                       code ++ str "return (" ++ pp_type vars typ ++ str (")" ^ res ^ ";")) ++ str "\n" ++
                     (pp_method false "public static" (arrow,vars) "lambda" ([],[]) @@
                       pp_lambda_return (arrow,names))
         | _ ->
           if is_custom ref
           then assert false
             else let vars = List.map mktvar @@ range 1 @@ count_variables typ in
                  let typname = pp_type vars typ in
                  let fname = pp_global Term ref in
                  let initname = fname ++ str "_init" in
                  let (res,code) = pp_expr [] (typ,vars) @@ def
                  in str "public static " ++ typname ++ str " " ++ fname ++ str " = " ++ initname ++ str ".create();\n" ++
                     (pp_class (str "public static class " ++ initname) @@
                       (pp_method false "public static" (typ,vars) "create" ([],[]) @@
                         code ++ str "return (" ++ pp_type vars typ ++ str (")" ^ res ^ ";")))

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
