open Pp             (* lib/pp.ml4 *)
open Util           (* lib/util.ml *)
module N = Names    (* kernel/names.ml *)
module No = Nameops (* library/nameops.ml *) 
module L = Libnames (* library/libnames.ml *)

module T = Table
open Miniml
module MU = Mlutil
module C = Common

let (!%) = Printf.sprintf
let ($) g f x = g (f x)
let p = print_endline
let slist f xs = String.concat ";" (List.map f xs)
let sarray f xs = slist f (Array.to_list xs)
let id x = x
let list_mapi f = Array.to_list $ Array.mapi f $ Array.of_list
let tryo f x = try Some (f x) with _ -> None
let string1 = String.make 1
let (|>) x f = f x
let (--) a b =
  let rec iter store a bi =
    if a = bi then bi::store
    else iter (bi::store) a (bi - 1)
  in
  if a <= b then iter [] a b
  else List.rev (iter [] b a)

(* see Scala language specification: http://www.scala-lang.org/sites/default/files/linuxsoft_archives/docu/files/ScalaReference.pdf *)
let keywords =
  List.fold_right (fun s -> N.Idset.add (N.id_of_string s))
  [ "abstract"; "do"; "finally"; "import"; "object"; "return"; "trait"; "var"; 
    "_"; "case"; "else"; "for"; "lazy"; "override"; "sealed"; "try"; "while";
    "catch"; "extends"; "forSome"; "match"; "package"; "super"; "true"; "with";
    "class"; "false"; "if"; "new"; "private"; "this"; "type"; "yield"; "def";
    "final"; "implicit"; "null"; "protected"; "throw"; "val"; ]
  N.Idset.empty

let preamble mod_name used_modules usf = str ""

let prarray_with_sep pp f xs = prlist_with_sep pp f (Array.to_list xs)
let prlist_with_comma f xs = prlist_with_sep (fun () -> str ", ") f xs
let prlist_with_space f xs = prlist_with_sep (fun () -> str " ") f xs

let pp_global k r =
  if T.is_inline_custom r then str (T.find_custom r)
  else str (Common.pp_global k r)

let pr_id id =
  let s = N.string_of_id id in
  let ss = List.map (function | "\'" -> "$prime" | c -> c) (explode s) in
  str (String.concat "" ss)

let free_type_vars typ =
  let module S = Set.Make(struct type t = int let compare = compare end) in
  let rec iter = function
    | Tmeta _ | Tvar' _ -> S.empty
    | Tvar (i:int) ->  S.singleton i
    | Tglob ((r: L.global_reference), (l: ml_type list)) ->
	List.fold_left (fun store typ ->
	  S.union store (iter typ)) S.empty l
    | Tarr (t1,t2) ->
	S.union (iter t1) (iter t2)
    | Tdummy _
    | Tunknown
    | Taxiom -> S.empty
  in
  S.elements (iter typ)

let name_of_tvar i =
  "T" ^ string_of_int i

let name_of_tvar' i =
  if 1 <= i && i <= 26 then
    string1 (char_of_int (int_of_char 'A' + i - 1))
  else
    "A" ^ string_of_int i

let rec pp_type (tvs:N.identifier list) = function
    | Tmeta m -> begin match m.contents with
      | Some t -> pp_type tvs t
      | None -> str "MetaNone"
    end
    | Tvar' i -> str (name_of_tvar' i)
    | Tvar i ->
	begin match tryo (List.nth tvs) (i-1) with
	| Some v -> pr_id v
(*	| None -> str (name_of_tvar2 i)*)
        | None -> str "Any"
	end
    | Tglob ((r: L.global_reference), (l: ml_type list)) ->
	pp_global C.Type r
	  ++ if l = [] then mt ()
	     else str "[" ++ prlist_with_comma (pp_type tvs) l ++ str "]"
    | Tarr (t1,t2) ->
	str "(" ++ pp_type tvs t1 ++ str " => " ++ pp_type tvs t2 ++ str")"
    | Tdummy _ -> str "Unit"
    | Tunknown -> str "Any"
    | Taxiom -> str "Unit // AXIOM TO BE REALIZED" ++ Pp.fnl()

let rec pp_expr (tvs: N.identifier list) (env: C.env) : ml_ast -> 'a =
  function
    | MLrel (i, ts) ->
	let id = C.get_db_name i env in
        let type_annot = if ts = [] then mt()
            else str "[" ++ prlist_with_comma (pp_type tvs) ts ++ str "]"
        in
	pr_id id ++ type_annot
    | MLapp ((f: ml_ast), (args: ml_ast list)) ->
	pp_expr tvs env f ++ str "("
	  ++ prlist_with_sep (fun () -> str ")(") (pp_expr tvs env) args ++ str ")"
    | MLlam (_, _, _) as a ->
      	let fl,a' = MU.collect_lams' a in
        let (ids,tys) = List.split fl in
	let ids',env' = C.push_vars (List.map MU.id_of_mlid ids) env in
        let fl' = List.combine ids' tys in
        let pp_arg (id,ty) = str "(" ++ pr_id id ++ str ":"
            ++ pp_type tvs ty ++ str ") =>"
        in
	str"{" ++ Pp.fnl()
          ++ prlist_with_space pp_arg (List.rev fl') ++ Pp.fnl()
          ++ pp_expr tvs env' a' ++ Pp.fnl()
          ++ str "}"
    | MLletin ((mlid: ml_ident), (i,mlty), (a1: ml_ast), (a2: ml_ast)) ->
	let id = MU.id_of_mlid mlid in
	let (ids', env2) = C.push_vars [id] env in
	str "{" ++ Pp.fnl()
          ++ local_def' tvs env (List.hd ids') i mlty a1 ++ Pp.fnl()
	  ++ pp_expr tvs env2 a2 ++ Pp.fnl() ++ str "}" ++ Pp.fnl()
    | MLglob (r, ty_args) ->
        let type_annot = if ty_args = [] then mt()
          else str"[" ++ prlist_with_comma (pp_type tvs) ty_args ++ str "]"
        in
        pp_global C.Term r ++ type_annot
    | MLcons ((_: ml_type), (r: L.global_reference), (args: ml_ast list)) ->
	pp_global C.Cons r ++ str "("
	  ++ prlist_with_comma (pp_expr tvs env) args ++ str ")"
    | MLtuple (ts : ml_ast list) ->
        str "(" ++ prlist_with_comma (pp_expr tvs env) ts ++ str")"
    | MLcase ((_ : ml_type), (t: ml_ast), (pv: ml_branch array))  ->
	pp_expr tvs env t ++ str " match {" ++ Pp.fnl()
	  ++ prarray_with_sep Pp.fnl (pp_case tvs env) pv
	  ++ Pp.fnl() ++ str "}"
    | MLfix ((i: int), idtys ,(defs: ml_ast array)) ->
        let ids,tys = Array.to_list idtys |> List.split in
	let ids',env' = C.push_vars (List.rev ids) env in
	let ids'' = List.rev ids' in
	let local_defs =
	  prlist_with_sep Pp.fnl id
	    (list_map3 (fun id ty def -> local_def' tvs env' id 0 ty def)
	       ids'' tys (Array.to_list defs))
	in
	let body = pr_id (List.nth ids'' i) in
	str"{" ++Pp.fnl()++ local_defs ++Pp.fnl()++ body ++ str"}" ++Pp.fnl()
    | MLexn (s: string) -> str ("throw new Exception(\"" ^s^ "\")")
    | MLdummy -> str "()"
    | MLmagic (a, ty) ->
	str "(" ++ pp_expr tvs env a ++ str ").asInstanceOf[" ++ pp_type tvs ty ++ str"]"
    | MLaxiom -> str "() // AXIOM TO BE REALIZED" ++ Pp.fnl()

  (*
    場合分けの一つのcaseについて
    patternはパターン、idsは束縛される変数名の配列、tは式
   *)
and pp_case tvs env ((ids, pattern, t): ml_branch) =
(*  let (ids, env') = C.push_vars (List.rev_map MU.id_of_mlid ids) env in*)
  let (s1, s2) = pp_one_case tvs env (ids,pattern,t) in
  str "case " ++ s1 (*++ str "(" ++
    prlist_with_comma pr_id (List.rev ids)
    ++ str ")"*) ++ str " => "
    ++ s2
and pp_one_case tvs env (ids,pattern,t) =
  let ids',env' = C.push_vars (List.rev_map MU.id_of_mlid ids) env in
  (pp_gen_pat (List.rev ids') env' pattern,
  pp_expr tvs env' t)
and pp_gen_pat ids env = function
  | Pcons (r, l) -> 
      pp_global C.Cons r ++ str "(" ++
        prlist_with_comma (pp_gen_pat ids env) l ++ str")"
  | Pusual r ->
      pp_global C.Cons r ++ str "(" ++
        prlist_with_comma (pr_id) ids ++ str")"
  | Ptuple l -> str "(" ++ prlist_with_comma (pp_gen_pat ids env) l ++ str")"
  | Pwild -> str "_"
  | Prel n -> pr_id (C.get_db_name n env)

and local_def tvs env (id: N.identifier) (def: ml_ast) =
  str "def " ++ pr_id id ++ str " = " ++ pp_expr tvs env def

and local_def' tvs env (id: N.identifier) i (ty: ml_type) (def: ml_ast) =
  let new_tvars =
    let n = List.length tvs in
    if i=0 then []
    else (n+1)--(n+i)
    |> List.map (N.id_of_string $ name_of_tvar)
  in
  let tvs' = List.rev new_tvars @ tvs in
  let pp_tvars = if new_tvars = [] then mt() else
    str "[" ++ prlist_with_comma pr_id new_tvars ++ str "]"
  in
  str "def " ++ pr_id id ++ pp_tvars ++ str ": " ++ pp_type tvs' ty
    ++ str " = " ++ pp_expr tvs' env def

let pp_def glob body typ =
  let ftvs = free_type_vars typ in
  let tvars = if ftvs = [] then mt() else
    str "[" ++ prlist_with_comma (str $ name_of_tvar') ftvs ++ str "]"
  in
  let tvs = List.map (fun i -> N.id_of_string (name_of_tvar' i)) ftvs in
  let pbody =
    if T.is_custom glob then str (T.find_custom glob)
    else pp_expr [] (C.empty_env()) body
  in
  str "def " ++ pp_global C.Term glob ++ tvars ++ str " : " ++ pp_type tvs typ
    ++ str " = " ++ pbody ++ Pp.fnl()

let pp_singleton kn packet =
  let l = packet.ip_vars in
  let l' = List.rev l in
  let params = if l = [] then mt ()
      else str "[" ++ prlist_with_comma pr_id l ++ str "]"
  in
  str "type " ++ pp_global C.Type (L.IndRef (kn, 0)) ++ params 
    ++ str " = " ++ pp_type l' (List.hd packet.ip_types.(0)) ++ fnl()

let pp_one_ind (ip: N.inductive) (tvars: N.identifier list)
    (cv: ml_type list array) =
  let tname = pp_global C.Type (L.IndRef ip) in
  let pp_tvars vs =
    if vs = [] then mt()
    else str "[" ++ prlist_with_comma pr_id vs ++ str "]"
  in
  let pp_constructor (r,typs) =
    str "case class " ++ pp_global C.Cons r ++ pp_tvars tvars ++ str "("
      ++ prlist_with_comma
        (fun (i, typ) ->
	  let vname = str "x" ++ int i in
	  vname ++ str ": " ++ pp_type tvars typ)
        (list_mapi (fun i typ -> (i+1,typ)) typs)
      ++ str ") extends " ++ tname ++ pp_tvars tvars
  in
  str "sealed abstract class " ++ tname ++ pp_tvars tvars ++ fnl()
    ++ prvect_with_sep Pp.fnl pp_constructor
      (Array.mapi (fun j typ -> (L.ConstructRef(ip,j+1), typ)) cv)
    

let pp_decl : ml_decl -> std_ppcmds = function
  | Dind (mind,i) when i.ind_kind = Singleton ->
      pp_singleton mind i.ind_packets.(0) ++ fnl ()
(*  | Dind ((kn: N.kernel_name), (ind: ml_ind)) ->*)
  | Dind ((mind: N.mutual_inductive), (ind: ml_ind)) ->
      let rec iter i =
	if i >= Array.length ind.ind_packets then mt()
	else
	  let packet = ind.ind_packets.(i) in
	  let ip = (mind,i) in
	  pp_one_ind ip packet.ip_vars packet.ip_types ++ fnl ()
	    ++ iter (i+1)
      in
      iter 0
  | Dtype ((r:L.global_reference), (l: N.identifier list), (t: ml_type)) ->
      if T.is_inline_custom r then mt()
      else
        let name = pp_global C.Type r in
	let l = C.rename_tvars keywords l in
        let ty_args, def = match tryo T.find_type_custom r with
          | Some (ids,s) -> List.map str ids, str s
          | None -> List.map pr_id l, pp_type l t
        in
        let tparams = if ty_args = [] then mt()
            else str "[" ++ prlist_with_comma id ty_args ++ str "]"
        in
        str "type " ++ name ++ tparams ++ str " = " ++ def ++ Pp.fnl()
  | Dfix ((rv: L.global_reference array), (defs: ml_ast array), (typs: ml_type array)) ->
      let max = Array.length rv in
      let rec iter i =
	if i = max then mt ()
	else
	  pp_def rv.(i) defs.(i) typs.(i) ++ iter (i+1)
      in
      iter 0
  | Dterm ((r: L.global_reference), (a: ml_ast), (t: ml_type)) ->
      if T.is_inline_custom r then mt ()
      else pp_def r a t

let rec pp_structure_elem = function
  | (l,SEdecl d) -> pp_decl d
  | (l,SEmodule m) -> pp_module_expr m.ml_mod_expr
  | (l,SEmodtype m) -> mt ()
and pp_module_expr = function
  | MEstruct (mp,sel) -> str "object CoqModule {" ++ Pp.fnl()
	++ prlist_strict pp_structure_elem sel
	++ str "}" ++ Pp.fnl()
  | MEfunctor _ -> mt ()
  | MEident _ | MEapply _ -> assert false

let pp_struct (sts: ml_structure) =
  let pp_sel (mp,sel) =
    C.push_visible mp [];
    let p =
      prlist_strict pp_structure_elem sel
    in
    C.pop_visible (); p
  in
  str "object CoqMain {" ++ Pp.fnl()
    ++ prlist_strict pp_sel sts
    ++ str "}" ++ Pp.fnl()


let descr = {
  keywords = keywords;
  file_suffix = ".scala";
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ -> mt ());
  pp_sig = (fun _ -> mt ());
  pp_decl = pp_decl;
}
