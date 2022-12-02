open Format
open Lib
open Ast
open Tast

exception Error of Ast.location * string
exception Anomaly of string

let error loc e = raise (Error (loc, e))

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

let new_var =
  let id = ref 0 in
  fun x loc ?(used=false) ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty; v_used = used; v_addr = 0; v_depth = 0 }

(* M key String / val Tast.var *)
module Context = struct
  module M = Map.Make(String)
  type t = var M.t
  let create = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env

  let all_vars = ref []
  let check_unused () =
    let check v =
      if v.v_name <> "_" && (* TODO used *) true then error v.v_loc "unused variable" in
    List.iter check !all_vars


  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    add env v, v

  (* TODO type () et vecteur de types *)
end

(* Variables globales du projet *)
let fmt_imported = ref false
let fmt_used = ref false
let found_main = ref false

let structure: (string, structure) Hashtbl.t = Hashtbl.create 10

(* TODO environnement pour les fonctions *)

let funct: (string, function_) Hashtbl.t = Hashtbl.create 10

let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | _ -> error dummy_loc ("unknown struct ") (* TODO type structure *)

let rec type_type_struct = function
  | PDstruct { ps_name   = {id = name; loc = pos}; ps_fields = pfl; } -> let hash_type: (string, field) Hashtbl.t = Hashtbl.create 0 in
  let _ = List.map (fun x -> match x with ({id;loc},ptype) -> Hashtbl.add hash_type id {f_name = id; f_typ = (type_type ptype); f_ofs = 0}) pfl in 
  { s_name = name; s_fields = hash_type; s_size = Hashtbl.length hash_type; }
  | _ -> error dummy_loc "Bad type"

let rec eq_type ty1 ty2 = match ty1, ty2 with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | _ -> false
(* TODO autres types *)

let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let tvoid = Tmany []
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid

let rec expr env e =
  let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  { expr_desc = e; expr_typ = ty }, rt

and expr_desc env loc = function
  | PEskip ->
    TEskip, tvoid, false
  | PEconstant c ->
    (* TODO *) TEconstant c, tvoid, false
  | PEbinop (op, e1, e2) ->
    (* TODO *) assert false
  | PEunop (Uamp, e1) ->
    (* TODO *) assert false
  | PEunop (Uneg | Unot | Ustar as op, e1) ->
    (* TODO *) assert false
  | PEcall ({id = "fmt.Print"}, el) ->
    (* TODO *) TEprint [], tvoid, false
  | PEcall ({id="new"}, [{pexpr_desc=PEident {id}}]) ->
    let ty = match id with
      | "int" -> Tint | "bool" -> Tbool | "string" -> Tstring
      | _ -> (* TODO *) error loc ("no such type " ^ id) in
    TEnew ty, Tptr ty, false
  | PEcall ({id="new"}, _) ->
    error loc "new expects a type"
  | PEcall (id, el) ->
    (* TODO *) assert false
  | PEfor (e, b) ->
    (* TODO *) assert false
  | PEif (e1, e2, e3) ->
    (* TODO *) assert false
  | PEnil ->
    (* TODO *) assert false
  | PEident {id=id} ->
    (* TODO *) (try let v = Context.find id env in TEident v, v.v_typ, false
                with Not_found -> error loc ("unbound variable " ^ id))
  | PEdot (e, id) ->
    (* TODO *) assert false
  | PEassign (lvl, el) ->
    (* TODO *) TEassign ([], []), tvoid, false 
  | PEreturn el ->
    (* TODO *) TEreturn [], tvoid, true
  | PEblock el ->
    (* TODO *) TEblock [], tvoid, false
  | PEincdec (e, op) ->
    (* TODO *) assert false
  | PEvars _ ->
    (* TODO *) assert false 


(* 1. declare structures *)
let phase1 = function
  | PDstruct { ps_name = { id; loc } } ->
    if Hashtbl.mem structure id then 
      error loc (sprintf "Structure %s already defined" id); 
    Hashtbl.add structure id { s_name = id; s_fields = Hashtbl.create 10; s_size = 0 }

  | PDfunction _ -> ()

let rec well_defined_struct = function
  | PTident {id;loc} -> Hashtbl.mem structure id || id = "bool" || id = "int" || id = "string" 
  | PTptr t2 -> well_defined_struct t2

let is_repeat valu rest = match valu with
  | {id;loc}, ptype -> List.mem valu rest, id, loc,ptype

let rec well_defined_struct_list = function
  | [] -> true, dummy_loc, ""
  | t::q -> let b, name, pos, ptype = is_repeat t q in if not (well_defined_struct ptype) || b then
        false, pos, name
    else
      well_defined_struct_list q
    
(* 2. declare functions and type fields *)
let phase2 = function
  (* vérifier la présence de la fonction main *)
  | PDfunction { pf_name={id="main"; loc}; pf_params=[]; pf_typ=[]; } -> if !found_main then
    error loc (sprintf "Function main already defined");
  Hashtbl.add funct "main" { fn_name = "main"; fn_params = []; fn_typ = []; }; found_main:=true
  (* gère les fonctions en général *)
  | PDfunction { pf_name={id; loc}; pf_body = pfb; pf_params = pfp; pf_typ = pft; } -> if Hashtbl.mem funct id then 
    error loc (sprintf "Function %s already defined" id);
  Hashtbl.add funct id (type_type_func { pf_name={id; loc}; pf_body = pfb; pf_params = pfp; pf_typ = pft; })

  (* gère les structures *)
  | PDstruct { ps_name = { id; loc }; ps_fields =  pfield_list } -> let b, pos, name = well_defined_struct_list pfield_list in 
  if not b then
    error loc (sprintf "In %s structure, %s already defined" id name);
  let stru = type_type_struct (PDstruct { ps_name = { id; loc }; ps_fields =  pfield_list }) in
    Hashtbl.remove structure id;
      Hashtbl.add structure id stru
      (* j'ai pas trouvé comment faire propre... *)
 
  | _ -> error dummy_loc "Unbound struct/funct/whatever you want"


(* 3. type check function bodies *)
let sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | _ -> (* TODO *) assert false 

let phase3 = function
  | PDfunction { pf_name={id; loc}; pf_body = e; pf_typ=tyl } ->
    (* TODO check name and type *) 
    let f = { fn_name = id; fn_params = []; fn_typ = []} in
    let e, rt = expr Context.create e in
    TDfunction (f, e)
  | PDstruct {ps_name={id}} ->
    (* TODO *) let s = { s_name = id; s_fields = Hashtbl.create 5; s_size = 0 } in
    TDstruct s

let file (imp, dl) =
  (* fmt_imported := imp; *)
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "Missing method main";
  let dl = List.map phase3 dl in
  Context.check_unused (); (* TODO variables non utilisees *)
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl
