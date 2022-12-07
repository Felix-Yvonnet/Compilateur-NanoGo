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
  | PEconstant c -> begin
    match c with
      | Cbool b -> TEconstant c, Tbool, false
      | Cint i -> TEconstant c, Tint, false
      | Cstring s -> TEconstant c, Tstring, false
    end
  | PEbinop (op, e1, e2) ->
    let e, ty, rt = e1.pexpr_desc and e3, ty2, rt2 = e2.pexpr_desc in
    if rt || rt2 then
      error 


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

let rec type_type = function
  | PTident {id;loc} when Hashtbl.mem structure id -> Tstruct (Hashtbl.find structure id)
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | PTident {id;loc} -> error loc (sprintf "Structure %s not defined" id)

let rec type_type_struct = function
  | PDstruct { ps_name   = {id = name; loc = pos}; ps_fields = pfl; } -> 
    let hash_type: (string, field) Hashtbl.t = Hashtbl.create 0 in
    let _ = List.map (fun x -> match x with ({id;loc},ptype) -> Hashtbl.add hash_type id {f_name = id; f_typ = (type_type ptype); f_ofs = 0}) pfl in 
    TDstruct { s_name = name; s_fields = hash_type; s_size = Hashtbl.length hash_type; }
  | _ -> error dummy_loc "Bad type"

let rec pf_typ_to_string = function
  | PTident { id } ->  id
  | PTptr t2 -> "*" ^ pf_typ_to_string t2

let rec tf_typ_to_string = function
| Tint -> "int"
| Tbool -> "bool"
| Tstring -> "string"
| Tstruct structure -> structure.s_name
| Tptr typ -> "*" ^ tf_typ_to_string typ
| Twild -> "unit"
| Tmany typl -> String.concat ", " (List.map tf_typ_to_string typl)

let rec type_type_func = function
  | PDfunction {pf_name;pf_params;pf_typ;pf_body;} -> 
    let e, rt = expr Context.create pf_body in
    if not rt then
      error pf_name.loc (sprintf "Missing return status in %s" pf_name.id);
    let fn_typ = List.map (fun x -> type_type x) pf_typ in
    if not (eq_type e.expr_typ (Tmany fn_typ)) then
      error pf_name.loc (sprintf "Wrong return type in %s, expected %s got %s" pf_name.id (String.concat ", " (List.map (fun x -> pf_typ_to_string x) pf_typ)) (tf_typ_to_string e.expr_typ));
    TDfunction ({fn_name = pf_name.id; fn_params = List.map (fun x -> let y,z = x in new_var y.id y.loc (type_type z)) pf_params; fn_typ = fn_typ}, e)
  | _ -> error dummy_loc "Bad function"


(* 1. declare structures *)
let phase1 = function
  | PDstruct { ps_name = { id; loc } } ->
    if Hashtbl.mem structure id then 
      error loc (sprintf "Structure %s already defined" id); 
    Hashtbl.add structure id { s_name = id; s_fields = Hashtbl.create 10; s_size = 0 }

  | PDfunction _ -> ()

  (* 2. declare functions and type fields *)

let rec from_ptyp_to_id = function
  | PTident { id } ->  id
  | PTptr t2 -> from_ptyp_to_id t2

let rec well_defined_type ptype = let id = from_ptyp_to_id ptype in
  id = "bool" || id = "int" || id = "string" || Hashtbl.mem structure id

let is_repeat valu rest = match valu with
  | {id;loc}, ptype -> List.mem id rest, loc, ptype, id

let rec well_defined_struct_list = function
  | [] -> true, true, dummy_loc, "", []
  | t::q -> let is_good, no_repeat, loc, id, id_list = well_defined_struct_list q in
    let b, pos, ptype, name = is_repeat t id_list in
    let b2 = well_defined_type ptype in
    if not b2 && not b then
        false, no_repeat, pos, from_ptyp_to_id ptype, []
    else (
      if b then
        is_good, false, pos, name, []
      else
      is_good, no_repeat, loc, id, name::id_list
      )
    
let phase2 = function
  (* vérifier la présence de la fonction main *)
  | PDfunction { pf_name={id="main"; loc}; pf_params=[]; pf_typ=[]; } -> if !found_main then
    error loc (sprintf "Function main already defined");
  Hashtbl.add funct "main" { fn_name = "main"; fn_params = []; fn_typ = []; }; found_main:=true

  (* gère les fonctions en général *)
  | PDfunction { pf_name={id; loc}; pf_params = pfp; pf_typ = pft; } -> 
  if Hashtbl.mem funct id then
    error loc (sprintf "Function %s already defined" id);
  let is_good, no_repeat, pos, name, _ = well_defined_struct_list pfp and b2 = List.mem false (List.map (fun x -> well_defined_type x) pft) in 
  if not is_good then
    error pos (sprintf "In function %s, type %s not well defined" id name);
  if not no_repeat then
    error pos (sprintf "In function %s, input type %s appears multiple times" id name);
  if b2 then 
    error loc (sprintf "In function %s, output type %s not well defined" id (from_ptyp_to_id (List.find (fun x -> not (well_defined_type x)) pft)));
  Hashtbl.add funct id { fn_name = id; fn_params = []; fn_typ = []; }

  (* gère les structures *)
  | PDstruct { ps_name = { id; loc }; ps_fields =  pfield_list } -> 
    let is_good, no_repeat, pos, name, _ = well_defined_struct_list pfield_list in 
    if not no_repeat then
      error loc (sprintf "In %s structure, %s already defined" id name);
    if not is_good then
      error pos (sprintf "In structure %s, type %s not well defined" id name);
    let stru = type_type_struct (PDstruct { ps_name = { id; loc }; ps_fields =  pfield_list }) in
      Hashtbl.remove structure id;
      (match stru with | TDstruct s -> Hashtbl.add structure id s)
      (* j'ai pas trouvé comment faire propre... *)
 
  | _ -> error dummy_loc "Unbound struct/funct/whatever you want"


(* 3. type check function bodies *)
let sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | _ -> (* TODO *) assert false 

let phase3 = function
  | PDfunction { pf_name = { id; loc }; pf_params = pf_params; pf_body = e; pf_typ = tyl } ->
    type_type_func (PDfunction { pf_name = { id; loc }; pf_params = pf_params; pf_body = e; pf_typ = tyl })
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
