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

let rec pf_typ_to_string = function
  | PTident { id } ->  id
  | PTptr t2 -> "*" ^ pf_typ_to_string t2

let rec pf_list_to_string = function
  | [] -> "nil"
  | pf_typ -> String.concat ", " (List.map (fun x -> pf_typ_to_string x) pf_typ)

let rec tf_typ_to_string = function
| Tint -> "int"
| Tbool -> "bool"
| Tstring -> "string"
| Tstruct structure -> structure.s_name
| Tptr typ -> "*" ^ tf_typ_to_string typ
| Twild -> "nil"
| Tmany [] -> "nil"
| Tmany typl -> String.concat ", " (List.map tf_typ_to_string typl)

let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let tvoid = Tmany []
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid


let is_l_value env id =  try (Context.find id env; true) with Not_found -> false



let rec expr env e =
  let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  { expr_desc = e; expr_typ = ty }, rt

and handle env e =  let e,_ = expr env e in e

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
    let loc1, loc2 = e1.pexpr_loc, e2.pexpr_loc in
    let e1, _ = expr env e1 and e2,_ = expr env e2 in
    let t1,t2 = e1.expr_typ, e2.expr_typ in
    if not (eq_type t1 t2) then 
      error loc2 (sprintf "Comparison between different types not supported, got %s and %s" (tf_typ_to_string t1) (tf_typ_to_string t2));
    begin
    match op with
      |Beq| Bne ->
        if e1.expr_desc = TEnil && e2.expr_desc = TEnil then 
          error loc1 "Both side of the test are nil";
        TEbinop(op, e1, e2), Tbool, false
      | Badd| Bsub | Bmul | Bdiv | Bmod ->
        if not (eq_type t1 Tint) then
          error loc1 (sprintf " Invalid type for operation, expected integer got %s" (tf_typ_to_string t1));
        TEbinop(op, e1, e2), Tint, false
      | Blt | Ble | Bgt | Bge ->
        if not (eq_type t1 Tint) then
          error loc1 (sprintf " Invalid type for operation, expected integer got %s" (tf_typ_to_string t1));
        TEbinop(op,e1, e2), Tbool, false
      | Band | Bor ->
        if not (eq_type t1 Tbool) then
          error loc1 (sprintf " Invalid type for operation, expected bool got %s" (tf_typ_to_string t1));
        TEbinop(op,e1,e2), Tbool, false
    end

  | PEunop (Uamp, e1) -> 
    let loc = e1.pexpr_loc in
    let e1,_ = expr env e1 in
    let value = match e1.expr_desc with | TEident {v_name} ->  is_l_value env v_name | _ -> false in
    if not value then
      error loc "J'vais t'faire courir moi tu vas voir rouquin + ratio + pas l-value + pas évalué";
    TEunop(Uamp, e1), Tptr e1.expr_typ, false

  | PEunop (Uneg, e1) ->
    let loc = e1.pexpr_loc in
    let e1,_ = expr env e1 in
    if not (eq_type e1.expr_typ Tint) then
      error loc (sprintf "Expected int but got %s" (tf_typ_to_string e1.expr_typ));
    TEunop(Uneg,e1), Tint, false

  | PEunop (Unot, e1) ->
    let loc = e1.pexpr_loc in
    let e1,_ = expr env e1 in
    if not (eq_type e1.expr_typ Tbool) then
      error loc (sprintf "Expected bool but got %s" (tf_typ_to_string e1.expr_typ));
    TEunop(Unot,e1), Tbool, false

  | PEunop (Ustar, e1) ->
    let loc = e1.pexpr_loc in
    let e1,_ = expr env e1 in
    if e1.expr_desc = TEnil then
      error loc "Ah bha c'est bien nil, bravo pour l'appareil photo !";
    let ty = 
    match e1.expr_typ with
      | Tptr t -> t
      | typ -> error loc (sprintf "Expected pointers but got %s" (tf_typ_to_string typ))
    in
      TEunop(Ustar,e1), ty, false

  | PEcall ({id = "fmt.Print"}, el) -> fmt_used := true;
    let loc = (List.hd el).pexpr_loc in
    let l = List.map (handle env) el in 
    (match l with 
      | [{expr_desc = TEcall _}] -> let e = List.hd l in 
        TEprint [e], tvoid, false
      | _ -> List.iter (function |{expr_typ = Tmany _} -> error loc "Function call as part of a plotting are not supported" | _ -> ()) l;
        TEprint l, tvoid, false)

  | PEcall ({id="new"}, [{pexpr_desc=PEident {id;loc}}]) ->
    let ty = match id with
      | "int" -> Tint | "bool" -> Tbool | "string" -> Tstring
      | _ -> if not (Hashtbl.mem structure id) then 
          error loc (sprintf "Undefined type %s" id);
        Tstruct (Hashtbl.find structure id) 
    in
    TEnew ty, Tptr ty, false

  | PEcall ({id="new";loc}, _) ->
    error loc "new expects a type"

  | PEcall ({id;loc}, el) ->
      if not (Hashtbl.mem funct id) then 
      error loc (sprintf "Unknown function %s" id);
    let el = List.map (handle env) el in
    let f = Hashtbl.find funct id in
    (match el with
      | [{expr_desc = TEcall (g,el2)}] when List.length f.fn_params > 1 ->
        if List.length g.fn_typ != List.length f.fn_params then 
          error loc (sprintf "Output size of %s (%d) is not matching %s input size (%d)" g.fn_name (List.length el2) id (List.length el));
        let typlid = List.map (fun x -> x.v_typ) (Hashtbl.find funct id).fn_params in
        List.iter2 (fun typ1 typ -> if not (eq_type typ1 typ) then
              error loc (sprintf "Function %s expects type %s but got type %s" id (tf_typ_to_string (Tmany typlid)) (tf_typ_to_string (Tmany g.fn_typ)));
        ) typlid g.fn_typ; 
        TEcall (f,el), Tmany f.fn_typ, false
      
      | el -> List.iter (function |{expr_typ = Tmany _} -> error loc "Function call as part of a plotting are not supported" | _ -> ()) el;
        if List.length f.fn_typ = 1 then
          TEcall (f,el), List.hd f.fn_typ, false
        else
          TEcall (f,el), Tmany f.fn_typ, false)
    
  | PEfor (e, b) ->
    let e,_ = expr env e and b,rt = expr env b in
    if not( eq_type e.expr_typ Tbool) then
      error loc (sprintf "Expected boolean condition in the loop, got %s" (tf_typ_to_string e.expr_typ));
    TEfor(e,b), b.expr_typ, rt

  | PEif (e1, e2, e3) ->
    let loc = e1.pexpr_loc in
    let e1,_ = expr env e1 and e2,rt2 = expr env e2 and e3,rt3 = expr env e3 in
    if not (eq_type e1.expr_typ Tbool) then
      error loc (sprintf "Expected boolean condition, got %s" (tf_typ_to_string e1.expr_typ));
    let typ = if rt2 && rt3 then (
      if not (eq_type e2.expr_typ e3.expr_typ) then
        error loc (sprintf "Return types are not compatible, got %s and %s" (tf_typ_to_string e2.expr_typ) (tf_typ_to_string e3.expr_typ));
      e2.expr_typ) else tvoid in
    TEif(e1,e2,e3), typ, rt2 && rt3
    
  | PEnil ->
    TEnil, Tptr (Twild), false
  | PEident {id;loc} ->
    if id = "_" then
      error loc ("the _ variable is not to be used");
    (try let v = Context.find id env in TEident v, v.v_typ, false
      with Not_found -> error loc ("unbound variable " ^ id))
  | PEdot (e, id) ->
    (* TODO *) assert false
  | PEassign (lvl, el) ->
    if List.length el <> List.length lvl then
      error loc (sprintf "Expected same size affectation got %d and %d" (List.length lvl) (List.length el));
    let lvl = List.map (handle env) lvl and el = List.map (handle env) el in
    let err x y = if not (eq_type x.expr_typ y.expr_typ) then error loc "Expected same type affectation" in
    List.iter2 err lvl el;
    TEassign (lvl, el), tvoid, false 

  | PEreturn el ->
    (* TODO *) TEreturn [], tvoid, true
  | PEblock el ->
    (* TODO *) TEblock [], tvoid, true
  | PEincdec (e, op) ->
    let loc = e.pexpr_loc in
    let e,_ = expr env e in
    if not (eq_type e.expr_typ Tint) then
      error loc (sprintf "Expected int, got %s" (tf_typ_to_string e.expr_typ));
    TEincdec (e,op), Tint, false
    

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

let rec type_type_func = function
  | PDfunction {pf_name;pf_params;pf_typ;pf_body;} -> 
    let e, rt = expr Context.create pf_body in
    let fn_typ = List.map (fun x -> type_type x) pf_typ in
    if List.length fn_typ = 0 && (not rt || (eq_type e.expr_typ (Tmany[]))) then 
      TDfunction ({fn_name = pf_name.id; fn_params = List.map (fun x -> let y,z = x in new_var y.id y.loc (type_type z)) pf_params; fn_typ = fn_typ}, e)
    else begin
    if not rt then
      error pf_name.loc (sprintf "Missing return status in %s" pf_name.id);
    if not (eq_type e.expr_typ (Tmany fn_typ)) then
      error pf_name.loc (sprintf "Wrong return type in %s, expected %s got %s" pf_name.id (pf_list_to_string pf_typ) (tf_typ_to_string e.expr_typ));
    TDfunction ({fn_name = pf_name.id; fn_params = List.map (fun x -> let y,z = x in new_var y.id y.loc (type_type z)) pf_params; fn_typ = fn_typ}, e)
    end 
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
      (match stru with | TDstruct s -> Hashtbl.add structure id s |_ -> error dummy_loc "Not supposed to be")
      (* j'ai pas trouvé comment faire propre... *)

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
