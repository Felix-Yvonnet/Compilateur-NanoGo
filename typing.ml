open Format
open Lib
open Ast
open Tast

exception Error of Ast.location * string
exception Anomaly of string

let error loc e = raise (Error (loc, e))
let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

let new_var =
  let id = ref 0 in
  fun x loc ?(used = false) ty ->
    incr id;
    {
      v_name = x;
      v_id = !id;
      v_loc = loc;
      v_typ = ty;
      v_used = used;
      v_addr = 0;
      v_depth = 0;
    }

(* M key String / val Tast.var *)
module Context = struct
  module M = Map.Make (String)

  type t = var M.t

  let create = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env
  let all_vars : (string,var) Hashtbl.t = Hashtbl.create 10

  let check_unused () =
    let check v =
      if v.v_name <> "_" && not v.v_used then
        error v.v_loc "unused variable"
    in
    Hashtbl.iter (fun id vars -> check vars) all_vars

  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    Hashtbl.add all_vars x v;
    (add env v, v)

  (* TODO type () et vecteur de types *)
end

(* Variables globales du projet *)
let fmt_imported = ref false
let fmt_used = ref false
let found_main = ref false
let func_type = ref []
let structure : (string, structure) Hashtbl.t = Hashtbl.create 10

(* TODO environnement pour les fonctions *)

let funct : (string, function_) Hashtbl.t = Hashtbl.create 10

let rec eq_type ty1 ty2 =
  match (ty1, ty2) with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | Tmany x, Tmany y -> List.mem false (List.map2 eq_type x y)
  | Twild, Twild -> true
  | _ -> false
(* TODO autres types *)

let rec pf_typ_to_string = function
  | PTident { id } -> id
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

let rec is_l_value env exp = match exp with
  | TEident var -> (try
    let _ = Context.find var.v_name env in ()
    with Not_found -> error var.v_loc (sprintf "%s is expected to be a variable" var.v_name));
    true

  | TEdot({expr_desc = (TEident v); expr_typ = typ},f) -> 
    let _ = is_l_value env (TEident v) in true
    
  | TEunop(Ustar, e) -> 
    if e.expr_desc = TEnil then false
    else begin
      let b = (match e.expr_typ with | Tptr _ -> true | _ -> false) in
      let b3 = (match e.expr_desc with | TEident {v_name = "_"} -> false | _ -> true) in
      let b2 = is_l_value env e.expr_desc in b && b2 && b3
    end 
  | _ -> false

  let rec well_defined_t typ = match typ with
  | Tint | Tbool | Tstring -> true
  | Tstruct s -> Hashtbl.mem structure s.s_name
  | Tptr s -> well_defined_t s
  | Twild -> true
  | Tmany sl -> List.fold_left (fun x y -> x && well_defined_t y) true sl

  let rec type_type = function
  | PTident { id; loc } when Hashtbl.mem structure id ->
      Tstruct (Hashtbl.find structure id)
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | PTident { id; loc } -> error loc (sprintf "Structure %s not defined" id)

let rec expr env e =
  let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  ({ expr_desc = e; expr_typ = ty }, rt)

and recure env e = fst (expr env e)

and expr_desc env loc = function
  | PEskip -> (TEskip, tvoid, false)

  | PEconstant c -> (
      match c with
      | Cbool b -> (TEconstant c, Tbool, false)
      | Cint i -> (TEconstant c, Tint, false)
      | Cstring s -> (TEconstant c, Tstring, false))

  | PEbinop (op, e1, e2) -> (
      let loc1, loc2 = (e1.pexpr_loc, e2.pexpr_loc) in
      let e1, _ = expr env e1 and e2, _ = expr env e2 in
      let t1, t2 = (e1.expr_typ, e2.expr_typ) in
      if not (eq_type t1 t2) then
        error loc2
          (sprintf
             "Operations between different types not supported, got %s and %s"
             (tf_typ_to_string t1) (tf_typ_to_string t2));
      match op with
      | Beq | Bne ->
          if e1.expr_desc = TEnil && e2.expr_desc = TEnil then
            error loc1 "Both side of the test are nil";
          (TEbinop (op, e1, e2), Tbool, false)
      | Badd | Bsub | Bmul | Bdiv | Bmod ->
          if not (eq_type t1 Tint) then
            error loc1
              (sprintf " Invalid type for operation, expected integer got %s"
                 (tf_typ_to_string t1));
          (TEbinop (op, e1, e2), Tint, false)
      | Blt | Ble | Bgt | Bge ->
          if not (eq_type t1 Tint) then
            error loc1
              (sprintf " Invalid type for operation, expected integer got %s"
                 (tf_typ_to_string t1));
          (TEbinop (op, e1, e2), Tbool, false)
      | Band | Bor ->
          if not (eq_type t1 Tbool) then
            error loc1
              (sprintf " Invalid type for operation, expected bool got %s"
                 (tf_typ_to_string t1));
          (TEbinop (op, e1, e2), Tbool, false))

  | PEunop (Uamp, e1) ->
      let loc = e1.pexpr_loc in
      let e1, _ = expr env e1 in
      let value =
        match e1.expr_desc with
        | TEident v -> is_l_value env (TEident v)
        | _ -> false
      in
      if not value then
        error loc
          "J'vais t'faire courir moi tu vas voir rouquin + ratio + pas l-value \
           + pas évalué";
      (TEunop (Uamp, e1), Tptr e1.expr_typ, false)

  | PEunop (Uneg, e1) ->
      let loc = e1.pexpr_loc in
      let e1, _ = expr env e1 in
      if not (eq_type e1.expr_typ Tint) then
        error loc
          (sprintf "Expected int but got %s" (tf_typ_to_string e1.expr_typ));
      (TEunop (Uneg, e1), Tint, false)

  | PEunop (Unot, e1) ->
      let loc = e1.pexpr_loc in
      let e1, _ = expr env e1 in
      if not (eq_type e1.expr_typ Tbool) then
        error loc
          (sprintf "Expected bool but got %s" (tf_typ_to_string e1.expr_typ));
      (TEunop (Unot, e1), Tbool, false)

  | PEunop (Ustar, e1) ->
      let loc = e1.pexpr_loc in
      let e1, _ = expr env e1 in
      if e1.expr_desc = TEnil then
        error loc "Ah bha c'est bien nil, bravo pour l'appareil photo !";
      let ty =
        match e1.expr_typ with
        | Tptr t -> t
        | typ ->
            error loc
              (sprintf "Expected pointers but got %s" (tf_typ_to_string typ))
      in
      (TEunop (Ustar, e1), ty, false)

  | PEcall ({ id = "fmt.Print" }, el) -> (
      fmt_used := true;
      let loc = (List.hd el).pexpr_loc in
      let l = List.map (recure env) el in
      match l with
      | [ { expr_desc = TEcall _ } ] ->
          let e = List.hd l in
          (TEprint [ e ], tvoid, false)
      | _ ->
          List.iter
            (function
              | { expr_typ = Tmany _ } ->
                  error loc
                    "Function call as part of a plotting are not supported"
              | _ -> ())
            l;
          (TEprint l, tvoid, false))

  | PEcall ({ id = "new" }, [ { pexpr_desc = PEident { id; loc } } ]) ->
      let ty =
        match id with
        | "int" -> Tint
        | "bool" -> Tbool
        | "string" -> Tstring
        | _ ->
            if not (Hashtbl.mem structure id) then
              error loc (sprintf "Undefined type %s" id);
            Tstruct (Hashtbl.find structure id)
      in
      (TEnew ty, Tptr ty, false)

  | PEcall ({ id = "new"; loc }, _) -> error loc "new expects a type"

  | PEcall ({ id; loc }, el) -> (
      if not (Hashtbl.mem funct id) then
        error loc (sprintf "Unknown function %s" id);
      let el = List.map (recure env) el in
      let f = Hashtbl.find funct id in
      match el with
      | [ { expr_desc = TEcall (g, el2) } ] when List.length f.fn_params > 1 ->
          if List.length g.fn_typ != List.length f.fn_params then
            error loc
              (sprintf
                 "Output size of %s (%d) is not matching %s input size (%d)"
                 g.fn_name (List.length el2) id (List.length el));
          let typlid =
            List.map (fun x -> x.v_typ) (Hashtbl.find funct id).fn_params
          in
          List.iter2
            (fun typ1 typ ->
              if not (eq_type typ1 typ) then
                error loc
                  (sprintf "Function %s expects type %s but got type %s" id
                     (tf_typ_to_string (Tmany typlid))
                     (tf_typ_to_string (Tmany g.fn_typ))))
            typlid g.fn_typ;
          (TEcall (f, el), Tmany f.fn_typ, false)
      | el ->
          List.iter
            (function
              | { expr_typ = Tmany _ } ->
                  error loc
                    "Function call as part of a plotting are not supported"
              | _ -> ())
            el;
          if List.length f.fn_typ = 1 then
            (TEcall (f, el), List.hd f.fn_typ, false)
          else (TEcall (f, el), Tmany f.fn_typ, false))

  | PEfor (e, b) ->
      let e, _ = expr env e and b, rt = expr env b in
      if not (eq_type e.expr_typ Tbool) then
        error loc
          (sprintf "Expected boolean condition in the loop, got %s"
             (tf_typ_to_string e.expr_typ));
      (TEfor (e, b), b.expr_typ, rt)

  | PEif (e1, e2, e3) ->
      let loc = e1.pexpr_loc in
      let e1, _ = expr env e1
      and e2, rt2 = expr env e2
      and e3, rt3 = expr env e3 in
      if not (eq_type e1.expr_typ Tbool) then
        error loc
          (sprintf "Expected boolean condition, got %s"
             (tf_typ_to_string e1.expr_typ));
      (TEif (e1, e2, e3), tvoid, rt2 && rt3)
  | PEnil -> (TEnil, Tptr Twild, false)
  | PEident { id; loc } -> (
      if id = "_" then error loc "the variable \"_\" is not meant to be used";
      try
        let v = Context.find id env in
        (Hashtbl.find Context.all_vars id).v_used <- true;
        TEident v, v.v_typ, false
      with Not_found -> error loc ("unbound variable " ^ id))

  | PEdot (e, {id;loc}) -> 
    let pos = e.pexpr_loc in
    let e,_ = expr env e in
    (match e.expr_typ with
      | Tptr (Tstruct s) -> 
        if e.expr_desc = TEnil then
          error pos "nil doesn't have dotted value";
        if not (is_l_value env e.expr_desc) || (match e.expr_desc with | TEident {v_name} -> v_name = "_" | _ -> true) then
          error pos "Not well defined mate";
        if not (Hashtbl.mem structure s.s_name) then
          error loc (sprintf "Structure %s not defined" s.s_name);
        if not (Hashtbl.mem s.s_fields id) then 
          error loc (sprintf "Fields %s do not belong to the structure %s" id s.s_name);
        TEdot(e,{f_name = s.s_name; f_typ = Tstruct s; f_ofs = 0}), (Hashtbl.find s.s_fields id).f_typ , false

      | Tstruct s -> 
        if not (is_l_value env e.expr_desc) || (match e.expr_desc with | TEident {v_name} -> v_name = "_" | _ -> true) then
          error pos "Not well defined mate no2";
        if not (Hashtbl.mem structure s.s_name) then
          error loc (sprintf "Structure %s not defined" s.s_name);
        if not (Hashtbl.mem s.s_fields id) then 
          error loc (sprintf "Fields %s do not belong to the structure %s" id s.s_name);
        TEdot(e,{f_name = s.s_name; f_typ = Tstruct s; f_ofs = 0}), (Hashtbl.find s.s_fields id).f_typ , false

      | _ -> error pos (sprintf "No attribute %s" id))

  | PEassign (lvl, el) -> 
    let pos = (List.hd lvl).pexpr_loc in
    let lvl = List.map (recure env) lvl and el = List.map (recure env) el in
    List.iter (fun x -> match x.expr_desc with | TEident v -> if not (is_l_value env (TEident v)) then error v.v_loc (sprintf "Expected l-value") | TEdot (e,f) -> if not (is_l_value env e.expr_desc) then error pos (sprintf "Expected l-value") | _ -> error pos (sprintf "Expected l-value got %s" (tf_typ_to_string x.expr_typ) )) lvl;
    (match el with
      | [{ expr_desc = TEcall (f, el2) }] -> 
        if List.length f.fn_typ <> List.length lvl then
          error pos (sprintf "Extraction expects %d val but got %d" (List.length lvl) (List.length f.fn_typ));
        List.iter2 (fun ex ex2 -> if not (eq_type ex.expr_typ ex2) then error pos (sprintf "Expected %s but got type %s" ( String.concat ", " (List.map (fun x -> tf_typ_to_string x.expr_typ) lvl)) (tf_typ_to_string (Tmany f.fn_typ)))) lvl f.fn_typ;
        TEassign (lvl, el), tvoid, false
      | el -> 
        if List.length el <> List.length lvl then
          error pos (sprintf "Extraction expects %d val but got %d" (List.length lvl) (List.length el));
        List.iter2 (fun ex ex2 -> if not (eq_type ex.expr_typ ex2.expr_typ) then error pos (sprintf "Expected %s but got type %s" ( String.concat ", " (List.map (fun x -> tf_typ_to_string x.expr_typ) lvl)) ( String.concat ", " (List.map (fun x -> tf_typ_to_string x.expr_typ) el)) )) lvl el;
        List.iter (fun x -> match x.expr_typ with |Tmany _ -> error pos "Unexpected function extraction in assignation" | _ -> ()) lvl;
        TEassign (lvl, el), tvoid, false
      )

  | PEreturn el -> 
    let pos = (List.hd el).pexpr_loc in
    let el = List.map (fun x -> let e,_ = expr env x in e) el in
    (match el with
      | [{ expr_desc = TEcall (f, el2) }] -> 
        if List.length f.fn_typ = 1 then(
          if not (eq_type (Tmany !func_type) (Tmany f.fn_typ)) then
            error pos (sprintf "Wrong type, expected %s got %s" (tf_typ_to_string (Tmany !func_type))  (tf_typ_to_string (Tmany f.fn_typ)));
          TEreturn el, tvoid, true)
        else 
          TEreturn el, tvoid, true
      | el -> 
        let tyl = List.map (fun x -> x.expr_typ) el in
        if List.mem false (List.map2 eq_type !func_type tyl) then
          error pos (sprintf "Wrong type, expected %s got %s" (tf_typ_to_string (Tmany !func_type))  (tf_typ_to_string (Tmany tyl)));

        List.iter (fun x -> match x with | Tmany _ -> error pos "Unexpected function extraction in assignation" | _ -> ()) tyl;
        TEreturn el,tvoid, true
    )

  | PEblock el -> 

    let rec aux liste env = match liste with
      | [] -> TEblock [], tvoid, false
      | t::q -> let exp, rt = expr env t in
        let rec add_vars vl env = match vl with
          | [] -> env
          | v::q -> add_vars q (Context.add env v)
        in 
        (match exp.expr_desc with
          | TEvars (var_list,_) -> (let TEblock expredesc2,_, rt2 = aux q (add_vars var_list env) in
            TEblock(exp::expredesc2), tvoid, rt || rt2)
          | _ -> let TEblock (exp2), _, rt2 = aux q env in
            TEblock(exp::exp2), tvoid, rt || rt2)
    in aux el env

  | PEincdec (e, op) ->
      let loc = e.pexpr_loc in
      let e, _ = expr env e in
      if not (eq_type e.expr_typ Tint) then
        error loc (sprintf "Expected int, got %s" (tf_typ_to_string e.expr_typ));
      (TEincdec (e, op), Tint, false)
      
  | PEvars (il, ptp, pel) ->
  let pos = (List.hd il).loc in 
    let el = List.map (recure env) pel in
    let tl = match el with
      | [] -> []
      | [{expr_desc = TEcall(f,el)}]-> 
        if List.length f.fn_typ <> List.length il then
          error pos (sprintf "Assignation expect %d arguments but got %d" (List.length il) (List.length f.fn_typ));
        f.fn_typ
      | _ -> 
        List.iter (fun x -> match x.expr_typ with | Tmany _ -> error pos "Unexpected tuplish function call in assignment" | _ -> ()) el;
        List.map (fun x -> x.expr_typ) el
    in
    if List.length tl = 0 then begin
      let tau = match ptp with | None -> error pos "No type definition for assignment" | Some ty -> type_type ty in
      let vl = List.map (fun x -> snd (Context.var x.id x.loc tau env)) il in
      TEvars (vl, el), tvoid, false
    end
    else begin
      let tau,b = match ptp with | None ->  Twild, false | Some ty -> type_type ty, true in
      if b then (
        if List.length tl <> List.length il then
          error pos (sprintf "Assignation expect %d arguments but got %d" (List.length il) (List.length tl));
        List.iter (fun x -> if not(eq_type x tau) then error pos (sprintf "Not same type, expected %s got %s" (tf_typ_to_string x) (tf_typ_to_string tau))) tl;
        TEvars(List.map (fun x -> snd (Context.var x.id x.loc tau env) ) il,el), tvoid, false

      )
      else (
        if List.length tl <> List.length il then
          error pos (sprintf "Assignation expect %d arguments but got %d" (List.length il) (List.length tl));
        TEvars(List.map2 (fun x y -> snd (Context.var x.id x.loc y env) ) il tl,el), tvoid, false

      )
    end

(* To change from not typed objects to typed objects *)
let type_type_struct = function
  | PDstruct { ps_name = { id = name; loc = pos }; ps_fields = pfl } ->
      let hash_type : (string, field) Hashtbl.t = Hashtbl.create 0 in
      let _ =
        List.map
          (fun x ->
            match x with
            | { id; loc }, ptype ->
                Hashtbl.add hash_type id
                  { f_name = id; f_typ = type_type ptype; f_ofs = 0 })
          pfl
      in
      TDstruct
        {
          s_name = name;
          s_fields = hash_type;
          s_size = Hashtbl.length hash_type;
        }
  | _ -> error dummy_loc "Bad type"

  let type_type_func = function
  | PDfunction { pf_name; pf_params; pf_typ; pf_body } ->
      let e = Context.create in
      let fn_params = List.map (fun x -> let y, z = x in new_var y.id y.loc (type_type z)) pf_params in
      let fn_typ = List.map (fun x -> type_type x) pf_typ in
      func_type :=  fn_typ;
      let e = List.fold_left (fun env var -> fst( Context.var var.v_name var.v_loc var.v_typ env)) e fn_params in
      let e, rt = expr e pf_body in
      if List.length fn_typ = 0 && ((not rt) || eq_type e.expr_typ (Tmany []))
      then
        TDfunction
          ( {
              fn_name = pf_name.id;
              fn_params =
                List.map
                  (fun x ->
                    let y, z = x in
                    new_var y.id y.loc (type_type z))
                  pf_params;
              fn_typ;
            },
          e )
      else (
        if not rt then
          error pf_name.loc (sprintf "Missing return status in %s" pf_name.id);
        TDfunction
          ( {
              fn_name = pf_name.id;
              fn_params =
                List.map
                  (fun x ->
                    let y, z = x in
                    new_var y.id y.loc (type_type z))
                  pf_params; 
              fn_typ;
            },
            e ))
  | _ -> error dummy_loc "Bad function definition"

(* 1. declare structures *)
let phase1 = function
  | PDstruct { ps_name = { id; loc } } ->
      if Hashtbl.mem structure id then
        error loc (sprintf "Structure %s already defined" id);
      Hashtbl.add structure id
        { s_name = id; s_fields = Hashtbl.create 10; s_size = 0 }
  | PDfunction _ -> ()

(* 2. declare functions and type fields *)

let rec from_ptyp_to_id = function
  | PTident { id } -> id
  | PTptr t2 -> from_ptyp_to_id t2

let rec well_defined_type ptype =
  let id = from_ptyp_to_id ptype in
  id = "bool" || id = "int" || id = "string" || Hashtbl.mem structure id

let is_repeat valu rest =
  match valu with { id; loc }, ptype -> (List.mem id rest, loc, ptype, id)

let rec well_defined_struct_list = function
  | [] -> (true, true, dummy_loc, "", [])
  | t :: q ->
      let is_good, no_repeat, loc, id, id_list = well_defined_struct_list q in
      let b, pos, ptype, name = is_repeat t id_list in
      let b2 = well_defined_type ptype in
      if (not b2) && not b then
        (false, no_repeat, pos, from_ptyp_to_id ptype, [])
      else if b then (is_good, false, pos, name, [])
      else (is_good, no_repeat, loc, id, name :: id_list)

let phase2 = function
  (* vérifier la présence de la fonction main *)
  | PDfunction { pf_name = { id = "main"; loc }; pf_params = []; pf_typ = [] } ->
      if !found_main then error loc (sprintf "Function main already defined");
      Hashtbl.add funct "main" { fn_name = "main"; fn_params = []; fn_typ = [] };
      found_main := true
  (* gère les fonctions en général *)
  | PDfunction { pf_name = { id; loc }; pf_params = pfp; pf_typ = pft } ->
      if Hashtbl.mem funct id then
        error loc (sprintf "Function %s already defined" id);
      let is_good, no_repeat, pos, name, _ = well_defined_struct_list pfp
      and b2 = List.mem false (List.map (fun x -> well_defined_type x) pft) in
      if not is_good then
        error pos (sprintf "In function %s, type %s not well defined" id name);
      if not no_repeat then
        error pos
          (sprintf "In function %s, input type %s appears multiple times" id
             name);
      if b2 then
        error loc
          (sprintf "In function %s, output type %s not well defined" id
             (from_ptyp_to_id
                (List.find (fun x -> not (well_defined_type x)) pft)));
      Hashtbl.add funct id { fn_name = id; fn_params = []; fn_typ = List.map type_type pft }
  (* gère les structures *)
  | PDstruct { ps_name = { id; loc }; ps_fields = pfield_list } -> (
      let is_good, no_repeat, pos, name, _ =
        well_defined_struct_list pfield_list
      in
      if not no_repeat then
        error loc (sprintf "In %s structure, %s already defined" id name);
      if not is_good then
        error pos (sprintf "In structure %s, type %s not well defined" id name);
      List.iter (fun (x,y) -> match y with | PTident {id = name} when name = id -> error loc "Recursive function definition is forbidden" |_ -> ()) pfield_list;

      let stru =
        type_type_struct
          (PDstruct { ps_name = { id; loc }; ps_fields = pfield_list })
      in
      Hashtbl.remove structure id;
      match stru with
      | TDstruct s -> Hashtbl.add structure id s
      | _ -> error dummy_loc "Not supposed to be")
(* j'ai pas trouvé comment faire propre... *)

(* 3. type check function bodies *)
let sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | _ -> (* TODO *) assert false

let phase3 = function
  | PDfunction { pf_name = { id; loc }; pf_params; pf_body = e; pf_typ = tyl } ->
      type_type_func
        (PDfunction
           { pf_name = { id; loc }; pf_params; pf_body = e; pf_typ = tyl })
  | PDstruct { ps_name = { id } } ->
      let s = { s_name = id; s_fields = Hashtbl.create 5; s_size = 0 } in
      TDstruct s

let file (imp, dl) =
  (* fmt_imported := imp; *)
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "Missing method main";
  let dl = List.map phase3 dl in
  Context.check_unused ();
  (* TODO variables non utilisees *)
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl
