(* étiquettes
     F_function      entrée fonction
     E_function      sortie fonction
     L_xxx           sauts
     S_xxx           chaîne

   expression calculée avec la pile si besoin, résultat final dans %rdi

   fonction : arguments sur la pile, résultat dans %rax ou sur la pile

            res k
            ...
            res 1
            arg n
            ...
            arg 1
            adr. retour
   rbp ---> ancien rbp
            ...
            var locales
            ...
            calculs
   rsp ---> ...

*)



(*
   rsi ; src
   rdi ; dest
   rcx ; len
   call memcpy
*)



open Format
open Ast
open Tast
open X86_64

exception Anomaly of string

let debug = ref false

let strings = Hashtbl.create 32
let alloc_string =
  let r = ref 0 in
  fun s ->
    incr r;
    let l = "S_" ^ string_of_int !r in
    Hashtbl.add strings l s;
    l

let malloc n = movq (imm n) !%rdi ++ call "malloc"
let allocz n = movq (imm n) !%rdi ++ call "allocz"

let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

type env = {
  mutable ofs_this: int;
  mutable next_local: int; (* maximum *)
  local_var: (string, int) Hashtbl.t;
}

let empty_env =
  { ofs_this = -1; next_local = 0; local_var = Hashtbl.create 10 }

let rec print_type ty = match ty with
  | Tint |Tptr _ | Twild-> call "print_int"
  | Tbool -> let l_false = new_label () and l_true = new_label () in testq !%rdi !%rdi ++ jz l_false ++ 
            movq (ilab "S_true") !%rdi ++ jmp l_true ++ label l_false ++
            movq (ilab "S_false") !%rdi ++
            label l_true ++ call "print_str"
  | Tstring -> call "print_str"
  | Tstruct {s_name;s_fields} -> movq (ilab "S_lbracket") !%rdi ++ Hashtbl.fold  (fun z y x -> x ++ 
          print_type y.f_typ) s_fields (call "print_str") ++
                                 movq (ilab "S_rbracket") !%rdi ++ call "print_str"
  | _ -> failwith "Nop"

let rec get_offset env = function
  | TEdot (e, x) -> get_offset env e.expr_desc - x.f_ofs
  | TEident v -> -(Hashtbl.find env.local_var v.v_name)
  | TEunop (Ustar, x) -> get_offset env x.expr_desc
  | _ -> failwith "Not a l-value."

let rec move_return_value added_ofs base_ofs = function
  | [] -> nop
  | t::q ->  move_return_value (added_ofs+sizeof t.expr_typ) base_ofs q ++
             popq rdi ++ movq !%rdi (ind ~ofs: (added_ofs+base_ofs) rbp)

let rec expr env e = match e.expr_desc with
  | TEskip ->
    nop
  | TEconstant (Cbool true) ->
    movq (imm 1) !%rdi
  | TEconstant (Cbool false) ->
    movq (imm 0) !%rdi
  | TEconstant (Cint x) ->
    movq (imm64 x) !%rdi
  | TEnil ->
    xorq !%rdi !%rdi
  | TEconstant (Cstring s) ->
    let l = alloc_string s in
    movq (ilab l) !%rdi
  | TEbinop (Band, e1, e2) ->
    let l_end = new_label () in
    expr env e1 ++
    testq !%rdi !%rdi ++
    je l_end ++
    expr env e2 ++
    label l_end
  | TEbinop (Bor, e1, e2) ->
    let l_end = new_label () in
    expr env e1 ++
    testq !%rdi !%rdi ++
    jne l_end ++
    expr env e2 ++
    label l_end
  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) ->
    let j_act = match op with
      | Blt -> jl
      | Ble -> jle
      | Bgt -> jg
      | Bge -> jge
      | _ -> failwith "Stop bothering me VS code\n"
    in
    let l_true = new_label() and l_end = new_label() in
    expr env e1 ++ pushq !%rdi ++
    expr env e2 ++ popq rsi ++
    cmpq !%rdi !%rsi ++
    j_act l_true ++
    movq (imm 0) !%rdi ++ jmp l_end ++
    label l_true ++ movq (imm 1) !%rdi ++
    label l_end
  | TEbinop (Badd | Bsub | Bmul as op, e1, e2) ->
    let act = match op with
      | Badd -> addq
      | Bsub -> subq
      | Bmul -> imulq
      | _ -> failwith "Stop bothering me VS code\n"
    in
    expr env e2 ++ pushq !%rdi ++
    expr env e1 ++ popq r12 ++
    act !%r12 !%rdi
  | TEbinop (Bdiv, e1, e2) ->
    expr env e1 ++ pushq !%rdi ++
    expr env e2 ++ popq rax ++
    xorq !%rdx !%rdx ++
    cqto ++
    idivq !%rdi ++
    movq !%rax !%rdi
  | TEbinop (Bmod, e1, e2) ->
    expr env e1 ++ pushq !%rdi ++
    expr env e2 ++ popq rax ++
    xorq !%rdx !%rdx ++
    cqto ++
    idivq !%rdi ++
    movq !%rdx !%rdi
  | TEbinop (Beq | Bne as op, e1, e2) ->
    let j_act = match op with
      | Beq -> jz
      | Bne -> jnz
      | _ -> failwith "Stop bothering me VS code\n"
    in
    let l_true = new_label() and l_end = new_label() in
    expr env e1 ++ pushq !%rdi ++
    expr env e2 ++ popq rsi ++
    (if e1.expr_typ = Tstring then call "strcmp" ++ testq !%rax !%rax
    else cmpq !%rdi !%rsi) ++ j_act l_true ++
    movq (imm 0) !%rdi ++ jmp l_end ++
    label l_true ++ movq (imm 1) !%rdi ++
    label l_end
  | TEunop (Uneg, e1) ->
    expr env e1 ++
    negq !%rdi
  | TEunop (Unot, e1) ->
    let l_un = new_label () and l_zero = new_label () in
    expr env e1 ++
    testq !%rdi !%rdi ++
    jz l_un ++
    movq (imm 0) !%rdi ++
    jmp l_zero ++
    label l_un ++
    movq (imm 1) !%rdi ++
    label l_zero

  | TEunop (Uamp, e1) ->
    movq !%rbp !%rdi ++
    subq (imm (get_offset env e1.expr_desc)) !%rdi
  | TEunop (Ustar, e1) ->
    expr env e1 ++
    movq (ind rdi) !%rdi
  | TEprint el ->
    List.fold_left (fun x y -> expr env y ++ pushq !%rdi ++ x) nop el ++
    List.fold_left (fun x y -> x ++ popq rdi ++ print_type y.expr_typ) nop el

  | TEident x ->
    (* For debugging :
    print_string (x.v_name ^ ": ");
    print_int (Hashtbl.find env.local_var x.v_name);
    print_string "\n";*)
    movq (ind ~ofs: (-(Hashtbl.find env.local_var x.v_name)-8) rbp) !%rdi

  | TEassign ([{expr_desc=TEident x}], [e1]) ->
    let ofs = get_offset env (TEident x) - 8 in
    expr env e1 ++
    movq !%rdi (ind ~ofs:ofs rbp)
    
  | TEassign ([lv], [e1]) ->
    (* TODO code pour x1,... := e1,... *) assert false 
  | TEassign (_, _) ->
     assert false
  | TEblock el ->
    let code =
    let rec aux = function
      | [] -> nop
      | t::q -> begin
          match t.expr_desc with 
          | TEvars (vl,eel) -> 
            let vl = List.rev vl and eel = List.rev eel in 
            let max_size = List.fold_left (fun x y -> x + sizeof y.v_typ) 0 vl in
            let k = ref (sizeof (List.hd (List.rev vl)).v_typ) in
            let f c = let a = Hashtbl.add env.local_var c.v_name (env.next_local + max_size - !k) in 
                      k := !k + sizeof c.v_typ; a in
            List.iter f vl;
            env.next_local <- env.next_local + max_size;
            List.fold_left (fun c e -> expr env e ++ pushq !%rdi ++ c) nop eel ++

            aux q
          | _ -> let code2 = expr env t in code2 ++ aux q
    end
    in aux el in code ++
    let rec aux = function
    | [] -> nop
    | t::q -> begin 
        match t.expr_desc with 
        | TEvars (vl,eel) -> 
          let f c = env.next_local <- env.next_local - sizeof c.v_typ; Hashtbl.remove env.local_var c.v_name in
          List.iter f vl;
          List.fold_left (fun c e -> popq rdi ++ c) nop eel ++
          aux q
        | _ -> aux q
      end
    in aux el

  | TEif (e1, e2, e3) ->
    let l_false = new_label() and l_end = new_label() in
    expr env e1 ++
    testq !%rdi !%rdi ++
    jz l_false ++
    expr env e2 ++
    jmp l_end ++
    label l_false ++
    expr env e3 ++
    label l_end
  | TEfor (e1, e2) ->
     let l_end = new_label () and l_repeat = new_label () in
     label l_repeat ++
     expr env e1 ++
     testq !%rdi !%rdi ++
     jz l_end ++
     expr env e2 ++
     jmp l_repeat ++
     label l_end
  | TEnew ty ->
     allocz (sizeof ty) ++
     movq !%rax !%rdi
  | TEcall (f, el) ->
    let n = List.length el in
    (if List.length f.fn_typ > 1 then
    List.fold_left (fun c t -> c ++ subq (imm (sizeof t)) !%rsp ) nop f.fn_typ (* on descend pour laisser la place aux rez *)
    else nop ) ++
    List.fold_left (fun c e -> expr env e ++ pushq !%rdi ++  c) nop el ++ (* on ajoute les arguments évalués *)
    call ("F_"^f.fn_name) ++
    addq (imm (8*n)) !%rsp

  | TEdot (e1, {f_ofs=ofs}) ->
     (* TODO code pour e.f *) assert false
  | TEvars _ ->
     assert false (* fait dans block *)
  | TEreturn [] ->
    movq !%rbp !%rsp ++
    popq rbp ++
    ret
  | TEreturn [e1] ->
    expr env e1 ++
    movq !%rbp !%rsp ++
    popq rbp ++
    ret
  | TEreturn el ->
    move_return_value 0 env.ofs_this el ++
    movq !%rbp !%rsi ++
    popq rbp ++
    ret
  | TEincdec (e1, op) ->
    let act = match op with
      | Inc -> incq
      | Dec -> decq
    in
    let ofs = get_offset env (e1.expr_desc) - 8 in
    expr env e1 ++
    act !%rdi ++
    movq !%rdi (ind ~ofs:ofs rbp)

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  let s = f.fn_name in
  let env = empty_env in
  env.next_local <- -24;
  List.iter (fun x -> Hashtbl.add env.local_var x.v_name env.next_local; env.next_local <- env.next_local + sizeof x.v_typ) f.fn_params;
  env.ofs_this <- List.fold_left (fun x y -> x + sizeof y.v_typ) 0 f.fn_params;
  env.next_local <- 0;
  label ("F_" ^ s) ++ pushq !%rbp ++ movq !%rsp !%rbp ++ expr env e ++ popq rbp ++ ret

let decl code = function
  | TDfunction (f, e) -> code ++ function_ f e
  | TDstruct _ -> code

let file ?debug:(b=false) dl =
  debug := b;
  (* TODO calcul offset champs *)
  let funs = List.fold_left decl nop dl in
  { text =
      globl "main" ++ label "main" ++
      call "F_main" ++
      xorq !%rax !%rax ++
      ret ++
      funs ++
      inline "
print_int:
        movq    %rdi, %rsi
        movq    $S_int, %rdi
        xorq    %rax, %rax
        call    printf
        ret

print_str:
        movq    %rdi, %rsi
        movq    $S_str, %rdi
        xorq    %rax, %rax
        call    printf
        ret
"; (* TODO print pour d'autres valeurs *)
   (* TODO appel malloc de stdlib *)
    data =
      label "S_int" ++ string "%ld" ++
      label "S_str" ++ string "%s" ++
      label "S_space" ++ string " " ++
      label "S_newline" ++ string "\n" ++
      label "S_lbracket" ++ string "{" ++      
      label "S_rbracket" ++ string "}" ++
      label "S_true" ++ string "true" ++
      label "S_false" ++ string "false" ++
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop)
    ;
  }
