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

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz"

let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

type env = {
  exit_label: string;
  ofs_this: int;
  nb_locals: int ref; (* maximum *)
  next_local: int; (* 0, 1, ... *)
  local_var: (string, int) Hashtbl.t;
}

let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0; local_var = Hashtbl.create 10 }

let rec print_type ty = match ty with
  | Tint |Tptr _ | Twild-> call "print_int"
  | Tbool -> let l_false = new_label () and l_true = new_label () in testq !%rdi !%rdi ++ jz l_false ++ 
            movq (ilab (alloc_string "true")) (reg rdi) ++ jmp l_true ++ label l_false ++ 
            movq (ilab (alloc_string "false")) (reg rdi) ++ 
            label l_true ++ call "print_str"
  | Tstring -> call "print_str"
  | Tstruct {s_name;s_fields} -> movq (ilab "S_lbracket") !%rdi ++ Hashtbl.fold  (fun z y x -> x ++ 
          print_type y.f_typ) s_fields (call "print_str") ++
                                 movq (ilab "S_rbracket") !%rdi ++ call "print_str"
  | _ -> failwith "Nop"

let rec get_offset = function
  | TEdot (e, x) -> get_offset e.expr_desc + x.f_ofs
  | TEident v -> Hashtbl.find env.local_var v.v_name
  | TEunop (Ustar, x) -> get_offset x.expr_desc
  | _ -> failwith "Not a l_value.\n"

let rec expr env e = match e.expr_desc with
  | TEskip ->
    nop
  | TEconstant (Cbool true) ->
    movq (imm 1) (reg rdi)
  | TEconstant (Cbool false) ->
    movq (imm 0) (reg rdi)
  | TEconstant (Cint x) ->
    movq (imm64 x) (reg rdi)
  | TEnil ->
    xorq (reg rdi) (reg rdi)
  | TEconstant (Cstring s) ->
    let l = alloc_string s in
    movq (ilab l) (reg rdi) (* ++ call "strdup" *)
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
    expr env e1 ++ pushq (reg rdi) ++
    expr env e2 ++ popq rsi ++
    cmpq (reg rdi) (reg rsi) ++
    j_act l_true ++
    movq (imm 0) (reg rdi) ++ jmp l_end ++
    label l_true ++ movq (imm 1) (reg rdi) ++
    label l_end
  | TEbinop (Badd | Bsub | Bmul as op, e1, e2) ->
    let act = match op with
      | Badd -> addq
      | Bsub -> subq
      | Bmul -> imulq
      | _ -> failwith "Stop bothering me VS code\n"
    in
    expr env e2 ++ pushq (reg rdi) ++
    expr env e1 ++ popq r12 ++
    act (reg r12) (reg rdi)
  | TEbinop (Bdiv, e1, e2) ->
    expr env e1 ++ pushq (reg rdi) ++
    expr env e2 ++ popq rax ++
    xorq (reg rdx) (reg rdx) ++
    cqto ++
    idivq (reg rdi) ++
    movq !%rax !%rdi
  | TEbinop (Bmod, e1, e2) ->
    expr env e1 ++ pushq (reg rdi) ++
    expr env e2 ++ popq rax ++
    xorq (reg rdx) (reg rdx) ++
    cqto ++
    idivq (reg rdi) ++
    movq (reg rdx) (reg rdi)
  | TEbinop (Beq | Bne as op, e1, e2) ->
    let j_act = match op with
      | Beq -> jz
      | Bne -> jnz
      | _ -> failwith "Stop bothering me VS code\n"
    in
    let l_true = new_label() and l_end = new_label() in
    expr env e1 ++ pushq (reg rdi) ++
    expr env e2 ++ popq rsi ++
    (if e1.expr_typ = Tstring then call "strcmp" ++ testq !%rax !%rax
    else cmpq (reg rdi) (reg rsi)) ++ j_act l_true ++
    movq (imm 0) (reg rdi) ++ jmp l_end ++
    label l_true ++ movq (imm 1) (reg rdi) ++
    label l_end
  | TEunop (Uneg, e1) ->
    expr env e1 ++
    negq (reg rdi)
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
    (* TODO code pour & *) assert false
  | TEunop (Ustar, e1) ->
    expr env e1 ++
    movq (ind rdi) !%rdi
  | TEprint el ->
    let rec aux = function
      | [] -> nop
      | t::q -> expr env t ++ print_type t.expr_typ ++ 
                 (if q!=[] then movq (ilab "S_space") (reg rdi) ++ call "print_str" else nop ) ++ aux q
    in
    aux el ++
    movq (ilab "S_newline") (reg rdi) ++
    call "print_str"

  | TEident x ->
    (* For debugging :
    print_string (x.v_name ^ ": ");
    print_int (Hashtbl.find env.local_var x.v_name);
    print_string "\n";*)
    movq (ind ~ofs: (-(Hashtbl.find env.local_var x.v_name)-8) rbp) !%rdi

  | TEassign ([{expr_desc=TEident x}], [e1]) ->
    expr env e1
    
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
            let max_size = List.fold_left (fun x y -> x + sizeof y.v_typ) 0 vl in
            let k = ref (sizeof (List.hd (List.rev vl)).v_typ) in
            let f c = let a = Hashtbl.add env.local_var c.v_name (!(env.nb_locals) + max_size - !k) in 
                      k := !k + sizeof c.v_typ; a in
            List.iter f vl;
            env.nb_locals := !(env.nb_locals) + max_size;
            List.fold_left (fun c e -> expr env e ++ pushq !%rdi ++ c) nop eel ++
            aux q
          | _ -> let code = expr env t in code ++ aux q
    end
    in aux el in code ++
    let rec aux = function
    | [] -> nop
    | t::q -> begin 
        match t.expr_desc with 
        | TEvars (vl,eel) -> 
          let f c = env.nb_locals:= !(env.nb_locals) - sizeof c.v_typ; Hashtbl.remove env.local_var c.v_name in
          List.iter f vl;
          List.fold_left (fun c e -> popq rdi ++ c) nop eel ++
          aux q
        | _ -> aux q
      end
    in aux el

  | TEif (e1, e2, e3) ->
    let l_false = new_label() and l_end = new_label() in
    expr env e1 ++
    testq (reg rdi) (reg rdi) ++
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
     movq !%rdi !%r12 ++
     jmp l_repeat ++
     label l_end ++
     movq !%r12 !%rdi
  | TEnew ty ->
     allocz (sizeof ty) ++
     movq (reg rax) (reg rdi)
  | TEcall (f, el) ->
    let n = List.length el in
    List.fold_left (fun c t -> c ++ subq (imm (sizeof t)) !%rsp ) nop f.fn_typ ++ (* on descend pour laisser la place aux rez *)
    List.fold_left (fun c e -> c ++ expr env e ++ pushq !%rdi) nop el ++ (* on ajoute les arguments évalués *)
    call ("F_"^f.fn_name) ++
    if e.expr_typ != Twild then addq (imm (8*n)) !%rsp ++ popq rax else nop

  | TEdot (e1, {f_ofs=ofs}) ->
     (* TODO code pour e.f *) assert false
  | TEvars _ ->
     assert false (* fait dans block *)
  | TEreturn [] ->
    ret
  | TEreturn [e1] ->
    expr env e1 ++
    ret
  | TEreturn el ->
    List.fold_left (fun c e -> c ++ expr env e ++ pushq !%rdi) nop el ++
    ret
  | TEincdec (e1, op) ->
    let act = match op with
      | Inc -> incq
      | Dec -> decq
    in
    let ofs = get_offset e.expr_desc in
    expr env e1 ++
    movq (ind ~ofs:ofs rbp) !%rdx ++
    act !%rdx ++
    movq !%rdx (ind ~ofs:ofs rbp)


let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  let s = f.fn_name in
  label ("F_" ^ s) ++ pushq !%rbp ++ movq !%rsp !%rbp ++ expr empty_env e ++ popq rbp ++ ret

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
      xorq (reg rax) (reg rax) ++
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
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop)
    ;
  }
