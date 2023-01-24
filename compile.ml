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
(* Dosen't work on basic assembly *)
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

(* get the number of the offset of a variable *)
let rec get_offset env = function
| TEdot (e, x) -> get_offset env e.expr_desc - x.f_ofs
| TEident v -> -(Hashtbl.find env.local_var v.v_name)
| TEunop (Ustar, x) -> get_offset env x.expr_desc
| _ -> failwith "Not a l-value."

(* same but with the direct assembly code *)
let rec from_expr_to_pos env expr =
  match expr.expr_desc with
  |TEident var -> movq !%rbp !%rdi ++ 
    subq (imm (Hashtbl.find env.local_var var.v_name)) !%rdi
  |TEdot (expr, {f_ofs}) -> 
    from_expr_to_pos env expr  ++
    (match expr.expr_typ with 
      |Tptr Tstruct _  -> movq (ind rdi) !%rdi
      | _ -> nop ) ++ subq (imm f_ofs) !%rdi
  |TEunop (Ustar, e1) -> from_expr_to_pos env e1 ++ movq (ind rdi) !%rdi
  |_ -> failwith "Ho sh*t I failed my task again!"

(* Chose the correct pattern to print the type *)
let rec print_type env e ty = match ty with
  | Tbool -> let l_false = new_label () and l_true = new_label () in testq !%rdi !%rdi ++ jz l_false ++ 
            movq (ilab "S_true") !%rdi ++ jmp l_true ++ label l_false ++
            movq (ilab "S_false") !%rdi ++
            label l_true ++ call "print_str"
  | Tstring -> call "print_str"
  | Tstruct stru -> 
            let aux code {f_typ; f_ofs}  = 
              code ++ movq !%rsi !%rcx ++ subq (imm f_ofs) !%rcx++ 
              (match f_typ with
              | Tint |Tbool |Tptr _ -> movq (ind rcx) !%rdi
              | _ ->  movq !%rcx !%rdi ) ++ print_type env e f_typ ++ 
                  movq (ilab "S_space") !%rdi ++ call "print_str"
            in
            from_expr_to_pos env e ++
            begin
            match e.expr_typ with 
              | Tptr _ ->  movq (ind rdi) !%rsi
              | _ -> movq !%rdi !%rsi
            end
            ++ movq (ilab "S_lbracket") !%rdi ++ call "print_str" ++
            List.fold_left aux nop stru.s_ordered_fields  
            ++ movq (ilab "S_rbracket") !%rdi ++ call "print_str"
  
  |Tmany l -> let aux c x =  movq (ind rsp) !%rdi ++  
              addq (imm (sizeof x)) !%rsp ++ print_type env e x ++ 
              movq (ilab "S_space") !%rdi ++ call "print_str" ++ c in 
              List.fold_left aux nop l
  | Tptr Tstruct s -> movq (ilab "S_star") !%rdi ++ call "print_str" ++ print_type env e (Tstruct s)
  | Tint | Tptr _ | Twild-> call "print_int"
  | _ -> failwith "not now, I'll be there tomorrow"

(* memcpy from assembly that copy from src to dest with len size *)
let rec memcpy src dest size =
  match size with
  |0 -> nop
  |n -> movq (ind src) !%r15 ++ movq !%r15 (ind dest) ++ 
        subq (imm 8) !%src ++ subq (imm 8) !%dest ++ 
        memcpy src dest (size-8)

let put_stack e = match e.expr_typ with 
    | Tstruct s -> subq (imm (sizeof (Tstruct s))) !%rsp ++ memcpy rdi rsp (sizeof (Tstruct s))
    | _ -> pushq !%rdi

let pop_stack e = match e.expr_typ with 
    | Tstruct s -> nop
    | _ -> popq rdi

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
  | TEbinop (Band, e1, e2) -> (* lazy and/or *)
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
  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) -> (* comparaisons between ints *)
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
  | TEbinop (Badd | Bsub | Bmul as op, e1, e2) -> (* basic operations *)
    let act = match op with
      | Badd -> addq
      | Bsub -> subq
      | Bmul -> imulq
      | _ -> failwith "Stop bothering me VS code\n"
    in
    expr env e2 ++ pushq !%rdi ++
    expr env e1 ++ popq rsi ++
    act !%rsi !%rdi
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
  | TEbinop (Beq | Bne as op, e1, e2) -> (* (in)equality with lazy tests too *)
    (* I've even done the struct though I didn't have them yet *)
    let l_false = new_label () and l_end = new_label () in
    let j_act = match op with 
      |Beq -> jnz
      |Bne -> jz
      |_ -> failwith "ratio vscode"
    in    
    let ope = 
      let rec aux = function
        | Tstring -> call "strcmp" ++ testq !%rax !%rax ++ j_act l_false
        | Tstruct s -> Hashtbl.fold (fun _ y code -> 
          code ++ pushq !%rdi ++ pushq !%rsi ++ 
          aux y.f_typ ++ popq rsi ++ popq rdi ++ subq (imm (sizeof y.f_typ)) !%rsi ++ 
          subq (imm (sizeof y.f_typ)) !%rdi) s.s_fields nop
        | Tptr _ | Tint |Tbool -> cmpq !%rdi !%rsi ++ j_act l_false
        | _ -> failwith "I hope it doesn't happen"
      in aux e1.expr_typ
    in
    expr env e2 ++ pushq !%rdi ++ expr env e1 ++ popq rsi ++ 
    ope ++ 
    movq (imm 1) !%rdi ++ jmp l_end ++
    label l_false ++ movq (imm 0) !%rdi ++ label l_end
  | TEunop (Uneg, e1) -> (* -n *)
    expr env e1 ++
    negq !%rdi
  | TEunop (Unot, e1) -> (* I first coded it to be applicable on ints but useless *)
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
    subq (imm (get_offset env e1.expr_desc-8)) !%rdi
  | TEunop (Ustar, e1) ->
    expr env e1 ++
    (match e1.expr_typ with
      |Tptr Tstruct _ -> nop
      |Tptr _ -> movq (ind rdi) !%rdi
      | _ -> failwith "Aled ça marche pas")
  | TEprint el ->
    begin
    match el with
      | [{expr_desc = TEcall (f,e);expr_typ}] -> 
          expr env {expr_desc = TEcall (f,e);expr_typ} ++
          List.fold_left (fun c t -> popq rdi ++ print_type env t t.expr_typ ++ c) nop el
      | _ -> List.fold_left (fun x y -> expr env y ++ (put_stack y) ++ x ++ (pop_stack y) ++ print_type env y y.expr_typ) nop el
    end
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
    
  | TEassign (lv, el) -> begin
    match el with
      | [{expr_desc = TEcall (f,el2);expr_typ}] -> expr env ({expr_desc = TEcall (f,el2);expr_typ}) ++ List.fold_left (fun c v -> c ++ popq rdi ++ movq !%rdi (ind ~ofs: (get_offset env v.expr_desc - 8) rbp)) nop lv
      | _ -> List.fold_left2 (fun c v e -> expr env e ++ pushq !%rdi ++ c ++ popq rdi ++ movq !%rdi (ind ~ofs:(get_offset env v.expr_desc - 8) rbp )) nop lv el
   end

  | TEblock el ->
    let code =
    let rec aux = function
      | [] -> nop
      | t::q -> begin
          match t.expr_desc with 
          | TEvars (vl,[{expr_desc = TEcall (f2,el)}]) ->
            let max_size = List.fold_left (fun x y -> x + sizeof y.v_typ) 0 vl in
            let k = ref (sizeof (List.hd (List.rev vl)).v_typ) in
            let f c = let a = if c.v_name != "_" then Hashtbl.add env.local_var c.v_name (env.next_local + max_size - !k) in 
                      k := !k + sizeof c.v_typ; a in
            List.iter f vl;
            env.next_local <- env.next_local + max_size;
            expr env ({expr_desc = TEcall (f2,el); expr_typ = Tmany f2.fn_typ}) ++
            aux q

          | TEvars (vl,eel) -> 
            let vl = List.rev vl and eel = List.rev eel in 
            let max_size = List.fold_left (fun x y -> x + sizeof y.v_typ) 0 vl in
            let k = ref (sizeof (List.hd (List.rev vl)).v_typ) in
            let f c = let a = if c.v_name != "_" then Hashtbl.add env.local_var c.v_name (env.next_local + max_size - !k) in 
                      k := !k + sizeof c.v_typ; a in
            List.iter f vl;
            env.next_local <- env.next_local + max_size;
            List.fold_left2 (fun c e v -> expr env e ++ (if v.v_name != "_" then put_stack e else nop) ++ c) nop eel vl ++
            aux q

          | _ -> let code2 = expr env t in code2 ++ aux q
    end
    in aux el in code ++
    let rec aux = function
    | [] -> nop
    | t::q -> begin 
        match t.expr_desc with 
        | TEvars (vl,[{expr_desc = TEcall (f2,el)}]) -> 
          let f c = env.next_local <- env.next_local - sizeof c.v_typ; Hashtbl.remove env.local_var c.v_name in
          List.iter f vl;
          List.fold_left (fun c e -> popq rdi ++ c) nop f2.fn_typ ++
          aux q
        | TEvars (vl,eel) -> 
          let f c = env.next_local <- env.next_local - sizeof c.v_typ; Hashtbl.remove env.local_var c.v_name in
          List.iter f vl;
          List.fold_left2 (fun c e v -> (if v.v_name != "_" then pop_stack e else nop) ++ c) nop eel vl ++
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
  | TEnew ty -> (* get the structure and return the corresponding offset *)
    let structu = match ty with 
    | Tstruct stroucte -> stroucte
    | _ -> failwith "J'essaye encore d'y croire"
    in 
    malloc structu.s_size ++ movq !%rax !%rdi ++ 
    addq (imm (structu.s_size - sizeof (List.hd structu.s_ordered_fields).f_typ)) !%rdi

  | TEcall (f, el) -> (* prep the place for return and input vars *)
    let n = List.length el in
    (if List.length f.fn_typ > 1 then
    List.fold_left (fun c t -> c ++ subq (imm (sizeof t)) !%rsp ) nop f.fn_typ (* on descend pour laisser la place aux rez *)
    else nop ) ++
    List.fold_left (fun c e -> expr env e ++ pushq !%rdi ++  c) nop el ++ (* on ajoute les arguments évalués *)
    call ("F_"^f.fn_name) ++
    addq (imm (8*n)) !%rsp

  | TEdot (e1, {f_ofs; f_typ}) -> 
    expr env e1 ++ 
    (match e1.expr_typ with
      | Tptr Tstruct _ -> movq (ind rdi) !%rdi
      | _ -> nop) ++
    addq (imm f_ofs) !%rdi ++
    (match f_typ with
        | Tint | Tbool | Tptr _ -> movq (ind rdi) !%rdi
        | _ -> nop)

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
    let max_ofs = List.fold_left (fun x y -> x + sizeof y.expr_typ) (-env.ofs_this) el in
    let el = List.rev el in
    let new_ref_ofs = ref 0 in
    List.fold_left (fun code expression  ->
    let code =
    expr env expression ++ movq !%rdi (ind ~ofs: ( max_ofs - !new_ref_ofs) rbp) ++ code
    in new_ref_ofs := !new_ref_ofs + sizeof expression.expr_typ; code) nop el ++
    movq !%rbp !%rsp ++
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
  env.next_local <- -32;
  List.iter (fun x -> Hashtbl.add env.local_var x.v_name env.next_local; env.next_local <- env.next_local - sizeof x.v_typ) f.fn_params;
  env.ofs_this <- List.fold_left (fun x y -> x - sizeof y.v_typ) (-8) f.fn_params ;
  env.next_local <- 0;
  label ("F_" ^ s) ++ pushq !%rbp ++ movq !%rsp !%rbp ++ expr env e ++ (if f.fn_typ = [] then popq rbp ++ ret else nop)

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
      label "S_star" ++ string "*" ++
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop)
    ;
  }
