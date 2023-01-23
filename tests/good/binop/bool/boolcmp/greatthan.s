	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_main:
	pushq %rbp
	movq %rsp, %rbp
	movq $5, %rdi
	pushq %rdi
	movq $6, %rdi
	popq %rsi
	cmpq %rdi, %rsi
	jg L_3
	movq $0, %rdi
	jmp L_4
L_3:
	movq $1, %rdi
L_4:
	testq %rdi, %rdi
	jz L_1
	movq $S_2, %rdi
	jmp L_2
L_1:
	movq $S_1, %rdi
L_2:
	call print_str
	movq $S_newline, %rdi
	call print_str
	popq %rbp
	ret

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
	.data
S_int:
	.string "%ld"
S_str:
	.string "%s"
S_space:
	.string " "
S_newline:
	.string "\n"
S_lbracket:
	.string "{"
S_rbracket:
	.string "}"
S_2:
	.string "true"
S_1:
	.string "false"
