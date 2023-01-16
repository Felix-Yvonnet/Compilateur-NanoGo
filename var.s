	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_main:
	movq $2, %rdi
	pushq %rdi
	movq $1, %rdi
	pushq %rdi
	movq $7, %rdi
	pushq %rdi
	movq $2, %rdi
	popq %r12
	addq %r12, %rdi
	call print_int
	movq $S_space, %rdi
	call print_str
	call print_int
	movq $S_newline, %rdi
	call print_str
	popq %rdi
	popq %rdi
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
