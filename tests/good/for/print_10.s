	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_main:
	pushq %rbp
	movq %rsp, %rbp
	movq $0, %rdi
	pushq %rdi
	movq $1, %rdi
	pushq %rdi
L_2:
	movq -16(%rbp), %rdi
	pushq %rdi
	movq $5, %rdi
	popq %rsi
	cmpq %rdi, %rsi
	jl L_3
	movq $0, %rdi
	jmp L_4
L_3:
	movq $1, %rdi
L_4:
	testq %rdi, %rdi
	jz L_1
	movq -16(%rbp), %rdi
	pushq %rdi
	movq -8(%rbp), %rdi
	popq %r12
	addq %r12, %rdi
	movq -16(%rbp), %rdi
	movq -8(%rbp), %rdx
	incq %rdx
	movq %rdx, -8(%rbp)
	movq %rdi, %r12
	jmp L_2
L_1:
	movq %r12, %rdi
	popq %rdi
	movq -8(%rbp), %rdi
	call print_int
	movq $S_newline, %rdi
	call print_str
	popq %rdi
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
