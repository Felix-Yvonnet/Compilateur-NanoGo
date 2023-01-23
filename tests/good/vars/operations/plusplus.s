	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_main:
	pushq %rbp
	movq %rsp, %rbp
	movq $3, %rdi
	pushq %rdi
	movq -8(%rbp), %rdi
	movq -8(%rbp), %rdx
	incq %rdx
	movq %rdx, -8(%rbp)
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
