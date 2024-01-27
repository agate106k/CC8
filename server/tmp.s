IO:
	.string "%lld"
	.text
	.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	pushq $1
	movq %rbp, %rax
	leaq -8(%rax), %rax
	popq (%rax)
	subq $16, %rsp
	movq %rbp, %rax
	leaq -8(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	popq  %rsi
	leaq IO(%rip), %rdi
	movq $0, %rax
	callq printf
	leaveq
	retq
