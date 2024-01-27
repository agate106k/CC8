IO:
	.string "%lld"
	.text
	.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	subq $32, %rsp
	pushq $1
	movq %rbp, %rax
	leaq -16(%rax), %rax
	popq (%rax)
	pushq $0
	movq %rbp, %rax
	leaq -8(%rax), %rax
	popq (%rax)
L2:
	movq %rbp, %rax
	leaq -8(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	pushq $5
	popq %rax
	popq %rbx
	cmpq %rax, %rbx
	jg L1
	subq $16, %rsp
	movq %rbp, %rax
	leaq -8(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	movq %rbp, %rax
	leaq -16(%rax), %rax
	popq (%rax)
	movq %rbp, %rax
	leaq -8(%rax), %rax
	movq (%rax), %rbx
	addq $1, %rbx
	movq %rbx, (%rax)
	subq $1, %rbx
	pushq %rbx
	jmp L2
L1:
	movq %rbp, %rax
	leaq -16(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	popq  %rsi
	leaq IO(%rip), %rdi
	movq $0, %rax
	callq printf
	leaveq
	retq
