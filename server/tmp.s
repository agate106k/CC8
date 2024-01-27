IO:
	.string "%lld"
	.text
	.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	subq $32, %rsp
	pushq $10
	movq %rbp, %rax
	leaq -16(%rax), %rax
	popq (%rax)
	movq $80, %rdi
	callq malloc
	pushq %rax
	movq %rbp, %rax
	leaq -8(%rax), %rax
	popq (%rax)
	pushq $0
	pushq %rbp
	callq init
	addq $16, %rsp
	.data
L1:	.string "before sorting\n"
	.text
	leaq L1(%rip), %rdi
	movq $0, %rax
	callq printf
	pushq $0
	pushq %rbp
	callq print
	addq $16, %rsp
	pushq $0
	pushq %rbp
	callq sort
	addq $16, %rsp
	.data
L2:	.string "after sorting\n"
	.text
	leaq L2(%rip), %rdi
	movq $0, %rax
	callq printf
	pushq $0
	pushq %rbp
	callq print
	addq $16, %rsp
	leaveq
	retq
