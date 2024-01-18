IO:
	.string "%lld"
	.text
	.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	subq $64, %rsp
	pushq $3
	movq %rbp, %rax
	leaq -40(%rax), %rax
	popq (%rax)
	pushq $2
	movq %rbp, %rax
	leaq -56(%rax), %rax
	popq (%rax)
	pushq $3
	movq %rbp, %rax
	leaq -8(%rax), %rax
	popq (%rax)
L2:
	subq $16, %rsp
	movq %rbp, %rax
	leaq -56(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	movq %rbp, %rax
	leaq -8(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	popq %rax
	addq %rax, (%rsp)
	movq %rbp, %rax
	leaq -56(%rax), %rax
	popq (%rax)
	movq %rbp, %rax
	leaq -40(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	pushq $1
	popq %rax
	subq %rax, (%rsp)
	movq %rbp, %rax
	leaq -40(%rax), %rax
	popq (%rax)
	movq %rbp, %rax
	leaq -40(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	pushq $0
	popq %rax
	popq %rbx
	cmpq %rax, %rbx
	jle L1
	jmp L2
L1:
	.data
L3:	.string "Answer = "
	.text
	leaq L3(%rip), %rdi
	movq $0, %rax
	callq printf
	movq %rbp, %rax
	leaq -56(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	popq  %rsi
	leaq IO(%rip), %rdi
	movq $0, %rax
	callq printf
	.data
L4:	.string "\n"
	.text
	leaq L4(%rip), %rdi
	movq $0, %rax
	callq printf
	leaveq
	retq
