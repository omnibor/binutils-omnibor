        .section	.note.omnibor,"awMS",@progbits,1
	.text
	.data
	.align 8
	.type	a, @object
	.size	a, 8
a:
	.quad	10
	.section	.rodata
.LC0:
	.string	"Got%ld!\n"
	.text
	.globl	main
	.type	main, @function
main:
.LFB0:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	a(%rip), %rax
	movq	%rax, %rsi
	movl	$.LC0, %edi
	movl	$0, %eax
	call	printf
	movl	$0, %eax
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	main, .-main
	.ident	"GCC: (GNU) 11.3.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.omnibor
	.string	"\b"
	.string	""
	.string	""
	.string	"\024"
	.string	""
	.string	""
	.string	"\001"
	.string	""
	.string	""
	.string	"OMNIBOR"
	.ascii	"\002\006\240\264\321|\b\355\001\265z7\302{\201\261T\361\252#"
	.string	"\b"
	.string	""
	.string	""
	.string	" "
	.string	""
	.string	""
	.string	"\002"
	.string	""
	.string	""
	.string	"OMNIBOR"
	.ascii	";\302\370\223\312\266n\0020\243A\013#\371\350\004\266\230J|9"
	.ascii	".\343\351s^\t-\254\263\331\250"
