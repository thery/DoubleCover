00000000004007a0 <poly_eval>:
  4007a0:	push   %r15
  4007a2:	push   %r14
  4007a4:	push   %r13
  4007a6:	push   %r12
  4007a8:	push   %rbp
  4007a9:	push   %rbx
  4007aa:	mov    %rsi,%rbx
  4007ad:	sub    $0x78,%rsp
  4007b1:	movl   $0x0,0xc(%rsp)
  4007b9:	test   %rdi,%rdi
  4007bc:	jns    4007c9 <poly_eval+0x29>
  4007be:	movl   $0x1,0xc(%rsp)
  4007c6:	neg    %rdi
  4007c9:	mov    %rdi,%rbp
  4007cc:	xor    %eax,%eax
  4007ce:	sar    $0x20,%rbp
  4007d2:	nopl   (%rax)
  4007d5:	data16 cs nopw 0x0(%rax,%rax,1)
  4007e0:	mov    0x4032ac(%rax),%edx
  4007e6:	mov    %edx,(%rbx,%rax,1)
  4007e9:	add    $0x4,%rax
  4007ed:	cmp    $0x54,%rax
  4007f1:	jne    4007e0 <poly_eval+0x40>
  4007f3:	mov    %edi,%r15d
  4007f6:	mov    $0x403258,%r14d
  4007fc:	lea    0x54(%rbx),%r13
  400800:	lea    0x64(%rsp),%r12
  400805:	data16 cs nopw 0x0(%rax,%rax,1)
  400810:	movdqu (%rbx),%xmm0
  400814:	mov    0x50(%rbx),%eax
  400817:	lea    0x10(%rsp),%rdx
  40081c:	movaps %xmm0,0x10(%rsp)
  400821:	movdqu 0x10(%rbx),%xmm0
  400826:	mov    %eax,0x60(%rsp)
  40082a:	xor    %eax,%eax
  40082c:	movaps %xmm0,0x20(%rsp)
  400831:	movdqu 0x20(%rbx),%xmm0
  400836:	movaps %xmm0,0x30(%rsp)
  40083b:	movdqu 0x30(%rbx),%xmm0
  400840:	movaps %xmm0,0x40(%rsp)
  400845:	movdqu 0x40(%rbx),%xmm0
  40084a:	movaps %xmm0,0x50(%rsp)
  40084f:	nopw   0x0(%rax,%rax,1)
  400855:	data16 cs nopw 0x0(%rax,%rax,1)
  400860:	mov    (%rdx),%esi
  400862:	add    $0x4,%rdx
  400866:	imul   %rbp,%rsi
  40086a:	add    %rsi,%rax
  40086d:	mov    %eax,-0x4(%rdx)
  400870:	shr    $0x20,%rax
  400874:	cmp    %r12,%rdx
  400877:	jne    400860 <poly_eval+0xc0>
  400879:	mov    $0x50,%edx
  40087e:	lea    0x10(%rsp),%rsi
  400883:	lea    0x14(%rsp),%rdi
  400888:	call   400380 <memmove@plt>
  40088d:	mov    %rbx,%rsi
  400890:	mov    %rbx,%rdx
  400893:	xor    %eax,%eax
  400895:	movl   $0x0,0x10(%rsp)
  40089d:	nopl   (%rax)
  4008a0:	mov    (%rdx),%edi
  4008a2:	add    $0x4,%rdx
  4008a6:	imul   %r15,%rdi
  4008aa:	add    %rdi,%rax
  4008ad:	mov    %eax,-0x4(%rdx)
  4008b0:	shr    $0x20,%rax
  4008b4:	cmp    %r13,%rdx
  4008b7:	jne    4008a0 <poly_eval+0x100>
  4008b9:	xor    %eax,%eax
  4008bb:	xor    %edx,%edx
  4008bd:	nopl   (%rax)
  4008c0:	mov    (%rbx,%rax,1),%edi
  4008c3:	mov    0x10(%rsp,%rax,1),%r9d
  4008c8:	add    %r9,%rdi
  4008cb:	add    %rdi,%rdx
  4008ce:	mov    %edx,(%rbx,%rax,1)
  4008d1:	add    $0x4,%rax
  4008d5:	shr    $0x20,%rdx
  4008d9:	cmp    $0x54,%rax
  4008dd:	jne    4008c0 <poly_eval+0x120>
  4008df:	mov    0xc(%rsp),%eax
  4008e3:	test   %eax,%eax
  4008e5:	jne    400938 <poly_eval+0x198>
  4008e7:	xor    %eax,%eax
  4008e9:	xor    %edx,%edx
  4008eb:	cs nopw 0x0(%rax,%rax,1)
  4008f5:	data16 cs nopw 0x0(%rax,%rax,1)
  400900:	mov    (%rbx,%rax,1),%esi
  400903:	mov    (%r14,%rax,1),%edi
  400907:	add    %rdi,%rsi
  40090a:	add    %rsi,%rdx
  40090d:	mov    %edx,(%rbx,%rax,1)
  400910:	add    $0x4,%rax
  400914:	shr    $0x20,%rdx
  400918:	cmp    $0x54,%rax
  40091c:	jne    400900 <poly_eval+0x160>
  40091e:	mov    $0x403060,%eax
  400923:	cmp    %r14,%rax
  400926:	je     400959 <poly_eval+0x1b9>
  400928:	sub    $0x54,%r14
  40092c:	jmp    400810 <poly_eval+0x70>
  400931:	nopl   0x0(%rax)
  400938:	mov    $0x1,%eax
  40093d:	nopl   (%rax)
  400940:	mov    (%rsi),%edx
  400942:	add    $0x4,%rsi
  400946:	not    %edx
  400948:	add    %rdx,%rax
  40094b:	mov    %eax,-0x4(%rsi)
  40094e:	shr    $0x20,%rax
  400952:	cmp    %rsi,%r13
  400955:	jne    400940 <poly_eval+0x1a0>
  400957:	jmp    4008e7 <poly_eval+0x147>
  400959:	add    $0x78,%rsp
  40095d:	pop    %rbx
  40095e:	pop    %rbp
  40095f:	pop    %r12
  400961:	pop    %r13
  400963:	pop    %r14
  400965:	pop    %r15
  400967:	ret

