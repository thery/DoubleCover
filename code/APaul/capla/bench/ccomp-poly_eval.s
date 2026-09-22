00000000004005c0 <poly_eval>:
  4005c0:	sub    $0x88,%rsp
  4005c7:	lea    0x90(%rsp),%rax
  4005cf:	mov    %rax,(%rsp)
  4005d3:	mov    %rbx,0x8(%rsp)
  4005d8:	mov    %rbp,0x10(%rsp)
  4005dd:	mov    %r12,0x18(%rsp)
  4005e2:	mov    %r13,0x20(%rsp)
  4005e7:	mov    %r14,0x28(%rsp)
  4005ec:	mov    %rsi,%rbx
  4005ef:	xor    %r13d,%r13d
  4005f2:	test   %rdi,%rdi
  4005f5:	jge    400600 <poly_eval+0x40>
  4005f7:	mov    $0x1,%r13d
  4005fd:	neg    %rdi
  400600:	mov    %rdi,%rbp
  400603:	mov    %rdi,%r12
  400606:	sar    $0x20,%r12
  40060a:	lea    0x2c5f(%rip),%rsi        # 403270 <CO+0x24c>
  400611:	mov    %rbx,%rdi
  400614:	call   400470 <big_set>
  400619:	mov    $0x6,%r14d
  40061f:	lea    0x30(%rsp),%rdi
  400624:	mov    %rbx,%rsi
  400627:	call   400470 <big_set>
  40062c:	lea    0x30(%rsp),%rdi
  400631:	mov    %r12,%rsi
  400634:	call   4004f0 <big_mul32>
  400639:	lea    0x30(%rsp),%rcx
  40063e:	mov    $0x14,%edi
  400643:	movslq %edi,%r8
  400646:	lea    -0x1(%edi),%edi
  40064a:	movslq %edi,%r11
  40064d:	mov    (%rcx,%r11,4),%r10d
  400651:	mov    %r10d,(%rcx,%r8,4)
  400655:	test   %edi,%edi
  400657:	jg     400643 <poly_eval+0x83>
  400659:	xor    %r11d,%r11d
  40065c:	mov    %r11d,0x30(%rsp)
  400661:	mov    %rbp,%rsi
  400664:	mov    %rbx,%rdi
  400667:	call   4004f0 <big_mul32>
  40066c:	lea    0x30(%rsp),%rsi
  400671:	mov    %rbx,%rdi
  400674:	call   4004a0 <big_add>
  400679:	cmp    $0x0,%r13d
  40067d:	je     4006ac <poly_eval+0xec>
  40067f:	mov    $0x1,%eax
  400684:	xor    %r10d,%r10d
  400687:	movslq %r10d,%r8
  40068a:	mov    (%rbx,%r8,4),%ecx
  40068e:	not    %ecx
  400690:	mov    %ecx,%edx
  400692:	lea    (%rdx,%rax,1),%rax
  400696:	mov    %rax,%rsi
  400699:	mov    %esi,(%rbx,%r8,4)
  40069d:	shr    $0x20,%rax
  4006a1:	lea    0x1(%r10d),%r10d
  4006a6:	cmp    $0x15,%r10d
  4006aa:	jl     400687 <poly_eval+0xc7>
  4006ac:	lea    0x2971(%rip),%rsi        # 403024 <CO>
  4006b3:	movslq %r14d,%rdx
  4006b6:	imul   $0x54,%rdx,%rdx
  4006ba:	lea    (%rsi,%rdx,1),%rsi
  4006be:	mov    %rbx,%rdi
  4006c1:	call   4004a0 <big_add>
  4006c6:	lea    -0x1(%r14d),%r14d
  4006cb:	test   %r14d,%r14d
  4006ce:	jge    40061f <poly_eval+0x5f>
  4006d4:	mov    0x8(%rsp),%rbx
  4006d9:	mov    0x10(%rsp),%rbp
  4006de:	mov    0x18(%rsp),%r12
  4006e3:	mov    0x20(%rsp),%r13
  4006e8:	mov    0x28(%rsp),%r14
  4006ed:	add    $0x88,%rsp
  4006f4:	ret
  4006f5:	data16 cs nopw 0x0(%rax,%rax,1)

