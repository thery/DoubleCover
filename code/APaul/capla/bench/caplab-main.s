0000000000401760 <main>:
  401760:	sub    $0x538,%rsp
  401767:	lea    0x540(%rsp),%rax
  40176f:	mov    %rax,0x8(%rsp)
  401774:	mov    %rbx,0x10(%rsp)
  401779:	mov    %rbp,0x18(%rsp)
  40177e:	mov    %r12,0x20(%rsp)
  401783:	mov    %r13,0x28(%rsp)
  401788:	mov    %r14,0x30(%rsp)
  40178d:	mov    %rsi,%r12
  401790:	mov    %rdi,%rbp
  401793:	lea    0x50(%rsp),%r9
  401798:	lea    0x290(%rsp),%rdx
  4017a0:	xor    %esi,%esi
  4017a2:	movslq %esi,%rax
  4017a5:	mov    %rax,%rcx
  4017a8:	imul   $0x54,%rcx,%rcx
  4017ac:	lea    (%rdx,%rcx,1),%rdi
  4017b0:	mov    %rdi,(%r9,%rax,8)
  4017b4:	lea    0x1(%esi),%esi
  4017b8:	cmp    $0x8,%esi
  4017bb:	jl     4017a2 <main+0x42>
  4017bd:	cmp    $0x2,%ebp
  4017c0:	jne    401a34 <main+0x2d4>
  4017c6:	mov    0x8(%r12),%rdi
  4017cb:	lea    0xc3c(%rip),%rsi        # 40240e <__stringlit_1>
  4017d2:	call   4003b0 <strcmp@plt>
  4017d7:	test   %eax,%eax
  4017d9:	jne    401a34 <main+0x2d4>
  4017df:	xor    %r12d,%r12d
  4017e2:	movabs $0x10000000000000,%rdi
  4017ec:	movabs $0x100029f16b11c7,%rsi
  4017f6:	lea    0x50(%rsp),%rdx
  4017fb:	lea    0xc1e(%rip),%rcx        # 402420 <oracle>
  401802:	mov    $0x5,%r8d
  401808:	lea    0x40(%rsp),%r9
  40180d:	mov    $0x15,%r10d
  401813:	mov    %r10,(%rsp)
  401817:	call   400500 <htr_check>
  40181c:	movzbl %al,%ebp
  40181f:	lea    0xac3(%rip),%rsi        # 4022e9 <__stringlit_3>
  401826:	lea    0xb68(%rip),%rdx        # 402395 <__stringlit_2>
  40182d:	cmp    $0x0,%ebp
  401830:	cmove  %rdx,%rsi
  401834:	lea    0xb83(%rip),%rdi        # 4023be <__stringlit_4>
  40183b:	mov    $0x0,%eax
  401840:	call   400390 <printf@plt>
  401845:	lea    0xa5c(%rip),%rdi        # 4022a8 <__stringlit_5>
  40184c:	mov    0x40(%rsp),%rsi
  401851:	mov    0x48(%rsp),%rdx
  401856:	mov    $0x0,%eax
  40185b:	call   400390 <printf@plt>
  401860:	mov    $0x1,%ebx
  401865:	cmp    $0x0,%ebp
  401868:	cmovne %r12,%rbx
  40186c:	movabs $0x10000000000001,%rax
  401876:	mov    %rax,0x38(%rsp)
  40187b:	movabs $0x10000000000000,%rdi
  401885:	movabs $0x10000000a00000,%rsi
  40188f:	lea    0x50(%rsp),%rdx
  401894:	lea    0x38(%rsp),%rcx
  401899:	mov    $0x1,%r8d
  40189f:	lea    0x40(%rsp),%r9
  4018a4:	mov    $0x15,%r10d
  4018aa:	mov    %r10,(%rsp)
  4018ae:	call   400500 <htr_check>
  4018b3:	movzbl %al,%ebp
  4018b6:	lea    0xa12(%rip),%rsi        # 4022cf <__stringlit_7>
  4018bd:	lea    0xa1c(%rip),%rdi        # 4022e0 <__stringlit_6>
  4018c4:	cmp    $0x0,%ebp
  4018c7:	cmove  %rdi,%rsi
  4018cb:	lea    0xa9e(%rip),%rdi        # 402370 <__stringlit_8>
  4018d2:	mov    $0x0,%eax
  4018d7:	call   400390 <printf@plt>
  4018dc:	mov    $0x1,%r14d
  4018e2:	cmp    $0x0,%ebp
  4018e5:	cmove  %rbx,%r14
  4018e9:	movabs $0x10000238500000,%r13
  4018f3:	movabs $0x10000238600000,%r12
  4018fd:	lea    0x50(%rsp),%rdx
  401902:	lea    0xb17(%rip),%rcx        # 402420 <oracle>
  401909:	mov    $0x1,%r8d
  40190f:	lea    0x40(%rsp),%r9
  401914:	mov    $0x15,%r10d
  40191a:	mov    %r10,(%rsp)
  40191e:	mov    %r12,%rsi
  401921:	mov    %r13,%rdi
  401924:	call   400500 <htr_check>
  401929:	movzbl %al,%ebx
  40192c:	lea    0x9b6(%rip),%rsi        # 4022e9 <__stringlit_3>
  401933:	lea    0xa5b(%rip),%rdi        # 402395 <__stringlit_2>
  40193a:	cmp    $0x0,%ebx
  40193d:	cmove  %rdi,%rsi
  401941:	lea    0x9c9(%rip),%rdi        # 402311 <__stringlit_9>
  401948:	mov    0x48(%rsp),%rdx
  40194d:	mov    $0x0,%eax
  401952:	call   400390 <printf@plt>
  401957:	mov    $0x1,%ebp
  40195c:	cmp    $0x0,%ebx
  40195f:	cmovne %r14,%rbp
  401963:	lea    0x50(%rsp),%rdx
  401968:	lea    0xab1(%rip),%rcx        # 402420 <oracle>
  40196f:	xor    %r8,%r8
  401972:	lea    0x40(%rsp),%r9
  401977:	mov    $0x15,%r11d
  40197d:	mov    %r11,(%rsp)
  401981:	mov    %r12,%rsi
  401984:	mov    %r13,%rdi
  401987:	call   400500 <htr_check>
  40198c:	movzbl %al,%ebx
  40198f:	lea    0x939(%rip),%rsi        # 4022cf <__stringlit_7>
  401996:	lea    0x943(%rip),%r8        # 4022e0 <__stringlit_6>
  40199d:	cmp    $0x0,%ebx
  4019a0:	cmove  %r8,%rsi
  4019a4:	lea    0x9f3(%rip),%rdi        # 40239e <__stringlit_10>
  4019ab:	mov    $0x0,%eax
  4019b0:	call   400390 <printf@plt>
  4019b5:	mov    $0x1,%r14d
  4019bb:	cmp    $0x0,%ebx
  4019be:	cmove  %rbp,%r14
  4019c2:	movabs $0x100002385331bf,%rax
  4019cc:	mov    %rax,0x38(%rsp)
  4019d1:	lea    0x50(%rsp),%rdx
  4019d6:	lea    0x38(%rsp),%rcx
  4019db:	mov    $0x1,%r8d
  4019e1:	lea    0x40(%rsp),%r9
  4019e6:	mov    $0x15,%esi
  4019eb:	mov    %rsi,(%rsp)
  4019ef:	mov    %r12,%rsi
  4019f2:	mov    %r13,%rdi
  4019f5:	call   400500 <htr_check>
  4019fa:	movzbl %al,%ebx
  4019fd:	lea    0x8cb(%rip),%rsi        # 4022cf <__stringlit_7>
  401a04:	lea    0x8d5(%rip),%r10        # 4022e0 <__stringlit_6>
  401a0b:	cmp    $0x0,%ebx
  401a0e:	cmove  %r10,%rsi
  401a12:	lea    0x8d9(%rip),%rdi        # 4022f2 <__stringlit_11>
  401a19:	mov    $0x0,%eax
  401a1e:	call   400390 <printf@plt>
  401a23:	mov    $0x1,%eax
  401a28:	cmp    $0x0,%ebx
  401a2b:	cmove  %r14,%rax
  401a2f:	jmp    401b12 <main+0x3b2>
  401a34:	movabs $0x10000000000000,%rbx
  401a3e:	movabs $0x100029f16b11c7,%rsi
  401a48:	cmp    $0x3,%ebp
  401a4b:	jne    401a77 <main+0x317>
  401a4d:	mov    0x8(%r12),%rdi
  401a52:	xor    %rsi,%rsi
  401a55:	mov    $0xa,%edx
  401a5a:	call   4003c0 <strtoll@plt>
  401a5f:	mov    %rax,%rbx
  401a62:	mov    0x10(%r12),%rdi
  401a67:	xor    %rsi,%rsi
  401a6a:	mov    $0xa,%edx
  401a6f:	call   4003c0 <strtoll@plt>
  401a74:	mov    %rax,%rsi
  401a77:	lea    0x50(%rsp),%rdx
  401a7c:	lea    0x90(%rsp),%rcx
  401a84:	mov    $0x40,%r8d
  401a8a:	lea    0x40(%rsp),%r9
  401a8f:	mov    $0x15,%r11d
  401a95:	mov    %r11,(%rsp)
  401a99:	mov    %rbx,%rdi
  401a9c:	call   4011a0 <htr_search>
  401aa1:	mov    %rax,%rbx
  401aa4:	xor    %rbp,%rbp
  401aa7:	cmp    %rbx,%rbp
  401aaa:	jae    401ad5 <main+0x375>
  401aac:	cmp    $0x40,%rbp
  401ab0:	jae    401ad5 <main+0x375>
  401ab2:	lea    0x95c(%rip),%rdi        # 402415 <__stringlit_12>
  401ab9:	lea    0x90(%rsp),%r8
  401ac1:	mov    (%r8,%rbp,8),%rsi
  401ac5:	mov    $0x0,%eax
  401aca:	call   400390 <printf@plt>
  401acf:	lea    0x1(%rbp),%rbp
  401ad3:	jmp    401aa7 <main+0x347>
  401ad5:	cmp    $0x40,%rbx
  401ad9:	jbe    401af5 <main+0x395>
  401adb:	lea    0x86d(%rip),%rdi        # 40234f <__stringlit_13>
  401ae2:	lea    -0x40(%rbx),%rsi
  401ae6:	mov    $0x40,%edx
  401aeb:	mov    $0x0,%eax
  401af0:	call   400390 <printf@plt>
  401af5:	lea    0x8e7(%rip),%rdi        # 4023e3 <__stringlit_14>
  401afc:	mov    0x40(%rsp),%rsi
  401b01:	mov    0x48(%rsp),%rdx
  401b06:	mov    $0x0,%eax
  401b0b:	call   400390 <printf@plt>
  401b10:	xor    %eax,%eax
  401b12:	mov    0x10(%rsp),%rbx
  401b17:	mov    0x18(%rsp),%rbp
  401b1c:	mov    0x20(%rsp),%r12
  401b21:	mov    0x28(%rsp),%r13
  401b26:	mov    0x30(%rsp),%r14
  401b2b:	add    $0x538,%rsp
  401b32:	ret

