0000000000400700 <main>:
  400700:	sub    $0xe8,%rsp
  400707:	lea    0xf0(%rsp),%rax
  40070f:	mov    %rax,(%rsp)
  400713:	mov    %rbx,0x8(%rsp)
  400718:	mov    %rbp,0x10(%rsp)
  40071d:	mov    %r12,0x18(%rsp)
  400722:	mov    %r13,0x20(%rsp)
  400727:	mov    %r14,0x28(%rsp)
  40072c:	movabs $0x10000000000000,%rbx
  400736:	lea    0xa7b(%rip),%rax        # 4011b8 <A0>
  40073d:	mov    %rax,0x88(%rsp)
  400745:	lea    0xac0(%rip),%r11        # 40120c <A1>
  40074c:	mov    %r11,0x90(%rsp)
  400754:	lea    0xb05(%rip),%rcx        # 401260 <A2>
  40075b:	mov    %rcx,0x98(%rsp)
  400763:	lea    0xb4a(%rip),%rcx        # 4012b4 <A3>
  40076a:	mov    %rcx,0xa0(%rsp)
  400772:	lea    0xb8f(%rip),%rdx        # 401308 <A4>
  400779:	mov    %rdx,0xa8(%rsp)
  400781:	lea    0xbd4(%rip),%r11        # 40135c <A5>
  400788:	mov    %r11,0xb0(%rsp)
  400790:	lea    0xc19(%rip),%r10        # 4013b0 <A6>
  400797:	mov    %r10,0xb8(%rsp)
  40079f:	lea    0xc5e(%rip),%rax        # 401404 <A7>
  4007a6:	mov    %rax,0xc0(%rsp)
  4007ae:	xor    %ebp,%ebp
  4007b0:	lea    0x286d(%rip),%r8        # 403024 <CO>
  4007b7:	movslq %ebp,%r11
  4007ba:	mov    %r11,%rdx
  4007bd:	imul   $0x54,%rdx,%rdx
  4007c1:	lea    (%r8,%rdx,1),%rdi
  4007c5:	lea    0x88(%rsp),%r10
  4007cd:	mov    (%r10,%r11,8),%rsi
  4007d1:	call   400470 <big_set>
  4007d6:	lea    0x2847(%rip),%rdi        # 403024 <CO>
  4007dd:	movslq %ebp,%rcx
  4007e0:	imul   $0x54,%rcx,%rcx
  4007e4:	lea    (%rdi,%rcx,1),%r10
  4007e8:	mov    $0x7,%r8d
  4007ee:	sub    %ebp,%r8d
  4007f1:	imul   $0x36,%r8d,%r8d
  4007f5:	mov    %r8,%rax
  4007f8:	test   %eax,%eax
  4007fa:	lea    0x1f(%eax),%ecx
  4007fe:	cmovl  %rcx,%rax
  400802:	sar    $0x5,%eax
  400805:	mov    %rax,%rcx
  400808:	shl    $0x5,%ecx
  40080b:	sub    %ecx,%r8d
  40080e:	mov    $0x14,%esi
  400813:	mov    %rsi,%rdi
  400816:	sub    %eax,%edi
  400818:	test   %edi,%edi
  40081a:	jl     400825 <main+0x125>
  40081c:	movslq %edi,%rdi
  40081f:	mov    (%r10,%rdi,4),%r11d
  400823:	jmp    400828 <main+0x128>
  400825:	xor    %r11d,%r11d
  400828:	movslq %esi,%rcx
  40082b:	mov    %r11d,(%r10,%rcx,4)
  40082f:	lea    -0x1(%esi),%esi
  400833:	test   %esi,%esi
  400835:	jge    400813 <main+0x113>
  400837:	test   %r8d,%r8d
  40083a:	jle    40087c <main+0x17c>
  40083c:	mov    $0x14,%esi
  400841:	lea    -0x1(%esi),%r11d
  400846:	movslq %r11d,%r9
  400849:	mov    (%r10,%r9,4),%r9d
  40084d:	mov    $0x20,%ecx
  400852:	sub    %r8d,%ecx
  400855:	shr    %cl,%r9d
  400858:	movslq %esi,%rax
  40085b:	mov    (%r10,%rax,4),%edx
  40085f:	mov    %r8,%rcx
  400862:	shl    %cl,%edx
  400864:	or     %r9d,%edx
  400867:	mov    %edx,(%r10,%rax,4)
  40086b:	lea    -0x1(%esi),%esi
  40086f:	test   %esi,%esi
  400871:	jl     40087c <main+0x17c>
  400873:	test   %esi,%esi
  400875:	jg     400841 <main+0x141>
  400877:	xor    %r9d,%r9d
  40087a:	jmp    400858 <main+0x158>
  40087c:	lea    0x1(%ebp),%ebp
  400880:	cmp    $0x8,%ebp
  400883:	jl     4007b0 <main+0xb0>
  400889:	cmp    0xbc8(%rip),%rbx        # 401458 <A7+0x54>
  400890:	jge    4009e6 <main+0x2e6>
  400896:	lea    (%rbx),%rdi
  400899:	add    0xbc0(%rip),%rdi        # 401460 <A7+0x5c>
  4008a0:	lea    0x30(%rsp),%rsi
  4008a5:	call   4005c0 <poly_eval>
  4008aa:	lea    0x30(%rsp),%rdi
  4008af:	mov    $0x226,%esi
  4008b4:	call   400540 <big_bits64>
  4008b9:	lea    0x20000000(%rax),%rbp
  4008c0:	lea    0x30(%rsp),%rdi
  4008c5:	mov    $0x1e1,%esi
  4008ca:	call   400540 <big_bits64>
  4008cf:	lea    (%rax,%rbp,1),%r13
  4008d3:	lea    0x30(%rsp),%rdi
  4008d8:	mov    $0x217,%esi
  4008dd:	call   400540 <big_bits64>
  4008e2:	mov    %rax,%r12
  4008e5:	lea    0x0(,%rbp,2),%r14
  4008ed:	xor    %rbp,%rbp
  4008f0:	cmp    %r14,%r13
  4008f3:	jae    4009c4 <main+0x2c4>
  4008f9:	mov    0x2710(%rip),%r10        # 403010 <candidates>
  400900:	lea    0x1(%r10),%rdi
  400904:	mov    %rdi,0x2705(%rip)        # 403010 <candidates>
  40090b:	lea    (%rbx,%rbp,1),%rdi
  40090f:	lea    (%rdi),%rdi
  400912:	add    0xb47(%rip),%rdi        # 401460 <A7+0x5c>
  400919:	lea    0x88(%rsp),%rsi
  400921:	call   4005c0 <poly_eval>
  400926:	lea    0x88(%rsp),%rdi
  40092e:	mov    $0x1fe,%esi
  400933:	call   400540 <big_bits64>
  400938:	and    0xb29(%rip),%rax        # 401468 <A7+0x64>
  40093f:	cmp    $0x0,%rax
  400943:	jne    40094c <main+0x24c>
  400945:	mov    $0x1,%edx
  40094a:	jmp    400998 <main+0x298>
  40094c:	cmp    0xb15(%rip),%rax        # 401468 <A7+0x64>
  400953:	jne    400996 <main+0x296>
  400955:	lea    0x88(%rsp),%r11
  40095d:	xor    %r9d,%r9d
  400960:	movslq %r9d,%r10
  400963:	mov    (%r11,%r10,4),%r8d
  400967:	cmp    $0x0,%r8d
  40096b:	je     400974 <main+0x274>
  40096d:	mov    $0x1,%edx
  400972:	jmp    400998 <main+0x298>
  400974:	lea    0x1(%r9d),%r9d
  400979:	cmp    $0xf,%r9d
  40097d:	jl     400960 <main+0x260>
  40097f:	mov    0x3c(%r11),%esi
  400983:	test   $0x3fffffff,%esi
  400989:	je     400992 <main+0x292>
  40098b:	mov    $0x1,%edx
  400990:	jmp    400998 <main+0x298>
  400992:	xor    %edx,%edx
  400994:	jmp    400998 <main+0x298>
  400996:	xor    %edx,%edx
  400998:	cmp    $0x0,%edx
  40099b:	je     4009c4 <main+0x2c4>
  40099d:	mov    0x2674(%rip),%rax        # 403018 <found>
  4009a4:	lea    0x1(%rax),%rsi
  4009a8:	mov    %rsi,0x2669(%rip)        # 403018 <found>
  4009af:	lea    0x7f5(%rip),%rdi        # 4011ab <__stringlit_1>
  4009b6:	lea    (%rbx,%rbp,1),%rsi
  4009ba:	mov    $0x0,%eax
  4009bf:	call   400370 <printf@plt>
  4009c4:	lea    0x0(%r13,%r12,1),%r13
  4009c9:	lea    0x1(%rbp),%rbp
  4009cd:	cmp    $0x100000,%rbp
  4009d4:	jb     4008f0 <main+0x1f0>
  4009da:	lea    0x100000(%rbx),%rbx
  4009e1:	jmp    400889 <main+0x189>
  4009e6:	lea    0x793(%rip),%rdi        # 401180 <__stringlit_2>
  4009ed:	mov    0x261c(%rip),%rsi        # 403010 <candidates>
  4009f4:	mov    0x261d(%rip),%rdx        # 403018 <found>
  4009fb:	mov    $0x0,%eax
  400a00:	call   400370 <printf@plt>
  400a05:	xor    %eax,%eax
  400a07:	mov    0x8(%rsp),%rbx
  400a0c:	mov    0x10(%rsp),%rbp
  400a11:	mov    0x18(%rsp),%r12
  400a16:	mov    0x20(%rsp),%r13
  400a1b:	mov    0x28(%rsp),%r14
  400a20:	add    $0xe8,%rsp
  400a27:	ret

