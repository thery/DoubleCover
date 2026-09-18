00000000004003a0 <main>:
  4003a0:	push   %r15
  4003a2:	mov    $0x403060,%esi
  4003a7:	mov    $0x40305c,%r9d
  4003ad:	mov    $0x17a,%r10d
  4003b3:	push   %r14
  4003b5:	push   %r13
  4003b7:	push   %r12
  4003b9:	push   %rbp
  4003ba:	mov    $0x1,%ebp
  4003bf:	push   %rbx
  4003c0:	sub    $0xc8,%rsp
  4003c7:	movq   0x1149(%rip),%xmm0        # 401518 <A0+0x58>
  4003cf:	movhps 0x114a(%rip),%xmm0        # 401520 <A0+0x60>
  4003d6:	lea    0x60(%rsp),%r11
  4003db:	movaps %xmm0,0x60(%rsp)
  4003e0:	movq   0x1140(%rip),%xmm0        # 401528 <A0+0x68>
  4003e8:	movhps 0x1141(%rip),%xmm0        # 401530 <A0+0x70>
  4003ef:	movaps %xmm0,0x70(%rsp)
  4003f4:	movq   0x113c(%rip),%xmm0        # 401538 <A0+0x78>
  4003fc:	movhps 0x113d(%rip),%xmm0        # 401540 <A0+0x80>
  400403:	movaps %xmm0,0x80(%rsp)
  40040b:	movq   0x1135(%rip),%xmm0        # 401548 <A0+0x88>
  400413:	movhps 0x1136(%rip),%xmm0        # 401550 <A0+0x90>
  40041a:	movaps %xmm0,0x90(%rsp)
  400422:	mov    (%r11),%rax
  400425:	mov    %r10d,%edx
  400428:	mov    %r10d,%r8d
  40042b:	mov    %ebp,%ecx
  40042d:	sar    $0x5,%edx
  400430:	and    $0x1f,%r8d
  400434:	movdqu (%rax),%xmm0
  400438:	sub    %edx,%ecx
  40043a:	movups %xmm0,(%rsi)
  40043d:	movdqu 0x10(%rax),%xmm0
  400442:	movups %xmm0,0x10(%rsi)
  400446:	movdqu 0x20(%rax),%xmm0
  40044b:	movups %xmm0,0x20(%rsi)
  40044f:	movdqu 0x30(%rax),%xmm0
  400454:	movups %xmm0,0x30(%rsi)
  400458:	movdqu 0x40(%rax),%xmm0
  40045d:	mov    0x50(%rax),%eax
  400460:	mov    %eax,0x50(%rsi)
  400463:	movslq %edx,%rax
  400466:	neg    %rax
  400469:	movups %xmm0,0x40(%rsi)
  40046d:	lea    (%rsi,%rax,4),%r12
  400471:	mov    $0x13,%eax
  400476:	cs nopw 0x0(%rax,%rax,1)
  400480:	mov    %ecx,%edi
  400482:	xor    %edx,%edx
  400484:	add    %eax,%edi
  400486:	js     40048d <main+0xed>
  400488:	mov    0x4(%r12,%rax,4),%edx
  40048d:	mov    %edx,0x4(%rsi,%rax,4)
  400491:	sub    $0x1,%rax
  400495:	cmp    $0xfffffffffffffffe,%rax
  400499:	jne    400480 <main+0xe0>
  40049b:	mov    $0x20,%r12d
  4004a1:	lea    0x50(%rsi),%rax
  4004a5:	sub    %r8d,%r12d
  4004a8:	test   %r8d,%r8d
  4004ab:	jne    4004c5 <main+0x125>
  4004ad:	jmp    4004d3 <main+0x133>
  4004af:	mov    -0x4(%rax),%edx
  4004b2:	mov    %r12d,%ecx
  4004b5:	sub    $0x4,%rax
  4004b9:	shr    %cl,%edx
  4004bb:	or     %edi,%edx
  4004bd:	mov    %edx,0x4(%rax)
  4004c0:	cmp    %rax,%r9
  4004c3:	je     4004d3 <main+0x133>
  4004c5:	mov    (%rax),%edi
  4004c7:	mov    %r8d,%ecx
  4004ca:	shl    %cl,%edi
  4004cc:	cmp    %rax,%rsi
  4004cf:	jne    4004af <main+0x10f>
  4004d1:	mov    %edi,(%rsi)
  4004d3:	add    $0x54,%rsi
  4004d7:	add    $0x8,%r11
  4004db:	sub    $0x36,%r10d
  4004df:	add    $0x54,%r9
  4004e3:	cmp    $0x403300,%rsi
  4004ea:	jne    400422 <main+0x82>
  4004f0:	mov    0x2b51(%rip),%r15        # 403048 <candidates>
  4004f7:	movabs $0x10000000100000,%r13
  400501:	nopl   0x0(%rax)
  400505:	data16 cs nopw 0x0(%rax,%rax,1)
  400510:	movabs $0xffefffeb073a771c,%rax
  40051a:	mov    %rsp,%rsi
  40051d:	lea    -0x100000(%r13),%r14
  400524:	lea    0x0(%r13,%rax,1),%rdi
  400529:	call   4007a0 <poly_eval>
  40052e:	mov    0x4c(%rsp),%eax
  400532:	mov    0x44(%rsp),%rdx
  400537:	mov    0x44(%rsp),%ecx
  40053b:	mov    0x48(%rsp),%r12d
  400540:	shld   $0x3a,%rdx,%rax
  400545:	lea    0x20000000(%rax),%rbp
  40054c:	mov    0x3c(%rsp),%rax
  400551:	shld   $0x3f,%rax,%rcx
  400556:	mov    0x40(%rsp),%rax
  40055b:	lea    (%rcx,%rbp,1),%rbx
  40055f:	add    %rbp,%rbp
  400562:	shld   $0x29,%rax,%r12
  400567:	jmp    40058f <main+0x1ef>
  400569:	nopl   0x0(%rax)
  400570:	movabs $0x7ffffffff,%rcx
  40057a:	cmp    %rcx,%rax
  40057d:	je     400650 <main+0x2b0>
  400583:	add    $0x1,%r14
  400587:	add    %r12,%rbx
  40058a:	cmp    %r13,%r14
  40058d:	je     400604 <main+0x264>
  40058f:	cmp    %rbp,%rbx
  400592:	jae    400583 <main+0x1e3>
  400594:	movabs $0xffefffeb074a771c,%rax
  40059e:	lea    0x60(%rsp),%rsi
  4005a3:	add    $0x1,%r15
  4005a7:	lea    (%r14,%rax,1),%rdi
  4005ab:	mov    %r15,0x2a96(%rip)        # 403048 <candidates>
  4005b2:	call   4007a0 <poly_eval>
  4005b7:	mov    0xa4(%rsp),%eax
  4005be:	mov    0x9c(%rsp),%rsi
  4005c6:	movabs $0x7ffffffff,%rcx
  4005d0:	shld   $0x22,%rsi,%rax
  4005d5:	and    %rcx,%rax
  4005d8:	jne    400570 <main+0x1d0>
  4005da:	mov    %r14,%rsi
  4005dd:	mov    $0x4011d0,%edi
  4005e2:	xor    %eax,%eax
  4005e4:	add    $0x1,%r14
  4005e8:	addq   $0x1,0x2a50(%rip)        # 403040 <found>
  4005f0:	add    %r12,%rbx
  4005f3:	call   400370 <printf@plt>
  4005f8:	mov    0x2a49(%rip),%r15        # 403048 <candidates>
  4005ff:	cmp    %r13,%r14
  400602:	jne    40058f <main+0x1ef>
  400604:	lea    0x100000(%r14),%r13
  40060b:	movabs $0x100029f1800000,%rax
  400615:	cmp    %rax,%r13
  400618:	jne    400510 <main+0x170>
  40061e:	mov    0x2a1b(%rip),%rdx        # 403040 <found>
  400625:	mov    %r15,%rsi
  400628:	mov    $0x4011e0,%edi
  40062d:	xor    %eax,%eax
  40062f:	call   400370 <printf@plt>
  400634:	add    $0xc8,%rsp
  40063b:	xor    %eax,%eax
  40063d:	pop    %rbx
  40063e:	pop    %rbp
  40063f:	pop    %r12
  400641:	pop    %r13
  400643:	pop    %r14
  400645:	pop    %r15
  400647:	ret
  400648:	nopl   0x0(%rax,%rax,1)
  400650:	lea    0x60(%rsp),%rax
  400655:	data16 cs nopw 0x0(%rax,%rax,1)
  400660:	mov    (%rax),%edx
  400662:	test   %edx,%edx
  400664:	jne    4005da <main+0x23a>
  40066a:	add    $0x4,%rax
  40066e:	lea    0x9c(%rsp),%rdx
  400676:	cmp    %rdx,%rax
  400679:	jne    400660 <main+0x2c0>
  40067b:	testl  $0x3fffffff,0x9c(%rsp)
  400686:	je     400583 <main+0x1e3>
  40068c:	jmp    4005da <main+0x23a>
  400691:	cs nopw 0x0(%rax,%rax,1)
  40069b:	nopl   0x0(%rax,%rax,1)

