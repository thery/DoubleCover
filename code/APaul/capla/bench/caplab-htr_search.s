00000000004011a0 <htr_search>:
  4011a0:	sub    $0xa8,%rsp
  4011a7:	lea    0xb0(%rsp),%rax
  4011af:	mov    %rax,(%rsp)
  4011b3:	mov    %rbx,0x8(%rsp)
  4011b8:	mov    %rbp,0x10(%rsp)
  4011bd:	mov    %r12,0x18(%rsp)
  4011c2:	mov    %r13,0x20(%rsp)
  4011c7:	mov    %r14,0x28(%rsp)
  4011cc:	mov    %r15,0x30(%rsp)
  4011d1:	mov    (%rax),%r10
  4011d4:	mov    %r10,0x40(%rsp)
  4011d9:	mov    %r9,0xa0(%rsp)
  4011e1:	mov    %r8,0x70(%rsp)
  4011e6:	mov    %rcx,0x98(%rsp)
  4011ee:	mov    %rdx,0x48(%rsp)
  4011f3:	mov    0x70(%rsp),%r9
  4011f8:	mov    %r9,0x88(%rsp)
  401200:	mov    0x40(%rsp),%rcx
  401205:	mov    %rcx,%r14
  401208:	mov    %rsi,0x90(%rsp)
  401210:	mov    %rdi,%rbp
  401213:	mov    $0x4,%esi
  401218:	mov    0x40(%rsp),%rdi
  40121d:	call   4003a0 <calloc@plt>
  401222:	mov    %rax,0x38(%rsp)
  401227:	mov    0x38(%rsp),%rdi
  40122c:	cmp    $0x0,%rdi
  401230:	je     4014a3 <htr_search+0x303>
  401236:	mov    0x40(%rsp),%r11
  40123b:	mov    %r11,0x80(%rsp)
  401243:	mov    $0x4,%esi
  401248:	mov    0x80(%rsp),%rdi
  401250:	call   4003a0 <calloc@plt>
  401255:	mov    %rax,0x58(%rsp)
  40125a:	mov    0x58(%rsp),%rdx
  40125f:	cmp    $0x0,%rdx
  401263:	je     4014a3 <htr_search+0x303>
  401269:	mov    0x40(%rsp),%r10
  40126e:	mov    %r10,0x60(%rsp)
  401273:	mov    $0x4,%esi
  401278:	mov    0x60(%rsp),%rdi
  40127d:	call   4003a0 <calloc@plt>
  401282:	mov    %rax,0x50(%rsp)
  401287:	mov    0x50(%rsp),%rsi
  40128c:	cmp    $0x0,%rsi
  401290:	je     4014a3 <htr_search+0x303>
  401296:	mov    0x40(%rsp),%rsi
  40129b:	cmp    %r14,%rsi
  40129e:	jne    4014a3 <htr_search+0x303>
  4012a4:	mov    0x48(%rsp),%rdi
  4012a9:	call   400aa0 <init_coeffs>
  4012ae:	xor    %r13,%r13
  4012b1:	xor    %r15,%r15
  4012b4:	mov    0x90(%rsp),%rdi
  4012bc:	cmp    %rdi,%rbp
  4012bf:	jge    40144d <htr_search+0x2ad>
  4012c5:	lea    0x0(%rbp),%rdi
  4012c9:	add    0xfc8(%rip),%rdi        # 402298 <__dso_handle+0x8>
  4012d0:	mov    0x40(%rsp),%r8
  4012d5:	mov    0x40(%rsp),%rcx
  4012da:	mov    0x60(%rsp),%rax
  4012df:	cmp    %rcx,%r8
  4012e2:	jne    4014a3 <htr_search+0x303>
  4012e8:	cmp    %r14,%r8
  4012eb:	jne    4014a3 <htr_search+0x303>
  4012f1:	cmp    %rax,%r8
  4012f4:	jne    4014a3 <htr_search+0x303>
  4012fa:	mov    0x50(%rsp),%rcx
  4012ff:	mov    0x48(%rsp),%rdx
  401304:	mov    0x38(%rsp),%rsi
  401309:	call   4008d0 <poly_eval>
  40130e:	mov    $0x226,%esi
  401313:	mov    0x40(%rsp),%rdx
  401318:	mov    0x40(%rsp),%rdi
  40131d:	cmp    %rdi,%rdx
  401320:	jne    4014a3 <htr_search+0x303>
  401326:	mov    0x38(%rsp),%rdi
  40132b:	call   401120 <big_bits64>
  401330:	lea    0x20000000(%rax),%rbx
  401337:	mov    $0x1e1,%esi
  40133c:	mov    0x40(%rsp),%rdx
  401341:	mov    0x40(%rsp),%r11
  401346:	cmp    %r11,%rdx
  401349:	jne    4014a3 <htr_search+0x303>
  40134f:	mov    0x38(%rsp),%rdi
  401354:	call   401120 <big_bits64>
  401359:	lea    (%rax,%rbx,1),%r12
  40135d:	mov    $0x217,%esi
  401362:	mov    0x40(%rsp),%rdx
  401367:	mov    0x40(%rsp),%rcx
  40136c:	cmp    %rcx,%rdx
  40136f:	jne    4014a3 <htr_search+0x303>
  401375:	mov    0x38(%rsp),%rdi
  40137a:	call   401120 <big_bits64>
  40137f:	mov    %rax,0x78(%rsp)
  401384:	lea    0x0(,%rbx,2),%r10
  40138c:	mov    %r10,0x68(%rsp)
  401391:	xor    %rbx,%rbx
  401394:	mov    0x68(%rsp),%r9
  401399:	cmp    %r9,%r12
  40139c:	jae    401427 <htr_search+0x287>
  4013a2:	lea    0x1(%r13),%r13
  4013a6:	lea    0x0(%rbp,%rbx,1),%rdi
  4013ab:	mov    0x40(%rsp),%r8
  4013b0:	mov    0x80(%rsp),%r9
  4013b8:	mov    %r9,%rdx
  4013bb:	mov    0x60(%rsp),%rcx
  4013c0:	mov    %rcx,%r10
  4013c3:	cmp    %r14,%r8
  4013c6:	jne    4014a3 <htr_search+0x303>
  4013cc:	cmp    %rdx,%r8
  4013cf:	jne    4014a3 <htr_search+0x303>
  4013d5:	cmp    %rcx,%r8
  4013d8:	jne    4014a3 <htr_search+0x303>
  4013de:	mov    0x50(%rsp),%rcx
  4013e3:	mov    0x58(%rsp),%rdx
  4013e8:	mov    0x48(%rsp),%rsi
  4013ed:	call   4014b0 <is_hard>
  4013f2:	cmp    $0x0,%eax
  4013f5:	je     401427 <htr_search+0x287>
  4013f7:	mov    0x70(%rsp),%r8
  4013fc:	cmp    %r8,%r15
  4013ff:	jae    401423 <htr_search+0x283>
  401401:	mov    0x88(%rsp),%rsi
  401409:	cmp    %rsi,%r15
  40140c:	jae    4014a3 <htr_search+0x303>
  401412:	lea    0x0(%rbp,%rbx,1),%rax
  401417:	mov    0x98(%rsp),%r11
  40141f:	mov    %rax,(%r11,%r15,8)
  401423:	lea    0x1(%r15),%r15
  401427:	mov    0x78(%rsp),%rdx
  40142c:	lea    (%r12,%rdx,1),%r12
  401430:	lea    0x1(%rbx),%rbx
  401434:	cmp    $0x100000,%rbx
  40143b:	jb     401394 <htr_search+0x1f4>
  401441:	lea    0x100000(%rbp),%rbp
  401448:	jmp    4012b4 <htr_search+0x114>
  40144d:	mov    0xa0(%rsp),%rax
  401455:	mov    %r13,(%rax)
  401458:	mov    %r15,0x8(%rax)
  40145c:	mov    0x38(%rsp),%rdi
  401461:	call   400370 <free@plt>
  401466:	mov    0x58(%rsp),%rdi
  40146b:	call   400370 <free@plt>
  401470:	mov    0x50(%rsp),%rdi
  401475:	call   400370 <free@plt>
  40147a:	mov    %r15,%rax
  40147d:	mov    0x8(%rsp),%rbx
  401482:	mov    0x10(%rsp),%rbp
  401487:	mov    0x18(%rsp),%r12
  40148c:	mov    0x20(%rsp),%r13
  401491:	mov    0x28(%rsp),%r14
  401496:	mov    0x30(%rsp),%r15
  40149b:	add    $0xa8,%rsp
  4014a2:	ret
  4014a3:	call   400380 <abort@plt>
  4014a8:	jmp    4014a3 <htr_search+0x303>
  4014aa:	nopw   0x0(%rax,%rax,1)

