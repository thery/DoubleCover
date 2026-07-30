from math import gcd
eq=0; le=0; tot=0; badle=0
for M in (32,64):
 for A in range(1,M):
  g=gcd(A,M)
  for B in range(M):
   N=M//g
   Pt=[(A*k)%M for k in range(4*M)]
   Dst=[(B+M-Pt[k])%M for k in range(4*M)]
   inf=[M]*(4*M+1)
   for n in range(1,4*M+1): inf[n]=min(inf[n-1],Dst[n-1])
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1
   for _ in range(3*M):
    if N<=u+v or p==0 or q==0: break
    if p<q: k=q//p; p2,q2,d2,u2,v2=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d2=(d-pn)%q if pn<=d else d; p2,q2,u2,v2=pn,q,u,v+k*u
    n2=min(u2+v2,4*M)
    tot+=1
    if d2==inf[n2]: eq+=1
    if d2<=inf[n2]: le+=1
    else: badle+=1
    p,q,d,u,v=p2,q2,d2,u2,v2
print("steps",tot," d2 == Inf(u2+v2):",eq," d2 <= Inf:",le," violations of <=:",badle)
