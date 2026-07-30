from math import gcd
old=0;new=0;bo=0;bn=0
for M in (32,64):
 for A in range(1,M):
  g=gcd(A,M); N=M//g
  for B in range(M):
   Pt=[(A*k)%M for k in range(6*M)]
   Dst=[(B+M-Pt[k])%M for k in range(6*M)]
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1
   for _ in range(3*M):
    if N<=u+v or p==0 or q==0: break
    if p<q: k=q//p; p2,q2,d2,u2,v2=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d2=(d-pn)%q if pn<=d else d; p2,q2,u2,v2=pn,q,u,v+k*u
    for x in range(0,min(u2+v2,6*M)):
     if x<u+v:
      old+=1
      if d2>Dst[x]: bo+=1
     else:
      new+=1
      if d2>Dst[x]: bn+=1
    p,q,d,u,v=p2,q2,d2,u2,v2
print("old indices x<u+v: checked",old,"violations",bo)
print("new indices u+v<=x:  checked",new,"violations",bn)
