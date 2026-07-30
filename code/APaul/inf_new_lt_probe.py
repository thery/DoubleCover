from math import gcd
a=[0,0]; ex={}
for M in (24,32,48):
 for A in range(1,M):
  g=gcd(A,M); N=M//g
  for B in range(M):
   L=12*M; Pt=[(A*k)%M for k in range(L)]; Dst=[(B+M-Pt[k])%M for k in range(L)]
   inf=[M]*(L+1)
   for n in range(1,L+1): inf[n]=min(inf[n-1],Dst[n-1])
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1; first=True
   while True:
    if N<=u+v or p==0 or q==0: break
    if p<q: k=q//p; p2,q2,d2,u2,v2=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d2=(d-pn)%q if pn<=d else d; p2,q2,u2,v2=pn,q,u,v+k*u
    if not first and p<q:
     I1=inf[min(u+v,L)]; I2=inf[min(u2+v2,L)]
     a[0]+=1
     if I2!=I1%p: a[1]+=1; ex.setdefault("e",(M,A,B,p,q,u,v,I1,I2,I1%p))
    first=False
    p,q,d,u,v=p2,q2,d2,u2,v2
print("candidate  Inf(new) = Inf(u+v) %% p  :  checked",a[0]," violations",a[1])
for k2,val in ex.items(): print("   first violation",val)
