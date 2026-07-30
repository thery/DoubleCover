from math import gcd
c1=[0,0]; c2=[0,0]; ex={}
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
    if not first and q<=p and p2>0:
     I1=inf[min(u+v,L)]; I2=inf[min(u2+v2,L)]
     c1[0]+=1
     if I2%p2!=I1%p2: c1[1]+=1; ex.setdefault("C1",(M,A,B,p,q,d,u,v,I1,I2,I1%p2))
     c2[0]+=1
     if d2%p2!=I2%p2: c2[1]+=1; ex.setdefault("C2",(M,A,B,p,q,d,u,v,d2,I2,p2))
    first=False
    p,q,d,u,v=p2,q2,d2,u2,v2
print("C1  Inf(new) == Inf(u+v) mod",("p%%q"),"  :",c1[0],"checked,",c1[1],"violations")
print("C2  d2 == Inf(new) mod (p mod q)  [the goal]:",c2[0],"checked,",c2[1],"violations")
for k2,val in ex.items(): print("  ",k2,"first violation",val)
