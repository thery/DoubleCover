"""ge/inf, the RIGHT mirror.  The lt branch has Inf(new) = Inf(old) %% p with
p the MIN gap; in the ge branch the min gap is q, not p %% q.  The refuted
statement used p %% q.  Test the min-gap version:

  E : Inf(new) = Inf(old) %% q
  F : Inf(new) >= Inf(old) %% q     (the half that gives ge/inf: < q)
  G : Inf(new) <= Inf(old) %% q
"""
from math import gcd
n=0; E=0; F=0; G=0; ex=[]
for M in (24,32,45,48,60,64):
 for A in range(1,M):
  g=gcd(A,M); N=M//g; L=26*M
  Pt=[(A*k)%M for k in range(L)]
  for B in range(M):
   Dst=[(B+M-Pt[k])%M for k in range(L)]
   inf=[M]*(L+1)
   for k2 in range(1,L+1): inf[k2]=min(inf[k2-1],Dst[k2-1])
   p,q,u,v=A%M,M-(A%M),1,1; first=True
   while u+v<N and p>0 and q>0:
    if p<q: k=q//p; p2,q2,u2,v2=p,q-k*p,u+k*v,v
    else:   k=p//q; p2,q2,u2,v2=p-k*q,q,u,v+k*u
    if not first and q<=p and u2+v2<=L and u2+v2<N:
     I0=inf[u+v]; I1=inf[u2+v2]; n+=1
     E += (I1==I0%q); F += (I1>=I0%q); G += (I1<=I0%q)
     if I1!=I0%q and len(ex)<5:
       ex.append(dict(M=M,A=A,B=B,p=p,q=q,u=u,v=v,k=k,I0=I0,I1=I1,mod=I0%q))
    first=False
    p,q,u,v=p2,q2,u2,v2
print(f"ge steps                  : {n}")
print(f"  E Inf(new) == Inf %% q  : {E}")
print(f"  F Inf(new) >= Inf %% q  : {F}")
print(f"  G Inf(new) <= Inf %% q  : {G}")
for e in ex: print("   E fails:", e)
