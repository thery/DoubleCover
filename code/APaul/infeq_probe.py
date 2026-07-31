"""Cut B slot 1: is Inf(u'+v') = Inf(u+v) %% p in the p<q branch?
(<= is the proved inf_new_lt_le; the >= is the question.)
Also: when Inf(new) is attained at a NEW index, what is that index's
distance relative to Inf(old) %% p ?
"""
from math import gcd
n=0; eq=0; ge=0; ex=[]
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
    if not first and p<q and u2+v2<=L:
     I0=inf[u+v]; I1=inf[u2+v2]; n+=1
     eq += (I1==I0%p); ge += (I1>=I0%p)
     if I1!=I0%p and len(ex)<3:
       ex.append(dict(M=M,A=A,B=B,p=p,q=q,u=u,v=v,I0=I0,I1=I1,mod=I0%p))
    first=False
    p,q,u,v=p2,q2,u2,v2
print(f"lt steps                    : {n}")
print(f"  Inf(new) = Inf(old) %% p  : {eq}")
print(f"  Inf(new) >= Inf(old) %% p : {ge}")
for e in ex: print("   ", e)
