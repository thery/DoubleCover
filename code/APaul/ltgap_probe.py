"""Cut 4 (lt/gap): how does Inf move across a p<q step, and what bounds it?
  A: Inf(u+v) - Inf(u'+v') is a multiple of p ?
  B: the multiplier c, and is c <= q %/ p ?
"""
from math import gcd
n=0; multp=0; cmax=0; cle=0; dist={}
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
     if (I0-I1)%p==0:
       multp+=1; c=(I0-I1)//p
       dist[c]=dist.get(c,0)+1
       cmax=max(cmax,c); cle += (c<=q//p)
    first=False
    p,q,u,v=p2,q2,u2,v2
print(f"lt steps                     : {n}")
print(f"  A  Inf drop is a multiple of p : {multp}")
print(f"  B  c <= q %/ p               : {cle};  max c seen = {cmax}")
print(f"     distribution of c         : {dict(sorted(dist.items())[:8])}")
