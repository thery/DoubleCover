"""Cut C: when Inf drops in a ge step, is the new minimiser  ymax + j*u
where ymax is the old MAX-distance index?  And which j?"""
from math import gcd
n=0; isform=0; jdist={}
for M in (24,32,45,48,60):
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
    if not first and q<=p and u2+v2<=L and inf[u2+v2]<inf[u+v]:
     n+=1
     ymax=max(range(u+v), key=lambda z: Dst[z])
     am=min(range(u2+v2), key=lambda z: Dst[z])
     if u>0 and (am-ymax)%u==0 and am>=ymax:
       isform+=1; j=(am-ymax)//u; jdist[j]=jdist.get(j,0)+1
    first=False
    p,q,u,v=p2,q2,u2,v2
print(f"ge steps where Inf drops     : {n}")
print(f"  new min = ymax + j*u       : {isform}")
print(f"  distribution of j          : {dict(sorted(jdist.items())[:8])}")
