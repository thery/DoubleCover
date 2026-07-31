"""ge/inf: what happens to Inf across a q<=p step?

  A: does Inf actually drop?          Inf(u'+v') < Inf(u+v) ?
  B: is the new minimiser a NEW index (>= u+v)?
  C: the target itself: Inf(u'+v') < q  (= maxn p' q since p%%q < q)
  D: is the drop a multiple of q?
"""
from math import gcd
n=0; drop=0; newmin=0; tgt=0; multq=0; ex=[]
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
    if not first and q<=p and u2+v2<=L:
     I0=inf[u+v]; I1=inf[u2+v2]
     n+=1
     drop += (I1<I0)
     tgt  += (I1<q)
     if I1<I0:
       # is the argmin a new index?
       am=min(range(u2+v2), key=lambda z: Dst[z])
       newmin += (am>=u+v)
       if q>0 and (I0-I1)%q==0: multq+=1
     if not (I1<q) and len(ex)<3:
       ex.append(dict(M=M,A=A,B=B,p=p,q=q,u=u,v=v,I0=I0,I1=I1))
    first=False
    p,q,u,v=p2,q2,u2,v2
print(f"ge steps                       : {n}")
print(f"  A  Inf drops                 : {drop}")
print(f"  B  new minimiser is a new ix : {newmin} (of the {drop} drops)")
print(f"  C  Inf(new) < q  (the goal)  : {tgt}")
print(f"  D  drop is a multiple of q   : {multq} (of the {drop} drops)")
for e in ex: print("   C fails:", e)
