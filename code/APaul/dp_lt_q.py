"""In ge states (q <= p), with d = Inf:
   X: Inf < q ?
   Y: d' + p' < q ?      (what the a = u case needs)
   Z: Inf < q + p' ?     (weaker, would give d' = Inf - p' directly)
"""
from math import gcd
n=0; X=0; Y=0; Z=0; exY=[]
for M in (24,32,45,48,60,64):
 for A in range(1,M):
  g=gcd(A,M); N=M//g; L=26*M
  Pt=[(A*k)%M for k in range(L)]
  for B in range(M):
   Dst=[(B+M-Pt[k])%M for k in range(L)]
   inf=[M]*(L+1)
   for k2 in range(1,L+1): inf[k2]=min(inf[k2-1],Dst[k2-1])
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1; first=True
   while u+v<N and p>0 and q>0:
    if not first and q<=p:
     I=inf[u+v]; pp=p%q
     dn=(d-pp)%q if pp<=d else d
     n+=1
     X += (I<q)
     Y += (dn+pp<q)
     Z += (I<q+pp)
     if not (dn+pp<q) and len(exY)<4:
      exY.append(dict(M=M,A=A,B=B,p=p,q=q,d=d,I=I,pp=pp,dn=dn,u=u,v=v))
    first=False
    if p<q: k=q//p; p,q,d,u,v=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d=(d-pn)%q if pn<=d else d; p,q,u,v=pn,q,u,v+k*u
print(f"ge states                 : {n}")
print(f"  X  Inf < q              : {X}")
print(f"  Y  d' + p' < q          : {Y}")
print(f"  Z  Inf < q + p'         : {Z}")
for e in exY: print("   Y counterexample:", e)
