"""inf_cong_ge: d' = Inf (u'+v') %[mod p'],  p' = p %% q.

Measure the shape of Inf(new) - d' in the ge branch:
  - is d' <= Inf(new)?          (step_invd_le, now proved)
  - is p' | (Inf(new) - d')?    (the statement)
  - distribution of (Inf(new) - d') / p'
  - how often is Inf(new) = d' outright?
"""
from math import gcd
n=0; le=0; div=0; eq=0; ratios={}; p0=0
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
    if p<q: k=q//p; p2,q2,d2,u2,v2=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q
     d2=(d-pn)%q if pn<=d else d
     p2,q2,u2,v2=pn,q,u,v+k*u
    if not first and q<=p and u2+v2<=L:
     pp=p%q; In=inf[u2+v2]
     n+=1
     le += (d2<=In)
     eq += (d2==In)
     if pp==0: p0+=1
     else:
      if (In-d2)%pp==0: div+=1
      if d2<=In: ratios[(In-d2)//pp]=ratios.get((In-d2)//pp,0)+1
    first=False
    p,q,d,u,v=p2,q2,d2,u2,v2
print(f"ge steps                     : {n}")
print(f"  d' <= Inf(new)             : {le}")
print(f"  d' == Inf(new)             : {eq}")
print(f"  p' = 0 (q divides p)       : {p0}")
print(f"  p' | (Inf(new) - d')       : {div}  (of {n-p0} with p'>0)")
print(f"  (Inf(new)-d')/p' distrib   : {dict(sorted(ratios.items()))}")
