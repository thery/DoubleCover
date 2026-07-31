"""Cut B: does the naive count c + a0 + b0*k stay <= u' = u + k*v ?
   Cut C: for NEW indices, is Dst >= Inf(old) %% p ?"""
from math import gcd
bn=0; bok=0; bexcess=0; cn=0; cok=0
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
    if not first and p<q and u2+v2<=L:
     I0=inf[u+v]; I1=inf[u2+v2]; c=(I0-I1)//p if (I0-I1)%p==0 else None
     # Cut B: for each old y, the minimal decomposition (a0,b0)
     if c is not None:
      for y in range(u+v):
       dec=None
       for a0 in range(u+1):
        for b0 in range(v+1):
         if I0+a0*p+b0*q==Dst[y]: dec=(a0,b0); break
        if dec: break
       if dec:
        a0,b0=dec; bn+=1
        ap=c+a0+b0*k
        if ap<=u2: bok+=1
        else: bexcess=max(bexcess,ap-u2)
     # Cut C: new indices
     for x in range(u+v,min(u2+v2,L)):
      cn+=1; cok += (Dst[x]>=I0%p)
    first=False
    p,q,u,v=p2,q2,u2,v2
print(f"Cut B  naive count c+a0+b0*k <= u' : {bok}/{bn}   worst excess {bexcess}")
print(f"Cut C  new-index Dst >= Inf %% p   : {cok}/{cn}")
