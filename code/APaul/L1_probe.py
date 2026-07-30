"""Candidate single leaf for le_ge_wrap's tight case, stated WITHOUT any
reference to a decomposition (so the probe and the lemma quantify alike):

  ge branch, y < u+v, 0 < m <= p%/q, M <= Dst y + m*q, W := Dst y+m*q-M < q
  ==>   Inf (u+v) <= W   \/   W = d'

Either disjunct gives d' <= W, since d' <= d = Inf (u+v) in the ge branch
(step_ge_d_le + ge_d_eq_inf).
"""
from math import gcd
n=0; bad=0; d1=0; d2=0; ex=[]
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
     for y in range(u+v):
      for m in range(1,p//q+1):
       if M<=Dst[y]+m*q:
        W=Dst[y]+m*q-M
        if W<q:
         n+=1
         a1 = (I<=W); a2 = (W==dn)
         if a1: d1+=1
         if a2: d2+=1
         if not (a1 or a2):
          bad+=1
          if len(ex)<4: ex.append(dict(M=M,A=A,B=B,p=p,q=q,d=d,u=u,v=v,y=y,m=m,W=W,dn=dn,I=I))
    first=False
    if p<q: k=q//p; p,q,d,u,v=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d=(d-pn)%q if pn<=d else d; p,q,u,v=pn,q,u,v+k*u
print(f"tight ge-wrap instances : {n}")
print(f"  Inf <= W                : {d1}")
print(f"  W = d'                  : {d2}")
print(f"  NEITHER (violations)    : {bad}")
for e in ex: print("   ", e)
