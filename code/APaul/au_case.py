"""Tight ge-wrap cases, split by a-u.  For a = u, does Inf <= W hold
(equivalently b+m >= v), which would close that branch immediately?"""
from math import gcd
cnt={}; au_n=0; au_IleW=0; au_Iltq=0; ex=[]
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
     I=inf[u+v]
     for y in range(u+v):
      dec=None
      for a in range(u+1):
       for b in range(v+1):
        if I+a*p+b*q==Dst[y]: dec=(a,b); break
       if dec: break
      if dec is None: continue
      a,b=dec
      for m in range(1,p//q+1):
       if M<=Dst[y]+m*q and Dst[y]+m*q-M<q:
        W=Dst[y]+m*q-M
        cnt[a-u]=cnt.get(a-u,0)+1
        if a==u:
         au_n+=1
         au_IleW += (I<=W)
         au_Iltq += (I<q)
         if I>W and len(ex)<4:
          ex.append(dict(M=M,A=A,B=B,p=p,q=q,u=u,v=v,y=y,m=m,a=a,b=b,I=I,W=W))
    first=False
    if p<q: k=q//p; p,q,d,u,v=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d=(d-pn)%q if pn<=d else d; p,q,u,v=pn,q,u,v+k*u
print("tight ge-wrap, distribution of a-u:", dict(sorted(cnt.items())))
print(f"a = u cases: {au_n},  Inf <= W: {au_IleW},  Inf < q: {au_Iltq}")
for e in ex: print("   Inf > W:", e)
