"""ge_wrap_au, AS STATED -- quantified over EVERY valid b, not just one:

  q<=p, y<u+v, 0<m<=p%/q, b<=v,
  Dst y = Inf (u+v) + u*p + b*q,
  M <= Dst y + m*q,  Dst y + m*q - M < q
  ==> v <= b+m

Also reports how often the decomposition is non-unique, which is the
thing my earlier probe could have missed.
"""
from math import gcd
n=0; bad=0; multi=0; ex=[]
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
      # EVERY b with b<=v and Dst y = I + u*p + b*q
      bs=[b for b in range(v+1) if I+u*p+b*q==Dst[y]]
      if len(bs)>1: multi+=1
      for b in bs:
       for m in range(1,p//q+1):
        if M<=Dst[y]+m*q and Dst[y]+m*q-M<q:
         n+=1
         if not v<=b+m:
          bad+=1
          if len(ex)<4: ex.append(dict(M=M,A=A,B=B,p=p,q=q,u=u,v=v,y=y,m=m,b=b,I=I))
    first=False
    if p<q: k=q//p; p,q,d,u,v=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d=(d-pn)%q if pn<=d else d; p,q,u,v=pn,q,u,v+k*u
print(f"ge_wrap_au as stated : {n} instances, {bad} violations")
print(f"non-unique decompositions encountered: {multi}")
for e in ex: print("   ", e)
