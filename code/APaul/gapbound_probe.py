"""Strengthened invx_gap: can the decomposition always be chosen with
   a <= u  and  b <= v ?   (u gaps of size p, v gaps of size q, M = u*p+v*q)

Also: in the ge tight-wrap case, is the coefficient a then forced into
{u-1, u} -- which is exactly what step 3 needs?
"""
from math import gcd
tot=ok=0; ex=[]
tight_tot=0; tight_au={}
for M in (24,32,45,48,60,64):
 for A in range(1,M):
  g=gcd(A,M); N=M//g; L=26*M
  Pt=[(A*k)%M for k in range(L)]
  for B in range(M):
   Dst=[(B+M-Pt[k])%M for k in range(L)]
   inf=[M]*(L+1)
   for n in range(1,L+1): inf[n]=min(inf[n-1],Dst[n-1])
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1; first=True
   while u+v<N and p>0 and q>0:
    if not first:
     I=inf[u+v]
     for y in range(u+v):
      tot+=1
      found=None
      for a in range(u+1):
       for b in range(v+1):
        if I+a*p+b*q==Dst[y]: found=(a,b); break
       if found: break
      if found: ok+=1
      elif len(ex)<4: ex.append(dict(M=M,A=A,B=B,p=p,q=q,u=u,v=v,y=y,
                                     Dst=Dst[y],Inf=I))
      # step-3 relevant: ge branch, tight wrap
      if q<=p and found:
       a,_=found
       for m in range(1,p//q+1):
        if M<=Dst[y]+m*q and Dst[y]+m*q-M<q:
         tight_tot+=1
         tight_au[a-u]=tight_au.get(a-u,0)+1
    first=False
    if p<q: k=q//p; p,q,d,u,v=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d=(d-pn)%q if pn<=d else d; p,q,u,v=pn,q,u,v+k*u
print(f"decomposition with a<=u, b<=v exists : {ok}/{tot}")
for e in ex: print("   ", e)
print(f"tight ge-wrap cases: {tight_tot},  distribution of (a-u): {dict(sorted(tight_au.items()))}")
