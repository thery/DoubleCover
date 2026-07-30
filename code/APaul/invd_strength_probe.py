from math import gcd
# is  d0 <= Inf(u+v)  ENOUGH to give  d0 %% p <= Inf(u+k*v+v)  ?
# quantify over ALL d0 <= Inf(u+v), not just the algorithm value.
bad=[];tot=0
for M in (24,32,48):
 for A in range(1,M):
  g=gcd(A,M); N=M//g
  for B in range(M):
   Pt=[(A*k)%M for k in range(8*M)]
   Dst=[(B+M-Pt[k])%M for k in range(8*M)]
   inf=[M]*(8*M+1)
   for n in range(1,8*M+1): inf[n]=min(inf[n-1],Dst[n-1])
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1; first=True
   while True:
    if N<=u+v or p==0 or q==0: break
    if p<q:
     k=q//p; p2,q2,d2,u2,v2=p,q-k*p,d%p,u+k*v,v
     if not first:
      I1=inf[min(u+v,8*M)]; I2=inf[min(u2+v2,8*M)]
      for d0 in range(0,I1+1):
       tot+=1
       if d0%p>I2: bad.append((M,A,B,p,q,u,v,d0,I1,I2))
    else:
     k=p//q; pn=p-k*q; d2=(d-pn)%q if pn<=d else d; p2,q2,u2,v2=pn,q,u,v+k*u
    first=False
    p,q,d,u,v=p2,q2,d2,u2,v2
print("arbitrary d0 <= Inf(u+v):  checked",tot," counterexamples",len(bad))
for r in bad[:5]: print("   M=%d A=%d B=%d p=%d q=%d u=%d v=%d d0=%d Inf(u+v)=%d Inf(new)=%d"%r)
