from math import gcd
tot=0; wrap=0; ex=[]
for M in (24,32,48):
 for A in range(1,M):
  g=gcd(A,M); N=M//g
  for B in range(M):
   L=14*M
   Pt=[(A*k)%M for k in range(L)]; Dst=[(B+M-Pt[k])%M for k in range(L)]
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1
   while True:
    if q<=p and q>0:
     for y in range(min(u+v,L)):
      for m in range(1,p//q+1):
       tot+=1
       if Dst[y]+m*q>=M:
        wrap+=1
        if len(ex)<3: ex.append(dict(M=M,A=A,B=B,p=p,q=q,d=d,u=u,v=v,y=y,m=m,Dst=Dst[y],sum=Dst[y]+m*q))
    if N<=u+v or p==0 or q==0: break
    if p<q:
     k=q//p; p,q,d,u,v=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d=(d-pn)%q if pn<=d else d; p,q,u,v=pn,q,u,v+k*u
print("ge branch: M <= Dst y + m*q happens in",wrap,"of",tot,"cases")
for e in ex: print("   ",e)
