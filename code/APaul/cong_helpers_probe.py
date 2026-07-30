from math import gcd
r={"first_ge":[0,0],"cong_lt":[0,0],"cong_ge":[0,0]}; ex={}
for M in (24,32,48):
 for A in range(1,M):
  g=gcd(A,M); N=M//g
  for B in range(M):
   Pt=[(A*k)%M for k in range(10*M)]
   Dst=[(B+M-Pt[k])%M for k in range(10*M)]
   inf=[M]*(10*M+1)
   for n in range(1,10*M+1): inf[n]=min(inf[n-1],Dst[n-1])
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1; first=True
   while True:
    if N<=u+v or p==0 or q==0: break
    if p<q: k=q//p; p2,q2,d2,u2,v2=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d2=(d-pn)%q if pn<=d else d; p2,q2,u2,v2=pn,q,u,v+k*u
    I2=inf[min(u2+v2,10*M)]
    if first:
     r["first_ge"][0]+=1
     if not I2<=d2: r["first_ge"][1]+=1; ex.setdefault("first_ge",(M,A,B,d2,I2))
    else:
     if p<q:
      r["cong_lt"][0]+=1
      if (I2-inf[min(u+v,10*M)])%p!=0:
       r["cong_lt"][1]+=1; ex.setdefault("cong_lt",(M,A,B,p,q,u,v,I2,inf[min(u+v,10*M)]))
     else:
      r["cong_ge"][0]+=1
      if p2>0 and (d2-I2)%p2!=0:
       r["cong_ge"][1]+=1; ex.setdefault("cong_ge",(M,A,B,p,q,u,v,d2,I2,p2))
    first=False
    p,q,d,u,v=p2,q2,d2,u2,v2
for k2,(t,b) in r.items(): print("%-9s checked %7d  violations %d"%(k2,t,b))
for k2,val in ex.items(): print("   first violation",k2,val)
