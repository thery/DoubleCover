from math import gcd
# L3: for old y < u+v and 1<=m<=k with m*p <= Dst y,  d %% p <= Dst y - m*p ?
r={"alg":[0,0],"anyd":[0,0],"congd":[0,0],"distd":[0,0]}
ex={}
for M in (24,32,48):
 for A in range(1,M):
  g=gcd(A,M); N=M//g
  for B in range(M):
   Pt=[(A*k)%M for k in range(8*M)]
   Dst=[(B+M-Pt[k])%M for k in range(8*M)]
   inf=[M]*(8*M+1)
   for n in range(1,8*M+1): inf[n]=min(inf[n-1],Dst[n-1])
   S=set(Dst[:M])
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1; first=True
   while True:
    if N<=u+v or p==0 or q==0: break
    if p<q:
     k=q//p
     if not first:
      I1=inf[min(u+v,8*M)]
      pairs=[(y,m) for y in range(u+v) for m in range(1,k+1) if m*p<=Dst[y]]
      for (y,m) in pairs:
       tgt=Dst[y]-m*p
       r["alg"][0]+=1
       if d%p>tgt: r["alg"][1]+=1; ex.setdefault("alg",(M,A,B,p,q,u,v,d,y,m,tgt))
       for d0 in range(0,I1+1):
        r["anyd"][0]+=1
        if d0%p>tgt: r["anyd"][1]+=1
        if (d0-I1)%p==0:
         r["congd"][0]+=1
         if d0%p>tgt: r["congd"][1]+=1; ex.setdefault("congd",(M,A,B,p,q,u,v,d0,I1,y,m,tgt))
        if d0 in S:
         r["distd"][0]+=1
         if d0%p>tgt: r["distd"][1]+=1; ex.setdefault("distd",(M,A,B,p,q,u,v,d0,y,m,tgt))
     p2,q2,d2,u2,v2=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d2=(d-pn)%q if pn<=d else d; p2,q2,u2,v2=pn,q,u,v+k*u
    first=False
    p,q,d,u,v=p2,q2,d2,u2,v2
for key,(t,b) in r.items(): print("L3 with %-6s : checked %8d  violations %d"%(key,t,b))
for k,val in ex.items(): print("   first violation",k,val)
