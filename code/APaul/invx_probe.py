from math import gcd
r={"pmin":[0,0],"pmax":[0,0]}
ex={}
for M in (24,32,48):
 for A in range(1,M):
  g=gcd(A,M); N=M//g
  Pt=[(A*k)%M for k in range(8*M)]
  p,q,u,v=A%M,M-(A%M),1,1
  while True:
   if N<=u+v or p==0 or q==0: break
   n=u+v-1   # configuration is {Pt m : m <= n}
   r["pmin"][0]+=1
   if any(0<m<=n and Pt[m]<p for m in range(0,n+1)):
    r["pmin"][1]+=1; ex.setdefault("pmin",(M,A,p,q,u,v,[Pt[m] for m in range(n+1)]))
   r["pmax"][0]+=1
   if any(m<=n and Pt[m]>M-q for m in range(0,n+1)):
    r["pmax"][1]+=1; ex.setdefault("pmax",(M,A,p,q,u,v,[Pt[m] for m in range(n+1)]))
   if p<q: k=q//p; p,q,u,v=p,q-k*p,u+k*v,v
   else:
    k=p//q; p,q,u,v=p-k*q,q,u,v+k*u
print("p = min {Pt m : 0<m<=u+v-1}  : states",r["pmin"][0]," violations",r["pmin"][1])
print("M-q = max {Pt m : m<=u+v-1}  : states",r["pmax"][0]," violations",r["pmax"][1])
for k,val in ex.items(): print("   first violation",k,val[:6])
