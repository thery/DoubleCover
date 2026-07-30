from math import gcd
# EXACT statements of the four axioms.
r={"lt_at":[0,0],"ge":[0,0],"first_cong":[0,0],"step_cong":[0,0]}
ex={}
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
    # invd_first_cong / step_invd_cong : d2 = Inf(u2+v2) mod p2
    key="first_cong" if first else "step_cong"
    r[key][0]+=1
    if p2>0 and (d2-inf[min(u2+v2,10*M)])%p2!=0:
     r[key][1]+=1; ex.setdefault(key,(M,A,B,p,q,d,u,v,p2,d2,inf[min(u2+v2,10*M)]))
    if not first:
     if p<q:
      # step_invd_le_new_lt_at : ALL y<u+v, 0<m<=k
      for y in range(u+v):
       for m in range(1,k+1):
        r["lt_at"][0]+=1
        if not (d%p)<=Dst[min(y+m*v,10*M-1)]:
         r["lt_at"][1]+=1; ex.setdefault("lt_at",(M,A,B,p,q,d,u,v,y,m))
     else:
      pn=p-(p//q)*q; dd=(d-pn)%q if pn<=d else d
      for x in range(u+v,min(u+(v+(p//q)*u),10*M)):
       r["ge"][0]+=1
       if not dd<=Dst[x]: r["ge"][1]+=1; ex.setdefault("ge",(M,A,B,p,q,d,u,v,x))
    first=False
    p,q,d,u,v=p2,q2,d2,u2,v2
for k2,(t,b) in r.items(): print("%-12s checked %8d  violations %d"%(k2,t,b))
for k2,val in ex.items(): print("   first violation",k2,val)
