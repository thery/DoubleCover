from math import gcd
c={"isdist":0,"isdist_bad":0,"cong":0,"cong_bad":0}
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
    if p<q: k=q//p; p2,q2,d2,u2,v2=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d2=(d-pn)%q if pn<=d else d; p2,q2,u2,v2=pn,q,u,v+k*u
    if not first:
     c["isdist"]+=1
     if d not in S: c["isdist_bad"]+=1; ex.setdefault("isdist",(M,A,B,p,q,u,v,d))
     c["cong"]+=1
     if (d-inf[min(u+v,8*M)])%p!=0:
      c["cong_bad"]+=1; ex.setdefault("cong",(M,A,B,p,q,u,v,d,inf[min(u+v,8*M)]))
    first=False
    p,q,d,u,v=p2,q2,d2,u2,v2
print("d is a genuine distance (some index < M):  checked",c["isdist"]," bad",c["isdist_bad"])
print("p divides (d - Inf(u+v))                :  checked",c["cong"]," bad",c["cong_bad"])
for k,val in ex.items(): print("   first bad",k,val)
