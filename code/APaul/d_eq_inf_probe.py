from math import gcd
a=[0,0]; ex=[]
for M in (24,32,48,60):
 for A in range(1,M):
  g=gcd(A,M); N=M//g
  for B in range(M):
   L=14*M
   Pt=[(A*k)%M for k in range(L)]; Dst=[(B+M-Pt[k])%M for k in range(L)]
   inf=[M]*(L+1)
   for n in range(1,L+1): inf[n]=min(inf[n-1],Dst[n-1])
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1
   first=True
   while True:
    if not first:
     a[0]+=1
     if d!=inf[min(u+v,L)]:
      a[1]+=1
      if len(ex)<4: ex.append(dict(M=M,A=A,B=B,p=p,q=q,d=d,u=u,v=v,Inf=inf[min(u+v,L)]))
    first=False
    if N<=u+v or p==0 or q==0: break
    if p<q:
     k=q//p; p,q,d,u,v=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d=(d-pn)%q if pn<=d else d; p,q,u,v=pn,q,u,v+k*u
print("d == Inf(u+v), initial config EXCLUDED :",a[0],"checked,",a[1],"violations")
for e in ex: print("   ",e)
