"""Step 3, stated directly:

  ge branch, wrap case, W := Dst y + m*q - M, W < q
  =>  W = d'  \/  W = d' + p'      (p' := p %% q)

Also re-checks the two facts it sits on:  d' < q, and (q <= W -> d' <= W).
"""
from math import gcd
n=eq=shift=other=0
dq_n=dq_ok=0
big_n=big_ok=0
ex=[]
for M in (24,32,45,48,60,64,81,100):
 for A in range(1,M):
  g=gcd(A,M); N=M//g; L=26*M
  Pt=[(A*k)%M for k in range(L)]
  for B in range(M):
   Dst=[(B+M-Pt[k])%M for k in range(L)]
   p,q,d,u,v=A%M,M-(A%M),B%M,1,1; first=True
   while u+v<N and p>0 and q>0:
    if not first and q<=p:
     pp=p%q
     dn=(d-pp)%q if pp<=d else d
     dq_n+=1; dq_ok+=(dn<q)
     for y in range(u+v):
      for m in range(1,p//q+1):
       if M<=Dst[y]+m*q:
        W=Dst[y]+m*q-M
        if W<q:
         n+=1
         if W==dn: eq+=1
         elif W==dn+pp: shift+=1
         else:
          other+=1
          if len(ex)<4: ex.append(dict(M=M,A=A,B=B,p=p,q=q,d=d,u=u,v=v,
                                       y=y,m=m,W=W,dp=dn,pp=pp))
        else:
         big_n+=1; big_ok+=(dn<=W)
    first=False
    if p<q: k=q//p; p,q,d,u,v=p,q-k*p,d%p,u+k*v,v
    else:
     k=p//q; pn=p-k*q; d=(d-pn)%q if pn<=d else d; p,q,u,v=pn,q,u,v+k*u
print(f"d' < q                      : {dq_ok}/{dq_n}")
print(f"W >= q  ->  d' <= W         : {big_ok}/{big_n}")
print(f"tight W < q                 : {n}")
print(f"   W = d'                   : {eq}")
print(f"   W = d' + p'              : {shift}")
print(f"   NEITHER (violations)     : {other}")
for e in ex: print("   ", e)
