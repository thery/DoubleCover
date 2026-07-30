"""The paper's invariant, in index form (from slater's get_nextDmin/get_nextDmax):

  P1: forall z < u,            Pt (z + v) = Pt z + p          (gap p, no wrap)
  P2: forall z, u <= z < u+v,  Pt z + q   = Pt (z - u) + M    (gap q, wraps)

i.e. the u+v points cut the circle into exactly u gaps of length p and
v gaps of length q -- "u et v contiennent le nombre d'intervalles de
longueurs respectives x et y" (Lefevre, these, 2.4).
"""
from math import gcd
n1=b1=0; n2=b2=0; states=0
ex1=[]; ex2=[]
for M in (24,32,45,48,60,64):
 for A in range(1,M):
  g=gcd(A,M); N=M//g
  Pt=lambda k: (A*k)%M
  p,q,u,v=A%M,M-(A%M),1,1
  first=True
  while u+v<N and p>0 and q>0:
   states+=1
   for z in range(u):
    n1+=1
    if Pt(z+v)!=Pt(z)+p:
     b1+=1
     if len(ex1)<3: ex1.append(dict(M=M,A=A,p=p,q=q,u=u,v=v,z=z,lhs=Pt(z+v),rhs=Pt(z)+p))
   for z in range(u,u+v):
    n2+=1
    if Pt(z-u)!=(Pt(z)+q)%M:
     b2+=1
     if len(ex2)<3: ex2.append(dict(M=M,A=A,p=p,q=q,u=u,v=v,z=z,lhs=Pt(z-u),rhs=(Pt(z)+q)%M))
   if p<q: k=q//p; p,q,u,v=p,q-k*p,u+k*v,v
   else:   k=p//q; p,q,u,v=p-k*q,q,u,v+k*u
print(f"reachable states checked : {states}")
print(f"P1  Pt(z+v) = Pt z + p     : {n1} checked, {b1} violations")
for e in ex1: print("   ", e)
print(f"P2  Pt(z-u) = (Pt z + q) %% M: {n2} checked, {b2} violations")
for e in ex2: print("   ", e)
