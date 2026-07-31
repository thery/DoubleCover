"""Cut D: does the ge walk from ymax reach M within k = p%/q steps?
   Cut E: in the ge branch, is Inf(old)-Inf(new) a multiple of q, and bounded?"""
from math import gcd
dn=0; dok=0; en=0; emult=0; ecle=0; cmax=0
for M in (24,32,45,48,60):
 for A in range(1,M):
  g=gcd(A,M); N=M//g; L=26*M
  Pt=[(A*k)%M for k in range(L)]
  for B in range(M):
   Dst=[(B+M-Pt[k])%M for k in range(L)]
   inf=[M]*(L+1)
   for k2 in range(1,L+1): inf[k2]=min(inf[k2-1],Dst[k2-1])
   p,q,u,v=A%M,M-(A%M),1,1; first=True
   while u+v<N and p>0 and q>0:
    if p<q: k=q//p; p2,q2,u2,v2=p,q-k*p,u+k*v,v
    else:   k=p//q; p2,q2,u2,v2=p-k*q,q,u,v+k*u
    if not first and q<=p and u2+v2<=L:
     dn+=1
     ymax=max(range(u+v), key=lambda z: Dst[z])
     dok += (M <= Dst[ymax] + (p//q)*q)
     I0=inf[u+v]; I1=inf[u2+v2]; en+=1
     if (I0-I1)%q==0:
       emult+=1; c=(I0-I1)//q; cmax=max(cmax,c); ecle += (c<=p//q)
    first=False
    p,q,u,v=p2,q2,u2,v2
print(f"Cut D  Dst ymax + (p%/q)*q >= M : {dok}/{dn}")
print(f"Cut E  Inf drop multiple of q   : {emult}/{en};  c <= p%/q : {ecle}; max c {cmax}")
