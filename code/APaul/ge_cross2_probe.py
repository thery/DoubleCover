"""ge_cross_ex as written is false: it bounds the crossing by j <= p//q.
Measure the corrected shape -- start at the argmax of Dst over the old
range and walk by u until the walk crosses M; the only bound needed is
that the index stays in the NEW range.

  H1 : Dst ymax >= M - p                      (max distance vs the max gap)
  H2 : the crossing happens, at some j >= 1
  H3 : ymax + j*u < u + v + k*u               (crossing index is in range)
  H4 : j <= p//q                              (what the lemma claims)
  H5 : Dst ymax + j*q - M < q                 (lands inside a q-gap)
"""
from math import gcd
n=H1=H2=H3=H4=H5=0; ex=[]
for M in (24,32,45,48,60,64):
 for A in range(1,M):
  g=gcd(A,M); N=M//g; L=26*M
  Pt=[(A*x)%M for x in range(L)]
  for B in range(M):
   Dst=[(B+M-Pt[x])%M for x in range(L)]
   p,q,u,v=A%M,M-(A%M),1,1; first=True
   while u+v<N and p>0 and q>0:
    if p<q: k=q//p; nxt=(p,q-k*p,u+k*v,v)
    else:   k=p//q; nxt=(p-k*q,q,u,v+k*u)
    if not first and q<=p and u+v+k*u<=L and u+v+k*u<N:
     n+=1
     ym=max(range(u+v), key=lambda z: Dst[z]); D=Dst[ym]
     H1 += (D >= M-p)
     j=1
     while D+j*q < M: j+=1
     H2 += 1
     H3 += (ym+j*u < u+v+k*u)
     H4 += (j <= k)
     H5 += (D+j*q-M < q)
     if not (ym+j*u < u+v+k*u) and len(ex)<4:
       ex.append(dict(M=M,A=A,B=B,p=p,q=q,u=u,v=v,k=k,ymax=ym,D=D,j=j))
    first=False
    p,q,u,v=nxt
print(f"ge steps                        : {n}")
print(f"  H1 Dst ymax >= M - p          : {H1}")
print(f"  H3 crossing index is in range : {H3}")
print(f"  H4 j <= p//q  (as stated)     : {H4}")
print(f"  H5 lands inside a q-gap       : {H5}")
for e in ex: print("   H3 fails:", e)

# --- the honest existential: SOME old index crosses inside the new range
from math import gcd
n=ok=0; ex=[]
for M in (24,32,45,48,60,64):
 for A in range(1,M):
  g=gcd(A,M); N=M//g; L=26*M
  Pt=[(A*x)%M for x in range(L)]
  for B in range(M):
   Dst=[(B+M-Pt[x])%M for x in range(L)]
   p,q,u,v=A%M,M-(A%M),1,1; first=True
   while u+v<N and p>0 and q>0:
    if p<q: k=q//p; nxt=(p,q-k*p,u+k*v,v)
    else:   k=p//q; nxt=(p-k*q,q,u,v+k*u)
    if not first and q<=p and u+v+k*u<=L and u+v+k*u<N:
     n+=1
     good=False
     for z in range(u+v):
      j=1
      while Dst[z]+j*q < M: j+=1
      if z+j*u < u+v+k*u and Dst[z]+j*q-M < q: good=True; break
     ok+=good
     if not good and len(ex)<3: ex.append(dict(M=M,A=A,B=B,p=p,q=q,u=u,v=v,k=k))
    first=False
    p,q,u,v=nxt
print(f"\nexistential over all old z      : {ok}/{n}")
for e in ex: print("   fails:", e)
