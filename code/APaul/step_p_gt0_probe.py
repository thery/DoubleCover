from math import gcd
bad=[];tot=0
for M in (32,64,128):
  for A in range(1,M):
    g=gcd(A,M)
    for N in range(1,M//g+1):
      p,q,d,u,v=A%M,M-(A%M),0,1,1
      for _ in range(3*M):
        if N<=u+v: break
        if p==0 or q==0: break
        if p<q:
          k=q//p; p2,q2,u2,v2=p,q-k*p,u+k*v,v
        else:
          k=p//q; p2,q2,u2,v2=p-k*q,q,u,v+k*u
        tot+=1
        if u2+v2<N and (p2==0 or q2==0): bad.append((M,A,N,p,q,u,v,p2,q2,u2,v2))
        p,q,u,v=p2,q2,u2,v2
print("conditioned step_p_gt0: steps checked",tot," counterexamples",len(bad))
for r in bad[:5]: print("  ",r)
