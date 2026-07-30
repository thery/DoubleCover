from math import gcd
c={'ifl_ge':0,'ifl_ge_bad':0,'lt':0,'lt_bad':0,'ge':0,'ge_bad':0}
ex={}
for M in (24,32,48,64):
  for A in range(1,M):
    g=gcd(A,M); N=M//g
    for B in range(M):
      Pt=[(A*k)%M for k in range(8*M)]
      Dst=[(B+M-Pt[k])%M for k in range(8*M)]
      inf=[M]*(8*M+1)
      for n in range(1,8*M+1): inf[n]=min(inf[n-1],Dst[n-1])
      # --- invd_first_le_ge : the q<=p branch of the FIRST step
      p,q,d,u,v=A%M,M-(A%M),B%M,1,1
      if q<=p and p>0 and q>0:
        k=p//q; pn=p-k*q
        d2=(d-pn)%q if pn<=d else d
        u2,v2=u,v+k*u
        c['ifl_ge']+=1
        if not d2<=inf[min(u2+v2,8*M)]:
          c['ifl_ge_bad']+=1; ex.setdefault('ifl_ge',(M,A,B,p,q,d,u,v,d2,u2,v2))
      # --- the two step_invd_le_new branches, from states where invd holds
      # (i.e. after the first step)
      first=True
      while True:
        if N<=u+v or p==0 or q==0: break
        if p<q: k=q//p; p2,q2,d2,u2,v2=p,q-k*p,d%p,u+k*v,v
        else:
          k=p//q; pn=p-k*q
          d2=(d-pn)%q if pn<=d else d
          p2,q2,u2,v2=pn,q,u,v+k*u
        if not first:      # invd holds at (p,q,d,u,v)
          if p<q:
            for x in range(u+v, min(u+(q//p)*v+v,8*M)):
              c['lt']+=1
              if not (d%p)<=Dst[x]:
                c['lt_bad']+=1; ex.setdefault('lt',(M,A,B,p,q,d,u,v,x))
          else:
            pn=p-(p//q)*q
            dd=(d-pn)%q if pn<=d else d
            for x in range(u+v, min(u+(v+(p//q)*u),8*M)):
              c['ge']+=1
              if not dd<=Dst[x]:
                c['ge_bad']+=1; ex.setdefault('ge',(M,A,B,p,q,d,u,v,x))
        first=False
        p,q,d,u,v=p2,q2,d2,u2,v2
print("invd_first_le_ge  : checked %7d  counterexamples %d"%(c['ifl_ge'],c['ifl_ge_bad']))
print("step_..._new_lt   : checked %7d  counterexamples %d"%(c['lt'],c['lt_bad']))
print("step_..._new_ge   : checked %7d  counterexamples %d"%(c['ge'],c['ge_bad']))
for k,val in ex.items(): print("  first counterexample",k,val)
