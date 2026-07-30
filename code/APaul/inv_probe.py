from math import gcd
def trace(M,A,B,N):
    p,q,d,u,v=A%M,M-(A%M),B%M,1,1; out=[(p,q,d,u,v)]
    for _ in range(3*M):
        if N<=u+v: break
        if p==0 or q==0: return out,True
        if p<q: k=q//p; q-=k*p; d%=p; u+=k*v
        else:
            k=p//q; pn=p-k*q
            if pn<=d: d=(d-pn)%q
            p=pn; v+=k*u
        out.append((p,q,d,u,v))
    return out,False

def check(M,N,skip):
    f={'C1 d<=Inf(u+v)':0,'C2 d<maxn p q':0,'C3 gcd p q = gcd A M':0,
       'C4 bezout':0,'degen':0,'states':0}
    for A in range(1,M):
        pts=[(A*x)%M for x in range(M)]
        for B in range(M):
            DST=[(B+M-pts[x])%M for x in range(M)]
            inf=[M]*(M+1)
            for n in range(1,M+1): inf[n]=min(inf[n-1],DST[n-1])
            tr,dg=trace(M,A,B,N)
            if dg: f['degen']+=1; continue
            for (p,q,d,u,v) in tr[skip:]:
                f['states']+=1
                if not d<=inf[min(u+v,M)]: f['C1 d<=Inf(u+v)']+=1
                if not d<max(p,q): f['C2 d<maxn p q']+=1
                if gcd(p,q)!=gcd(A,M): f['C3 gcd p q = gcd A M']+=1
                if u*p+v*q!=M: f['C4 bezout']+=1
    return f

for (M,N) in [(32,8),(64,10),(64,20),(128,16),(128,40),(256,32)]:
    for skip in (0,1):
        f=check(M,N,skip)
        bad={k:x for k,x in f.items() if x and k not in('states','degen')}
        print(f"M={M:4d} N={N:3d} skip={skip}  states={f['states']:7d} degen={f['degen']:5d}  "
              +("ALL HOLD" if not bad else str(bad)))
