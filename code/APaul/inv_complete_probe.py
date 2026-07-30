from math import gcd
def states(M,A,N):
    p,q,d,u,v=A%M,M-(A%M),0,1,1; out=[(p,q,u,v)]
    for _ in range(3*M):
        if N<=u+v: break
        if p==0 or q==0: return None
        if p<q:
            k=q//p; q-=k*p; d%=p; u+=k*v
        else:
            k=p//q; pn=p-k*q
            if pn<=d: d=(d-pn)%q
            p=pn; v+=k*u
        out.append((p,q,u,v))
    return out
bad=[];tot=0
for M in (32,64):
    for A in range(1,M):
        g=gcd(A,M); N=M//g
        st=states(M,A,N)
        if st is None: continue
        for (p,q,u,v) in st:
            if min(p,q)==g:
                tot+=1
                if u+v!=M//g: bad.append((M,A,g,p,q,u,v,M//g))
print("states with minn p q = g:",tot," counterexamples:",len(bad))
for r in bad[:6]: print("  M=%d A=%d g=%d p=%d q=%d u=%d v=%d u+v=%d M/g=%d"%(r[0],r[1],r[2],r[3],r[4],r[5],r[6],r[5]+r[6],r[7]))
