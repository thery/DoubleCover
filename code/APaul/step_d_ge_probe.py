# core identity behind step_d_ge:  q = M - Pt u
# claim: j*u <= x  ->  j*q <= Dst x  ->  Dst (x - j*u) = Dst x - j*q
bad=[];tot=0
for M in (24,32,40):
    for A in range(1,M):
        for B in range(M):
            Pt=[(A*k)%M for k in range(4*M)]
            Dst=[(B+M-Pt[k])%M for k in range(4*M)]
            for u in range(1,M):
                q=M-Pt[u]
                for x in range(3*M):
                    for j in range(0,4):
                        if j*u>x: continue
                        if j*q>Dst[x]: continue
                        tot+=1
                        if Dst[x-j*u]!=Dst[x]-j*q: bad.append((M,A,B,u,q,x,j,Dst[x-j*u],Dst[x]-j*q))
print("checked",tot,"bad",len(bad))
for r in bad[:6]: print("   M=%d A=%d B=%d u=%d q=%d x=%d j=%d  got=%d want=%d"%r)
