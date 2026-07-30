# is  y <= x -> Dst (x - y) = (Dst x + Pt y) %% M   true WITHOUT Pt y <= Pt x ?
bad=[];tot=0
for M in (24,32,48,64):
    for A in range(1,M):
        for B in range(M):
            Pt=[(A*k)%M for k in range(3*M)]
            Dst=[(B+M-Pt[k])%M for k in range(3*M)]
            for x in range(3*M):
                for y in range(x+1):
                    tot+=1
                    if Dst[x-y]!=(Dst[x]+Pt[y])%M: bad.append((M,A,B,x,y))
print("unconditional dstB: checked",tot,"bad",len(bad),bad[:3])
