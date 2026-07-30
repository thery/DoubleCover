def test(cond,name):
    bad=[];tot=0
    for M in (32,64,128):
        for A in range(1,M):
            g=A%M
            if g==0: continue
            for B in range(M):
                for x in range(0,2*M):
                    if not cond(M,g,B,x): continue
                    tot+=1
                    Dst=(B+M-(A*x)%M)%M
                    if not (B%g <= Dst): bad.append((M,A,B,x,B%g,Dst))
    print(f"{name}: checked {tot}, counterexamples {len(bad)}")
    for r in bad[:4]: print("   M=%d A=%d B=%d x=%d B%%g=%d Dst=%d"%r)

test(lambda M,g,B,x: g*x <  M, "g*x < M ")
test(lambda M,g,B,x: g*x <= M, "g*x <= M")
