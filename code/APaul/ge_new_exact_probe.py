"""After a ge step, is the new d exactly Inf of the new range?

If so, both le_ge_wrap and inf_cong_ge are immediate.
"""
from math import gcd
tot = bad = 0
ex = []
for M in (24, 32, 48, 60):
    for A in range(1, M):
        g = gcd(A, M); N = M // g
        L = 24 * M
        Pt = [(A * k) % M for k in range(L)]
        for B in range(M):
            Dst = [(B + M - Pt[k]) % M for k in range(L)]
            inf = [M] * (L + 1)
            for n in range(1, L + 1):
                inf[n] = min(inf[n - 1], Dst[n - 1])
            p, q, d, u, v = A % M, M - (A % M), B % M, 1, 1
            first = True
            while u + v < N and p > 0 and q > 0:
                if p < q:
                    k = q // p; p2, q2, d2, u2, v2 = p, q-k*p, d % p, u+k*v, v
                else:
                    k = p // q; pn = p-k*q
                    d2 = (d-pn) % q if pn <= d else d
                    p2, q2, u2, v2 = pn, q, u, v+k*u
                if not first and q <= p and u2+v2 <= L:
                    tot += 1
                    if d2 != inf[u2+v2]:
                        bad += 1
                        if len(ex) < 4:
                            ex.append(dict(M=M, A=A, B=B, p=p, q=q, d=d, u=u, v=v,
                                           d2=d2, InfNew=inf[u2+v2]))
                first = False
                p, q, d, u, v = p2, q2, d2, u2, v2
print("after a ge step:  d' = Inf (u'+v') :", tot, "checked,", bad, "violations")
for e in ex: print("   ", e)
