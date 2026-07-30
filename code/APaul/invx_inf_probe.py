"""Is  Inf (u+v) < maxn p q  an invariant of the loop?

Needed by inf_new_lt_le: the witness walks Inf %/ p steps of v, and that
count must be <= q %/ p, i.e. Inf must be below q.
"""
from math import gcd

tot = bad = 0
ex = []
for M in (24, 32, 48, 60):
    for A in range(1, M):
        g = gcd(A, M); N = M // g
        L = 20 * M
        Pt = [(A * k) % M for k in range(L)]
        for B in range(M):
            Dst = [(B + M - Pt[k]) % M for k in range(L)]
            inf = [M] * (L + 1)
            for n in range(1, L + 1):
                inf[n] = min(inf[n - 1], Dst[n - 1])
            p, q, u, v = A % M, M - (A % M), 1, 1
            while u + v < N and p > 0 and q > 0:
                tot += 1
                if not inf[u + v] < max(p, q):
                    bad += 1
                    if len(ex) < 4:
                        ex.append(dict(M=M, A=A, B=B, p=p, q=q, u=u, v=v,
                                       Inf=inf[u + v]))
                if p < q:
                    k = q // p; p, q, u, v = p, q - k * p, u + k * v, v
                else:
                    k = p // q; p, q, u, v = p - k * q, q, u, v + k * u
print("Inf (u+v) < maxn p q :", tot, "checked,", bad, "violations")
for e in ex: print("   ", e)
