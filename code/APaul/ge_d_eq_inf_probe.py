"""In the ge branch (q <= p), is d = Inf (u+v) exactly?

Derivation: invd_max gives d < maxn p q = p, invx_inf gives Inf < p, and
invd_cong gives d = Inf %[mod p].  Two values below p, congruent mod p.
"""
from math import gcd

tot = bad = 0
lt_tot = lt_bad = 0
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
            p, q, d, u, v = A % M, M - (A % M), B % M, 1, 1
            first = True
            while u + v < N and p > 0 and q > 0:
                I = inf[u + v]
                if first:
                    first = False
                    if p < q:
                        k = q // p; p, q, d, u, v = p, q-k*p, d%p, u+k*v, v
                    else:
                        k = p // q; pn = p-k*q
                        d = (d-pn)%q if pn <= d else d
                        p, q, u, v = pn, q, u, v+k*u
                    continue
                if q <= p:
                    tot += 1
                    if d != I:
                        bad += 1
                        if len(ex) < 4:
                            ex.append(dict(M=M, A=A, B=B, p=p, q=q, d=d,
                                           u=u, v=v, Inf=I))
                else:
                    lt_tot += 1
                    if d != I:
                        lt_bad += 1
                if p < q:
                    k = q // p; p, q, d, u, v = p, q - k * p, d % p, u + k * v, v
                else:
                    k = p // q; pn = p - k * q
                    d = (d - pn) % q if pn <= d else d
                    p, q, u, v = pn, q, u, v + k * u
print("ge branch, initial state EXCLUDED: d = Inf (u+v) :", tot, "checked,", bad, "violations")
for e in ex: print("   ", e)
print("lt branch (p < q) , for contrast   :", lt_tot, "checked,", lt_bad, "violations")
