"""The fact the four remaining leaves all bottom out in:

  D: for y < u+v,  Dst y = Inf (u+v) + a*p + b*q  for some a, b >= 0.

Also checks the two consequences we actually need:
  C1 (mod_le_restricted): Dst y %/ p <= q %/ p  ->  d %% p <= Dst y %% p
  C2 (le_ge_wrap): in the ge branch, M <= Dst y + m*q -> d' <= Dst y + m*q - M
"""
from math import gcd

def representable(x, p, q):
    b = 0
    while b * q <= x:
        if (x - b * q) % p == 0:
            return True
        b += 1
    return False

totD = badD = 0
totC1 = badC1 = 0
totC2 = badC2 = 0
exD = []
for M in (24, 32, 48):
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
            while u + v < N and p > 0 and q > 0:
                I = inf[u + v]
                for y in range(u + v):
                    totD += 1
                    if not representable(Dst[y] - I, p, q):
                        badD += 1
                        if len(exD) < 3:
                            exD.append(dict(M=M, A=A, B=B, p=p, q=q, u=u, v=v,
                                            y=y, Dst=Dst[y], Inf=I))
                    if p < q and Dst[y] // p <= q // p:
                        totC1 += 1
                        if d % p > Dst[y] % p:
                            badC1 += 1
                    if q <= p:
                        pn = p - (p // q) * q
                        dn = (d - pn) % q if pn <= d else d
                        for m in range(1, p // q + 1):
                            if M <= Dst[y] + m * q:
                                totC2 += 1
                                if dn > Dst[y] + m * q - M:
                                    badC2 += 1
                if p < q:
                    k = q // p; p, q, d, u, v = p, q - k * p, d % p, u + k * v, v
                else:
                    k = p // q; pn = p - k * q
                    d = (d - pn) % q if pn <= d else d
                    p, q, u, v = pn, q, u, v + k * u

print("D  Dst y = Inf + a*p + b*q :", totD, "checked,", badD, "violations")
for e in exD: print("     ", e)
print("C1 mod_le_restricted       :", totC1, "checked,", badC1, "violations")
print("C2 le_ge_wrap              :", totC2, "checked,", badC2, "violations")
