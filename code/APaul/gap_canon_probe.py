"""Round 8 phase 1.  invx_gap is EXISTENTIAL, and every wrong statement so far
came from that (ge_wrap_au, and lt_gap_new's borrow corner).  Is there a
CANONICAL witness?

For each reachable (inv,invx) state and each y < u+v, with D = Dst y - Inf:
  G1  greedy on the LARGER gap first
  G2  greedy on q first : b = D // q, a = (D %% q) // p
  G3  greedy on p first : a = D // p, b = (D %% p) // q
"exact" = no remainder left; "in range" = exact and a <= u and b <= v.
"""
from math import gcd

MS = (24, 32, 45, 48, 60, 64)


def walk(M, A, B):
    """yield (p,q,u,v,Dst,inf) for every reachable non-initial state."""
    g = gcd(A, M)
    N = M // g
    L = 26 * M
    Pt = [(A * x) % M for x in range(L)]
    Dst = [(B + M - Pt[x]) % M for x in range(L)]
    inf = [M] * (L + 1)
    for k in range(1, L + 1):
        inf[k] = min(inf[k - 1], Dst[k - 1])
    p, q, u, v = A % M, M - (A % M), 1, 1
    first = True
    while u + v < N and p > 0 and q > 0:
        if not first:
            yield p, q, u, v, Dst, inf
        if p < q:
            k = q // p
            p, q, u, v = p, q - k * p, u + k * v, v
        else:
            k = p // q
            p, q, u, v = p - k * q, q, u, v + k * u
        first = False


def main():
    n = 0
    ex1 = ex2 = ex3 = 0          # exact
    ok1 = ok2 = ok3 = 0          # exact and in range
    bad = []
    for M in MS:
        for A in range(1, M):
            for B in range(M):
                for p, q, u, v, Dst, inf in walk(M, A, B):
                    I = inf[u + v]
                    for y in range(u + v):
                        D = Dst[y] - I
                        n += 1
                        # G2 : q first
                        b = D // q
                        a = (D % q) // p
                        e2 = (D % q) % p == 0
                        ex2 += e2
                        ok2 += e2 and a <= u and b <= v
                        # G3 : p first
                        a3 = D // p
                        b3 = (D % p) // q
                        e3 = (D % p) % q == 0
                        ex3 += e3
                        ok3 += e3 and a3 <= u and b3 <= v
                        # G1 : larger first
                        if q >= p:
                            e1, a1, b1 = e2, a, b
                        else:
                            e1, a1, b1 = e3, a3, b3
                        ex1 += e1
                        ok1 += e1 and a1 <= u and b1 <= v
                        if not (e1 and a1 <= u and b1 <= v) and len(bad) < 6:
                            bad.append(dict(M=M, A=A, B=B, p=p, q=q, u=u, v=v,
                                            y=y, D=D, a=a1, b=b1, exact=e1))
    print(f"(state, index) pairs      : {n}")
    print(f"  G1 larger-first exact   : {ex1}   in range : {ok1}")
    print(f"  G2 q-first      exact   : {ex2}   in range : {ok2}")
    print(f"  G3 p-first      exact   : {ex3}   in range : {ok3}")
    for e in bad:
        print("   G1 fails:", e)


main()
