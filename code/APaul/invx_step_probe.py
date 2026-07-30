"""Does [invx] hold at every reachable state, and is it preserved by [step]?

invx p q u v :=
  (a) forall m, 0 < m < u+v -> p <= Pt m
  (b) forall m, m < u+v   -> Pt m <= M - q
  (c) q <= M
"""
from math import gcd

def invx(M, Pt, p, q, u, v):
    a = all(p <= Pt[m] for m in range(1, u + v))
    b = all(Pt[m] <= M - q for m in range(0, u + v))
    return a, b, q <= M

tot = 0
bad_state = [0, 0, 0]
bad_step = 0
ex_state = []
ex_step = []
for M in (24, 32, 48, 60):
    for A in range(1, M):
        g = gcd(A, M); N = M // g
        L = 20 * M
        Pt = [(A * k) % M for k in range(L)]
        # invx does not mention B, so one B suffices
        p, q, u, v = A % M, M - (A % M), 1, 1
        while True:
            if u + v >= L:
                break
            if u + v >= N: break
            tot += 1
            a, b, c = invx(M, Pt, p, q, u, v)
            if not (a and b and c):
                for i, f in enumerate((a, b, c)):
                    if not f:
                        bad_state[i] += 1
                if len(ex_state) < 4:
                    ex_state.append(dict(M=M, A=A, p=p, q=q, u=u, v=v,
                                         a=a, b=b, c=c))
            if N <= u + v or p == 0 or q == 0:
                break
            if p < q:
                k = q // p; p2, q2, u2, v2 = p, q - k * p, u + k * v, v
            else:
                k = p // q; p2, q2, u2, v2 = p - k * q, q, u, v + k * u
            # step preservation, on its own terms
            if u2 + v2 < L and p2 > 0 and q2 > 0:
                if all(invx(M, Pt, p, q, u, v)) and not all(invx(M, Pt, p2, q2, u2, v2)):
                    bad_step += 1
                    if len(ex_step) < 4:
                        ex_step.append(dict(M=M, A=A, p=p, q=q, u=u, v=v,
                                            p2=p2, q2=q2, u2=u2, v2=v2))
            p, q, u, v = p2, q2, u2, v2

print("invx at reachable states :", tot, "checked")
print("   violations  min:", bad_state[0], " max:", bad_state[1], " qM:", bad_state[2])
for e in ex_state: print("     ", e)
print("invx preserved by step   :", bad_step, "violations")
for e in ex_step: print("     ", e)
