#!/usr/bin/env python3
"""Reference check of one line of in_lt, in Paul's notation (not a proof).

A line is x0, n, then B_0 .. B_(k-1), each of l 64-bit words, least
significant first: B_i = P(i) mod beta^l (step 3 of Paul's algorithm).

Usage: check_line.py in_lt LINE K L M

exp is computed with integers in fixed point (P fraction bits), accurate
far beyond the bits the conditions need; the margins are printed so that
the reader can see they are not close to the rounding of this script."""
import sys

P = 1200  # fraction bits of the fixed-point reals


def exp_fix(xn, xe):
    """exp(xn * 2^xe) * 2^P, xn > 0, as an integer (error a few ulps)."""
    s = 12                       # exp(x) = exp(x / 2^s) ^ (2^s)
    q = P + 64                   # working precision
    y = (xn << q) >> (s - xe) if s - xe >= 0 else (xn << q) << (xe - s)
    # Taylor series of exp(y / 2^q)
    term, total, i = 1 << q, 1 << q, 1
    while term:
        term = term * y >> q
        term //= i
        total += term
        i += 1
    for _ in range(s):
        total = total * total >> q
    return total >> (q - P) if q >= P else total << (P - q)


def floor_log2(X):
    """floor(log2(X / 2^P)) for X > 0."""
    return X.bit_length() - 1 - P


def main(path, line, K, L, m):
    with open(path) as f:
        for i, w in enumerate(f):
            if i + 1 == line:
                w = w.split()
                break
    mant, ex = w[0][2:].split('p')
    ip, fp = mant.split('.')
    M0 = int(ip + fp.ljust(13, '0'), 16)
    xe = int(ex) - 52            # x0 = M0 * 2^xe, u = 2^xe
    n = int(w[1])
    words = [int(x, 16) for x in w[2:]]
    B = [sum(words[L * i + j] << (64 * j) for j in range(L)) for i in range(K)]
    lb = 64 * L                  # beta^l = 2^lb

    print('x0 = %s, n = %d, u = 2^%d' % (w[0], n, xe))
    # 1. u constant: x0 and x1 in one binade of x
    c1 = (1 << 52) <= M0 and M0 + n < (1 << 53) and n >= 0
    print('1. x0, x1 in [2^%d, 2^%d):' % (xe + 52, xe + 53), c1)

    # 2. v constant: exp x0 and exp x1 in one binade
    E0 = exp_fix(M0, xe)
    E1 = exp_fix(M0 + n, xe)
    e = floor_log2(E0)
    c2 = floor_log2(E1) == e
    print('2. exp x0, exp x1 in [2^%d, 2^%d), v = 2^%d:' % (e, e + 1, e - 53), c2)
    ve = e - 53                  # v = 2^ve

    # 3. (H_A) the table holds B_i = P(i) mod beta^l, i < k, with
    #    P(j) = A_0 + A_1 j + ... + A_(k-1) j^(k-1) and A_i the nearest
    #    integer to beta^l frac(a_i / v), so |A_i - beta^l frac(a_i/v)| < 1.
    worst = 0.0
    A = []
    fact = 1
    for i in range(K):
        if i:
            fact *= i
        # t = beta^l a_i / v = exp(x0) u^i / (i! v) * 2^lb, times 2^P
        sh = lb + xe * i - ve
        T = (E0 << sh if sh >= 0 else E0 >> -sh) // fact
        t = T % (1 << (lb + P))  # beta^l frac(a_i/v), times 2^P
        Ai = (t + (1 << (P - 1))) >> P
        worst = max(worst, abs((Ai << P) - t) / (1 << P))
        A.append(Ai)
    c3a = all(0 <= a < (1 << lb) for a in A) and worst < 1
    vals = [sum(A[j] * i ** j for j in range(K)) % (1 << lb) for i in range(K)]
    c3b = vals == B
    print('3. (H_A), largest |A_i - beta^l frac(a_i/v)| = %.3g:' % worst, c3a)
    print('   table = P(0) .. P(k-1) mod beta^l:', c3b)

    # 4. (H_T) rho = exp(x1) (n u)^k / (k! v): the Taylor remainder bound
    kf = fact * K                # K!
    # log2 rho, from exp(x1) = E1 / 2^P
    import math
    lrho = (math.log2(E1) - P) + K * (math.log2(n) + xe) - math.log2(kf) - ve
    print('4. (H_T) rho = exp(x1) (n u)^k / (k! v) = 2^%.2f' % lrho)

    # 5. (H_E) E >= beta^l (2^-m + rho) + (1 + n + ... + n^(k-1))
    Emin = 2.0 ** (lb - m) + 2.0 ** (lb + lrho) + sum(n ** i for i in range(K))
    print('5. (H_E) smallest E = 2^%.4f' % math.log2(Emin))
    print('   with E = 2^%d:' % (lb - m + 1), Emin <= 2.0 ** (lb - m + 1))

    # 6. 2 E < beta^l
    print('6. 2 E < beta^l for E = 2^%d:' % (lb - m + 1), (2 << (lb - m + 1)) < (1 << lb))


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]),
         int(sys.argv[5]))
