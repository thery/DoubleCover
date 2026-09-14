#!/usr/bin/env python3
"""How many units in the last place each triple-word operation is out by.

The widening of an interval bound does not have to be computed from a
residual: if an algorithm is within k units of the last place, the bound
is the answer shifted k up and down.  This finds k, by running the
algorithms on random inputs and comparing with the exact value held as a
rational.

Two sets are run: the ones currently in tw_updn.v, and the paper's own
Algorithms 13 and 14.  Python floats are binary64 and the arithmetic is
the same round-to-nearest, ties-to-even, so these are the same programs.
There is no fused multiply-add here, which is the point: Rocq has none,
so each RN(a + b*c) of the paper becomes two roundings, and each product
error comes from the two-product rather than from an FMA.

Run: python3 probek.py
"""

from fractions import Fraction as Q
import math
import random

U = 2.0 ** -53


# --------------------------------------------------------------- the blocks
def two_sum(a, b):
    s = a + b
    a1 = s - b
    b1 = s - a1
    return s, (a - a1) + (b - b1)


def fast_two_sum(a, b):
    s = a + b
    z = s - a
    return s, b - z


def fast_two_sum_s(a, b):
    return fast_two_sum(a, b) if abs(b) <= abs(a) else fast_two_sum(b, a)


def split(x):
    c = 134217729.0
    g = c * x
    d = x - g
    h = g + d
    return h, x - h


def two_prod(x, y):
    p = x * y
    xh, xl = split(x)
    yh, yl = split(y)
    e = (((-p + xh * yh) + xh * yl) + xl * yh) + xl * yl
    return p, e


def vec_sum(l):
    """Algorithm 4: one sweep of two-sums from the end to the front."""
    if not l:
        return []
    es = []
    s = l[-1]
    for x in reversed(l[:-1]):
        s, e = two_sum(x, s)
        es.append(e)
    return [s] + list(reversed(es))


def vseb(l):
    """Algorithm 5: the second sweep, dropping the terms that came out nought."""
    if not l:
        return []
    eps = l[0]
    rest = l[1:]
    out = []
    while rest:
        if len(rest) == 1:
            y0, y1 = two_sum(eps, rest[0])
            return out + [y0, y1]
        r, et = two_sum(eps, rest[0])
        rest = rest[1:]
        if et == 0.0:
            eps = r
        else:
            out.append(r)
            eps = et
    return out + [eps]


def merge(l1, l2):
    out = []
    i = j = 0
    while i < len(l1) and j < len(l2):
        if abs(l2[j]) <= abs(l1[i]):
            out.append(l1[i]); i += 1
        else:
            out.append(l2[j]); j += 1
    return out + l1[i:] + l2[j:]


def pad3(l):
    l = list(l[:3])
    return tuple(l + [0.0] * (3 - len(l)))


# ------------------------------------------------ Algorithm 8, the sum
def tw_sum(x, y):
    return pad3(vseb(vec_sum(merge(list(x), list(y))))[:3])


# --------------------------------- Algorithm 9, the product (no FMA)
def three_prod(x, y):
    x0, x1, x2 = x
    y0, y1, y2 = y
    z00p, z00m = two_prod(x0, y0)
    z01p, z01m = two_prod(x0, y1)
    z10p, z10m = two_prod(x1, y0)
    b = vec_sum([z00m, z01p, z10p])
    b0, b1, b2 = (b + [0.0, 0.0, 0.0])[:3]
    c = b2 + x1 * y1                       # one FMA of the paper: two here
    z31 = z10m + x0 * y2
    z32 = z01m + x2 * y0
    z3 = z31 + z32
    e = vec_sum([z00p, b0, b1, c, z3])
    e = (e + [0.0] * 5)[:5]
    r = vseb([e[1], e[2], e[3], e[4]])[:2]
    return pad3([e[0]] + list(r))


# ------------------------- Algorithm 11, a double word times a triple
def three_prod_dw(x, y):
    x0, x1, _ = x
    y0, y1, y2 = y
    z00p, z00m = two_prod(x0, y0)
    z01p, z01m = two_prod(x0, y1)
    z10p, z10m = two_prod(x1, y0)
    b = vec_sum([z00m, z01p, z10p])
    b0, b1, b2 = (b + [0.0, 0.0, 0.0])[:3]
    c = b2 + x1 * y1
    z31 = z10m + x0 * y2
    z3 = z31 + z01m
    e = vec_sum([z00p, b0, b1, c, z3])
    e = (e + [0.0] * 5)[:5]
    r = vseb([e[1], e[2], e[3], e[4]])[:2]
    return pad3([e[0]] + list(r))


# ---------- Algorithms 18 and 20: the second argument has head one
def p18_parts(x0, x1, y1, y2):
    z01p, z01m = two_prod(x0, y1)
    bh, bl = fast_two_sum_s(x1, z01p)
    z31 = z01m + x1 * y1
    z3 = z31 + x0 * y2
    s3 = bl + z3
    return bh, s3


def three_prod_one(x, y):
    x0, x1, _ = x
    _, y1, y2 = y
    bh, s3 = p18_parts(x0, x1, y1, y2)
    e = (vec_sum([x0, bh, s3]) + [0.0, 0.0, 0.0])[:3]
    r1, r2 = fast_two_sum_s(e[1], e[2])
    return (e[0], r1, r2)


def three_prod_one_tw(x, y):
    x0, x1, x2 = x
    _, y1, y2 = y
    bh, s3 = p18_parts(x0, x1, y1, y2)
    s3 = s3 + x2
    e = (vec_sum([x0, bh, s3]) + [0.0, 0.0, 0.0])[:3]
    r1, r2 = fast_two_sum_s(e[1], e[2])
    return (e[0], r1, r2)


# ------------------------- Algorithm 13's head: the Newton double word
def reci_bw(x0, x1):
    a = (1 + 2 * U) / x0
    p, e = two_prod(a, x0)                 # the paper's FMA, done by 2Prod
    h11 = (p - (1 + 2 * U)) + e
    h1 = -h11 - a * x1
    b01, b11 = two_prod(a, 1 - 2 * U)
    b12 = b11 + a * h1
    bh, bl = fast_two_sum(b01, b12)
    return (bh, bl, 0.0)


def sub2(t):
    return (2 - t[0], -t[1], -t[2])


# ------------------------------------- Algorithm 14, the quotient
def three_div(z, x):
    bw = reci_bw(x[0], x[1])
    return three_prod_one_tw(three_prod_dw(bw, z), sub2(three_prod_dw(bw, x)))


# -------------------------- and what tw_updn.v runs today, for comparison
def times_tw_tw(x, y):
    x0, x1, x2 = x
    y0, y1, y2 = y
    p00, e00 = two_prod(x0, y0)
    p01, e01 = two_prod(x0, y1)
    p10, e10 = two_prod(x1, y0)
    p11, e11 = two_prod(x1, y1)
    terms = [p00, p01, p10, p11, e00, e01, e10, e11,
             x0 * y2, x2 * y0, x1 * y2, x2 * y1, x2 * y2]
    terms.sort(key=abs, reverse=True)
    return pad3(vseb(vec_sum(terms))[:3])


def div_tw_tw(x, y):
    y0 = y[0]
    t1 = x[0] / y0
    r1 = tw_sum(x, tuple(-v for v in times_tw_tw(y, (t1, 0.0, 0.0))))
    t2 = r1[0] / y0
    r2 = tw_sum(r1, tuple(-v for v in times_tw_tw(y, (t2, 0.0, 0.0))))
    t3 = r2[0] / y0
    return pad3(vseb(vec_sum([t1, t2, t3]))[:3])


# ------------------------------------------------------------- the measuring
def val(t):
    return Q(t[0]) + Q(t[1]) + Q(t[2])


def rand_tw():
    """A triple word with every bit of all three words used."""
    h = random.uniform(0.5, 2.0) * (2.0 ** random.randint(-30, 30))
    if random.random() < 0.5:
        h = -h
    m = h * U * random.uniform(-0.5, 0.5)
    h, m = two_sum(h, m)
    l = h * U * U * random.uniform(-0.5, 0.5)
    m, l = two_sum(m, l)
    return (h, m, l)


def probe(name, op, exact_of, n=100000):
    """The worst error seen, in units of the last place of the third word.

    A triple word holds about 2^-159 of its leading word, so one unit in
    its last place is |leading word| times 2^-159.  Answering in these
    units is what makes the number a k to ADD.
    """
    worst = 0.0
    for _ in range(n):
        x = rand_tw()
        y = rand_tw()
        try:
            got = op(x, y)
        except ZeroDivisionError:
            continue
        if not all(math.isfinite(w) for w in got):
            continue
        exact = exact_of(x, y)
        one = Q(abs(got[0])) * Q(2) ** -159
        if one == 0:
            continue
        k = abs(val(got) - exact) / one
        worst = max(worst, k)
    rel = math.log2(float(worst)) - 159 if worst else 0
    print("  %-16s worst %14.1f ulps of the last word   (2^%.1f relative)"
          % (name, worst, rel))
    return worst


if __name__ == "__main__":
    random.seed(20260914)
    n = 40000
    print("triple words, %d random inputs each" % n)
    print(" the paper's algorithms:")
    probe("Alg 8  sum", tw_sum, lambda x, y: val(x) + val(y), n)
    probe("Alg 9  product", three_prod, lambda x, y: val(x) * val(y), n)
    probe("Alg 11 DW x TW", three_prod_dw,
          lambda x, y: val((x[0], x[1], 0.0)) * val(y), n)
    probe("Alg 14 quotient", three_div, lambda z, x: val(z) / val(x), n)
    print(" what tw_updn.v runs today:")
    probe("timesTwTw", times_tw_tw, lambda x, y: val(x) * val(y), n)
    probe("divTwTw", div_tw_tw, lambda x, y: val(x) / val(y), n)
