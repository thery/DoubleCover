#!/usr/bin/env python3
"""How many units in the last place each double-word operation is out by.

The widening of an interval bound does not have to be computed from a
residual: if an algorithm is known to be within k ulps, the bound is the
answer shifted k ulps up and down.  This finds k, by running the very
algorithms of dwarith.v on random inputs and comparing with the exact
value held as a rational.

Python floats are binary64 and Python's arithmetic is the same
round-to-nearest, ties-to-even, so the functions below are the Rocq ones
line for line.  There is no fused multiply-add here either, which is the
point: Rocq has none, so the transcription must not use one.

Run: python3 probek.py
"""

from fractions import Fraction as Q
import math
import random

U = 2.0 ** -53          # the unit roundoff of binary64


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


def split(x):
    c = 134217729.0                    # two to the twenty-seventh, plus one
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


# ------------------------------------------- the operations of dwarith.v
def plus_dw_dw(x, y):
    xh, xl = x
    yh, yl = y
    sh, sl = two_sum(xh, yh)
    th, tl = two_sum(xl, yl)
    c = sl + th
    vh, vl = fast_two_sum(sh, c)
    w = tl + vl
    return fast_two_sum(vh, w)


def times_dw_dw(x, y):
    xh, xl = x
    yh, yl = y
    ch, cl1 = two_prod(xh, yh)
    tl1 = xh * yl
    tl2 = xl * yh
    cl2 = tl1 + tl2
    cl3 = cl1 + cl2
    return fast_two_sum(ch, cl3)


def div_dw_dw2(x, y):
    xh, xl = x
    yh, yl = y
    th = xh / yh
    rh, rl = times_dw_fp1(y, th)
    pih = xh - rh
    dl = xl - rl
    d = pih + dl
    tl = d / yh
    return fast_two_sum(th, tl)


def times_dw_fp1(x, y):
    xh, xl = x
    ch, cl1 = two_prod(xh, y)
    cl2 = xl * y
    th, tl1 = fast_two_sum(ch, cl2)
    tl2 = tl1 + cl1
    return fast_two_sum(th, tl2)


def half_dw(d):
    return (d[0] / 2, d[1] / 2)


def sqrt_dw(x):
    xh, xl = x
    s = (math.sqrt(xh + xl), 0.0)
    return half_dw(plus_dw_dw(s, div_dw_dw2(x, s)))


# ------------------------------------------------------------- the measuring
def val(d):
    """The exact value a double word stands for."""
    return Q(d[0]) + Q(d[1])


def ulps(got, exact, scale):
    """How far apart, in units of the last place of the SECOND word.

    A double word holds about 2^-106 of its leading word, so one unit in
    its last place is |leading word| times 2^-106.  Answering in these
    units is what makes the number a k to add, rather than a relative
    error to multiply by.
    """
    one = Q(abs(scale)) * Q(2) ** -106
    if one == 0:
        return 0.0
    return abs(got - exact) / one


def rand_dw():
    """A double word with every bit of both words used."""
    h = random.uniform(0.5, 2.0) * (2.0 ** random.randint(-40, 40))
    if random.random() < 0.5:
        h = -h
    # a low word just under half a step of the high one
    l = h * U * random.uniform(-1.0, 1.0)
    return two_sum(h, l)


def probe(name, op, arity, n=200000):
    worst = 0.0
    worst_at = None
    for _ in range(n):
        x = rand_dw()
        if arity == 2:
            y = rand_dw()
            got = op(x, y)
            if name == "div":
                exact = val(x) / val(y)
            elif name == "mul":
                exact = val(x) * val(y)
            else:
                exact = val(x) + val(y)
        else:
            x = (abs(x[0]), x[1] if x[0] > 0 else -x[1])
            got = op(x)
            exact = None                      # the root is not rational
        if arity == 1:
            # compare against a root computed to plenty of digits
            import decimal
            decimal.getcontext().prec = 80
            v = decimal.Decimal(x[0]) + decimal.Decimal(x[1])
            if v <= 0:
                continue
            exact = Q(v.sqrt())
        if not all(math.isfinite(w) for w in got):
            continue
        k = ulps(val(got), exact, got[0])
        if k > worst:
            worst, worst_at = k, (x, y if arity == 2 else None)
    print("  %-5s worst %10.2f ulps of the last word   (2^%.1f relative)"
          % (name, worst, math.log2(float(worst)) - 106 if worst else 0))
    return worst


if __name__ == "__main__":
    random.seed(20260914)
    print("double words, dwarith.v's own algorithms, 200000 random inputs:")
    probe("add", plus_dw_dw, 2)
    probe("mul", times_dw_dw, 2)
    probe("div", div_dw_dw2, 2)
    probe("sqrt", sqrt_dw, 1, n=50000)
