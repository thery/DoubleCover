#!/usr/bin/env python3
"""l2test.py [code dir]: checks the derivative programs the tool generates, in
L2, by executing them with the evaluator of L2 (exec.elpi), against the
evaluator of L0 over dual numbers, the tangent of the source:

- tangent: its value and its tangent are those of the dual numbers;
- adjoint: the dot-product test <ybar, J xdot> = <xbar, xdot>, with J xdot from
  the dual numbers, for random xdot and ybar;
- adjoint-value: the same, and its value is the value of the source;

each program before and after simplification, at random points; and the
simplified program leaves exactly the same floats as the original one. Needs an Elpi
with fexp, pow and string_to_real (LPCIC/elpi#459): ELPI, by default the one
built in ~/git/elpi.
"""
import os, random, re, subprocess, sys, tempfile

CODE = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ELPI = os.environ.get("ELPI", os.path.expanduser("~/git/elpi/_build/install/default/bin/elpi"))
CASES = os.environ.get("CASES", os.path.expanduser("~/claudeExp/elpi/cases"))
POINTS = 5
TOL = 1e-9

tmp = tempfile.mkdtemp()
runner = os.path.join(tmp, "run.elpi")
open(runner, "w").write("accumulate evaluate.\naccumulate primal.\n")


def elpi(case, *args):
    out = subprocess.run([ELPI, "-I", CODE, "-I", case, runner, "-exec", *args],
                         capture_output=True, text=True, stdin=subprocess.DEVNULL)
    lines = [l for l in (out.stdout + out.stderr).splitlines()
             if l and not re.match(r"(Success:|Constraints:|State:|Time:|.*time:)", l)]
    if any("Warning" in l or "error" in l.lower() for l in lines):
        raise RuntimeError(" ".join(args) + "\n" + "\n".join(lines))
    return lines


def nums(s):
    return [float(x) for x in s.split()]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def close(a, b):
    return len(a) == len(b) and all(abs(x - y) <= TOL * max(1.0, abs(y)) for x, y in zip(a, b))


def shape(ty):
    return 1 if ty in ("real", "int") else int(ty[5:-1])


def rnd_reals(n, lo, hi):
    return [repr(rnd.uniform(lo, hi)) for _ in range(n)]


rnd = random.Random(2026)
checks = bad = 0


def report(ok, what):
    global checks, bad
    checks += 1
    if not ok:
        bad += 1
        print("  FAIL", what)


for c in sorted(os.listdir(CASES)):
    case = os.path.join(CASES, c)
    if not (os.path.exists(os.path.join(case, "primal.elpi")) and os.path.exists(os.path.join(case, "tangent.hpp"))):
        continue
    n0 = checks
    for sig in elpi(case, "signatures"):
        head, result = sig.split(" -> ")
        name, *args = head.split()
        args = [tuple(a.split(":")) for a in args]                 # (name, type, role)
        role = {a: r for a, _, r in args}
        types = {a: t for a, t, _ in args}
        out_name = result.split()[1] if result.startswith("writes") else "result"
        out_shape = shape(types[out_name]) if out_name != "result" else 1
        for _ in range(POINTS):
            # a point, a tangent of the inputs, a seed of the output
            x = {a: (([str(rnd.randint(0, 15))] if t == "int" else
                      rnd_reals(shape(t), 0.5, 1.5) if r != "dependent" else ["0.0"] * shape(t)))
                 for a, t, r in args}
            xdot = {a: (rnd_reals(shape(t), -1, 1) if r in ("independent", "inout") else ["0.0"] * shape(t))
                    for a, t, r in args if t != "int" and r != "passive"}
            ybar = rnd_reals(out_shape, -1, 1)
            flat = [v for a, _, _ in args for v in x[a]]
            dots = [v for a, _, _ in args if a in xdot for v in xdot[a]]
            # the specification: the source over dual numbers
            value, tangent = (nums(l) for l in elpi(case, "tangent", "--", name, *flat, "/", *dots))
            jx = dot(ybar and nums(" ".join(ybar)), tangent)              # <ybar, J xdot>
            xdx = {a: nums(" ".join(v)) for a, v in xdot.items() if role[a] in ("independent", "inout")}
            for mode in ("tangent", "adjoint", "adjoint-value"):
                for stage in ("derivative", "simplified"):
                    params = elpi(case, "l2-signature", "--", mode, stage, name)
                    plist, ret = [p.split(":") for p in params[:-1]], params[-1]
                    inputs = []
                    for pn, _, ty in plist:
                        base, kind = (pn[:-4], "dot") if pn.endswith("_dot") else (pn[:-4], "bar") if pn.endswith("_bar") else (pn, "")
                        if kind == "":
                            v = x[pn]
                        elif kind == "dot":
                            v = xdot[base] if base in xdot else ["0.0"] * shape(ty)      # result_dot: an output
                        else:                                                         # an adjoint
                            v = ybar if base in ("result", out_name) else ["0.0"] * shape(ty)
                        inputs += v
                    outs = elpi(case, "l2-run", "--", mode, stage, name, *inputs)
                    if stage == "simplified":                     # simplify: the same floats, exactly
                        same = elpi(case, "l2-same", "--", mode, name, *inputs)
                        report(same == ["same"], f"{c} {name} {mode} simplify: {same}")
                    finals = dict(zip([p[0] for p in plist], outs[:-1]))
                    returned = outs[-1]
                    what = f"{c} {name} {mode} {stage}"
                    if mode == "tangent":
                        v = nums(returned) if out_name == "result" else nums(finals[out_name])
                        t = nums(finals[out_name + "_dot"])
                        report(close(v, value) and close(t, tangent), f"{what}: {v} {t} vs {value} {tangent}")
                    else:
                        xbar = sum(dot(xdx[a], nums(finals[a + "_bar"])) for a in xdx)   # <xdot, xbar>
                        report(abs(jx - xbar) <= TOL * max(1.0, abs(jx)), f"{what}: <ybar, J xdot> = {jx}, <xdot, xbar> = {xbar}")
                        if mode == "adjoint-value":
                            v = nums(returned) if out_name == "result" else nums(finals[out_name])
                            if role.get(out_name) != "inout":                     # an inout's new value is not given back
                                report(close(v, value), f"{what} value: {v} vs {value}")
    print(f"{c}: {checks - n0} checks")
print(f"== {checks} checks, {bad} failures")
