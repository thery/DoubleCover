#!/usr/bin/env python3
"""evaltest.py [code dir]: checks the L0 evaluator of elpiDiff against the C++
of every case, at random points: in the domain of floats against the primal
(primal.hpp), and in the domain of dual numbers, along random tangents,
against the tangent the tool generates (tangent.hpp).

The evaluator needs an Elpi with the float functions fexp, pow and
string_to_real (LPCIC/elpi#459): set ELPI to its binary, by default the one
built in ~/git/elpi. Reals are written with 17 digits, so that both sides read
the same doubles; Elpi prints 12 significant digits, hence the tolerance.
"""
import os, random, re, subprocess, sys, tempfile

CODE = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ELPI = os.environ.get("ELPI", os.path.expanduser("~/git/elpi/_build/install/default/bin/elpi"))
CASES = os.environ.get("CASES", os.path.expanduser("~/claudeExp/elpi/cases"))
POINTS = 10
TOL = 1e-10

tmp = tempfile.mkdtemp()
runner = os.path.join(tmp, "run.elpi")
open(runner, "w").write("accumulate evaluate.\naccumulate primal.\n")


def elpi(case, *args):
    out = subprocess.run([ELPI, "-I", CODE, "-I", case, runner, "-exec", *args],
                         capture_output=True, text=True, stdin=subprocess.DEVNULL)
    lines = [l for l in (out.stdout + out.stderr).splitlines()
             if l and not re.match(r"(Success:|Constraints:|State:|Time:|.*time:)", l)]
    if any("Warning" in l or "error" in l.lower() for l in lines):
        raise RuntimeError("\n".join(lines))
    return lines


def parse_signature(line):
    head, result = line.split(" -> ")
    name, *args = head.split()
    return name, [tuple(a.split(":")) for a in args], result


def random_args(args, rnd):
    vals = []
    for _, ty, role in args:
        if ty == "int":
            vals.append(str(rnd.randint(0, 15)))   # >= 0: a C++ bool encoded as an int (weno5) agrees with "> 0"
        elif ty == "real":
            vals.append(repr(rnd.uniform(0.5, 1.5)) if role != "dependent" else "0.0")
        else:
            n = int(ty[5:-1])
            vals.append([repr(rnd.uniform(0.5, 1.5)) if role != "dependent" else "0.0" for _ in range(n)])
    return vals


def cxx_point(name, args, result, vals):
    decls, call = [], []
    for (an, ty, _), v in zip(args, vals):
        if ty == "int":
            decls.append(f"int {an} = {v};")
        elif ty == "real":
            decls.append(f"double {an} = {v};")
        else:
            decls.append(f"std::array<double, {len(v)}> {an}{{{', '.join(v)}}};")
        call.append(an)
    c = f"{name}({', '.join(call)})"
    if result.startswith("returns"):
        out = f'std::printf("%.17g\\n", {c});'
    else:
        y = result.split()[1]
        ty = next(t for n, t, _ in args if n == y)
        if ty == "real":
            out = f'{c}; std::printf("%.17g\\n", {y});'
        else:
            out = f'{c}; for (double e : {y}) std::printf("%.17g ", e); std::printf("\\n");'
    return "    { " + " ".join(decls) + " " + out + " }\n"


def random_dots(args, vals, rnd):
    """One tangent per real of each argument that is not passive; 0 for a dependent one."""
    dots = []
    for (_, ty, role), v in zip(args, vals):
        if ty == "int" or role == "passive":
            dots.append(None)
        elif ty == "real":
            dots.append(repr(rnd.uniform(-1, 1)) if role != "dependent" else "0.0")
        else:
            dots.append([repr(rnd.uniform(-1, 1)) if role != "dependent" else "0.0" for _ in v])
    return dots


def cxx_tangent_point(name, args, result, vals, dots):
    decls, call, dcall = [], [], []
    for (an, ty, _), v, d in zip(args, vals, dots):
        if ty == "int":
            decls.append(f"int {an} = {v};")
        elif ty == "real":
            decls.append(f"double {an} = {v};")
        else:
            decls.append(f"std::array<double, {len(v)}> {an}{{{', '.join(v)}}};")
        call.append(an)
        if d is not None:
            if ty == "real":
                decls.append(f"double {an}_dot = {d};")
            else:
                decls.append(f"std::array<double, {len(d)}> {an}_dot{{{', '.join(d)}}};")
            dcall.append(f"{an}_dot")
    if result.startswith("returns"):
        out = (f"double result_dot; double result = {name}_tangent({', '.join(call + dcall + ['result_dot'])}); "
               'std::printf("%.17g\\n%.17g\\n", result, result_dot);')
    else:
        y = result.split()[1]
        ty = next(t for n, t, _ in args if n == y)
        out = f"{name}_tangent({', '.join(call + dcall)}); "
        if ty == "real":
            out += f'std::printf("%.17g\\n%.17g\\n", {y}, {y}_dot);'
        else:
            out += (f'for (double e : {y}) std::printf("%.17g ", e); std::printf("\\n"); '
                    f'for (double e : {y}_dot) std::printf("%.17g ", e); std::printf("\\n");')
    return "    { " + " ".join(decls) + " " + out + " }\n"


def close(a, b):
    a, b = [float(x) for x in a.split()], [float(x) for x in b.split()]
    return len(a) == len(b) and all(abs(x - y) <= TOL * max(1.0, abs(y)) for x, y in zip(a, b))


rnd = random.Random(2026)
checks = bad = 0
for c in sorted(os.listdir(CASES)):
    case = os.path.join(CASES, c)
    if not (os.path.exists(os.path.join(case, "primal.elpi")) and os.path.exists(os.path.join(case, "primal.hpp"))):
        continue
    has_tangent = os.path.exists(os.path.join(case, "tangent.hpp"))
    sigs = [parse_signature(l) for l in elpi(case, "signatures")]
    main, expected = "", []
    for name, args, result in sigs:
        for _ in range(POINTS):
            vals = random_args(args, rnd)
            flat = [x for v in vals for x in (v if isinstance(v, list) else [v])]
            expected.append(("value", name, flat, " ".join(elpi(case, "run", "--", name, *flat))))
            main += cxx_point(name, args, result, vals)
            if has_tangent:
                dots = random_dots(args, vals, rnd)
                fdots = [x for d in dots if d is not None for x in (d if isinstance(d, list) else [d])]
                v, t = elpi(case, "tangent", "--", name, *flat, "/", *fdots)
                expected.append(("tangent: value", name, flat + ["/"] + fdots, v))
                expected.append(("tangent", name, flat + ["/"] + fdots, t))
                main += cxx_tangent_point(name, args, result, vals, dots)
    src = os.path.join(tmp, c + ".cpp")
    open(src, "w").write('#include <array>\n#include <cstdio>\n#include "primal.hpp"\n'
                         + ('#include "tangent.hpp"\n' if has_tangent else '') + 'using namespace adjudge;\n'
                         'int main() {\n' + main + "}\n")
    exe = os.path.join(tmp, c)
    cc = subprocess.run(["g++", "-std=c++20", "-O1", "-I", case, src, "-o", exe], capture_output=True, text=True)
    if cc.returncode:
        print(f"{c}: COMPILE FAIL\n{cc.stderr[:800]}"); bad += 1; continue
    got = subprocess.run([exe], capture_output=True, text=True).stdout.splitlines()
    nbad = 0
    if len(got) != len(expected):
        print(f"{c}: {len(got)} C++ results for {len(expected)} checks"); bad += 1; continue
    for (what, name, flat, ev), cx in zip(expected, got):
        checks += 1
        if not close(ev, cx):
            nbad += 1; bad += 1
            print(f"  FAIL {what} {name}({' '.join(flat)}): evaluator {ev}, C++ {cx}")
    nt = sum(1 for e in expected if e[0] == "tangent")
    print(f"{c}: {len(expected) - 2 * nt} values, {nt} tangents, {nbad} failures")
print(f"== {checks} checks, {bad} failures")
