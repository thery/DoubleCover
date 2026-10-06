#!/usr/bin/env python3
"""gallinatest.py [code dir]: checks the Gallina output (gallina.elpi, for
CertiRocq) against the C++ output, on every case and mode, at random points:
the generated functions are run in Rocq (vm_compute, on primitive floats) and
compiled from C++ (double), on the same arguments, and their results must
agree. sin, cos, exp and log, declared as axioms in the generated file (they
are to be mapped to C by CertiRocq), are replaced for the test by series
accurate to about 1e-12, hence the tolerance.
"""
import os, random, re, subprocess, sys, tempfile

CODE = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CASES = os.environ.get("CASES", os.path.expanduser("~/claudeExp/elpi/cases"))
MODES = ["tangent", "adjoint", "adjoint-value"]
POINTS = 3
TOL = 1e-9

# Test definitions of the axioms: series on primitive floats.
TEST_FUNCTIONS = """\
Fixpoint series (x : float) (k : nat) (term : float) (n : nat) : float :=
  match n with O => 0 | S n' => term + series x (S k) (term * x / of_uint63 (Uint63.of_nat (S k))) n' end.
Fixpoint sq (x : float) (n : nat) : float := match n with O => x | S n' => let y := sq x n' in y * y end.
Definition fexp (x : float) : float := sq (series (x / 1024) 0 1 30) 10.
Fixpoint alt (x2 : float) (k : nat) (term : float) (n : nat) : float :=
  match n with O => 0 | S n' =>
    term + alt x2 (S (S k)) (- term * x2 / of_uint63 (Uint63.of_nat ((S k) * (S (S k))))) n' end.
Definition fsin (x : float) : float := alt (x * x) 1 x 40.
Definition fcos (x : float) : float := alt (x * x) 0 1 40.
Fixpoint newton (x y : float) (n : nat) : float :=
  match n with O => y | S n' => let e := fexp y in newton x (y + 2 * (x - e) / (x + e)) n' end.
Definition flog (x : float) : float := newton x 0 60.
"""

tmp = tempfile.mkdtemp()
rnd = random.Random(2026)
checks = bad = 0


def run(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, stdin=subprocess.DEVNULL)


def cxx_params(header, name):
    """The parameters of the C++ function: (name, kind, size, result)."""
    m = re.search(r"\n(\w+) " + re.escape(name) + r"\((.*)\)\n", header)
    ret, args = m.group(1), m.group(2)
    out = []
    for a in [a.strip() for a in re.split(r", (?!\d)", args)] if args else []:
        unused = "/*" in a
        n = re.search(r"(\w+)\*/$", a).group(1) if unused else re.search(r"(\w+)$", a).group(1)
        size = int(re.search(r"std::array<T, (\d+)>", a).group(1)) if "std::array" in a else None
        kind = "int" if a.startswith("int ") else ("array" if size else "real")
        result = "&" in a and not a.startswith("const ") and not unused
        out.append((n, kind, size, result))
    return ret, out


def rocq_float(x):
    return repr(x) if x >= 0 else "(" + repr(x) + ")"


for c in sorted(os.listdir(CASES)):
    case = os.path.join(CASES, c)
    if not os.path.exists(os.path.join(case, "primal.elpi")):
        continue
    n0 = checks
    for mode in MODES:
        d = os.path.join(tmp, c, mode)
        os.makedirs(d)
        g = run(["elpi", "-I", CODE, os.path.join(case, "primal.elpi"), "-exec", "gallina", "--", case, mode, d])
        h = run(["elpi", "-I", CODE, os.path.join(case, "primal.elpi"), "-exec", "main", "--", case, mode, d])
        module = mode.replace("-", "_")
        vfile, hfile = os.path.join(d, module + ".v"), os.path.join(d, mode + ".hpp")
        if not os.path.exists(vfile) or not os.path.exists(hfile):
            if os.path.exists(vfile) != os.path.exists(hfile):
                bad += 1; print(f"  FAIL {c} {mode}: one output only")
            continue
        src = open(vfile).read().replace("Axiom fsin fcos fexp flog : float -> float.\n", TEST_FUNCTIONS)
        src = src.replace("From Stdlib Require Import Floats List ZArith.", "From Stdlib Require Import Floats List ZArith.\nFrom Stdlib Require Uint63.")
        header = open(hfile).read()
        names = re.findall(r"^Definition (\w+) ", src, re.M)
        names = [n for n in names if n.endswith(mode.replace("-", "_"))]
        evals, mains = [], []
        for k in range(POINTS):
            for name in names:
                ret, params = cxx_params(header, name)
                vals, cdecl, call, outs = [], [], [], []
                for (pn, kind, size, result) in params:
                    if kind == "int":
                        v = rnd.randint(0, 15); vals.append(f"{v}%nat"); cdecl.append(f"int {pn} = {v};")
                    elif kind == "real":
                        v = rnd.uniform(0.5, 1.5); vals.append(rocq_float(v)); cdecl.append(f"double {pn} = {v!r};")
                    else:
                        vs = [rnd.uniform(0.5, 1.5) for _ in range(size)]
                        vals.append("[" + "; ".join(map(rocq_float, vs)) + "]")
                        cdecl.append(f"std::array<double, {size}> {pn}{{{', '.join(map(repr, vs))}}};")
                    call.append(pn)
                    if result:
                        outs.append((pn, kind))
                evals.append(f"Eval vm_compute in ({name} {' '.join(vals)}).")
                c_call = f"adjudge::{name}<double>({', '.join(call)})"
                prints = []
                if ret != "void":
                    prints.append(f'std::printf("%.17g\\n", {c_call});')
                else:
                    prints.append(c_call + ";")
                for pn, kind in outs:
                    if kind == "array":
                        prints.append(f'for (double e : {pn}) std::printf("%.17g ", e); std::printf("\\n");')
                    else:
                        prints.append(f'std::printf("%.17g\\n", {pn});')
                mains.append("    { " + " ".join(cdecl) + " " + " ".join(prints) + ' std::printf("--\\n"); }')
        open(os.path.join(d, "Test.v"), "w").write(src + "\n" + "\n".join(evals) + "\n")
        r = run(["rocq", "compile", "Test.v"], cwd=d)
        if r.returncode != 0:
            bad += 1; print(f"  FAIL {c} {mode}: rocq\n" + r.stdout[-800:] + r.stderr[-800:]); continue
        rocq_vals = [[float(x) for x in re.findall(r"-?\d+\.?\d*(?:e-?\d+)?|-?inf|nan", blk.split(":")[0])]
                     for blk in r.stdout.split("     = ")[1:]]
        cpp = os.path.join(d, "test.cpp")
        open(cpp, "w").write(f'#include <cstdio>\n#include "{mode}.hpp"\nint main() {{\n' + "\n".join(mains) + "\n}\n")
        r2 = run(["g++", "-std=c++20", "-O1", "-I", d, cpp, "-o", os.path.join(d, "test")])
        if r2.returncode != 0:
            bad += 1; print(f"  FAIL {c} {mode}: g++\n" + r2.stderr[-800:]); continue
        out = run([os.path.join(d, "test")]).stdout
        cpp_vals = [[float(x) for x in blk.split()] for blk in out.split("--\n")[:-1]]
        for i, (a, b) in enumerate(zip(rocq_vals, cpp_vals)):
            checks += 1
            ok = len(a) == len(b) > 0 and all(abs(x - y) <= TOL * max(1.0, abs(y)) for x, y in zip(a, b))
            if not ok:
                bad += 1; print(f"  FAIL {c} {mode} #{i}: rocq {a} vs c++ {b}")
        if len(rocq_vals) != len(cpp_vals):
            bad += 1; print(f"  FAIL {c} {mode}: {len(rocq_vals)} rocq results, {len(cpp_vals)} c++")
    print(f"{c}: {checks - n0} checks")
print(f"== {checks} checks, {bad} failures")
