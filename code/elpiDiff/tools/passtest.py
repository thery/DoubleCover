#!/usr/bin/env python3
"""passtest.py [code dir]: checks that the passes normalize (L0 to L1) and
annotate (L1 to L1ᵃ) preserve the semantics exactly: at random points, the
evaluators of L0 and of L1 give the same floats on the source, its A-normal
form and its annotated form (the comparison is made in Elpi, bit for bit). Needs
an Elpi with fexp, pow and string_to_real (LPCIC/elpi#459).
"""
import os, random, re, subprocess, sys, tempfile

CODE = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ELPI = os.environ.get("ELPI", os.path.expanduser("~/git/elpi/_build/install/default/bin/elpi"))
CASES = os.environ.get("CASES", os.path.expanduser("~/claudeExp/elpi/cases"))
POINTS = 10

tmp = tempfile.mkdtemp()
runner = os.path.join(tmp, "run.elpi")
open(runner, "w").write("accumulate evaluate.\naccumulate primal.\n")


def elpi(case, *args):
    out = subprocess.run([ELPI, "-I", CODE, "-I", case, runner, "-exec", *args],
                         capture_output=True, text=True, stdin=subprocess.DEVNULL)
    return [l for l in (out.stdout + out.stderr).splitlines()
            if l and not re.match(r"(Success:|Constraints:|State:|Time:|.*time:)", l)]


rnd = random.Random(2026)
checks = bad = 0
for c in sorted(os.listdir(CASES)):
    case = os.path.join(CASES, c)
    if not os.path.exists(os.path.join(case, "primal.elpi")) or not os.path.exists(os.path.join(case, "primal.hpp")):
        continue
    n = 0
    for sig in elpi(case, "signatures"):
        name, *args = sig.split(" -> ")[0].split()
        for _ in range(POINTS):
            flat = []
            for a in args:
                _, ty, role = a.split(":")
                k = 1 if ty in ("real", "int") else int(ty[5:-1])
                flat += ([str(rnd.randint(0, 15))] if ty == "int" else
                         [repr(rnd.uniform(0.5, 1.5)) if role != "dependent" else "0.0" for _ in range(k)])
            out = elpi(case, "passes", "--", name, *flat)
            checks += 1; n += 1
            if out != ["same"]:
                bad += 1
                print(f"  FAIL {name}({' '.join(flat)}): {out}")
    print(f"{c}: {n} points")
print(f"== {checks} points, {bad} failures")
