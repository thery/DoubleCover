#!/usr/bin/env python3
"""rocqtest.py [rocq dir] [stage..]: compares the passes written in Rocq
(code/elpiDiff/rocq) with the Elpi ones, on every reference case. The primal
functions of a case are printed as Rocq terms (torocq.elpi); Rocq computes,
for each, its diagnostic and its derivative programs printed as L2 (Dump.v);
they must be the lines of `elpi … -exec dump -- <stage> <mode>`, and the
diagnostics those of Elpi.

A stage is derivative-tangent, derivative-adjoint, … (default: all the stages
the Rocq development defines).
"""
import os, re, subprocess, sys, tempfile

ROCQ = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "rocq")
CODE = os.path.dirname(ROCQ)
TOOLS = os.path.dirname(os.path.abspath(__file__))
CASES = os.environ.get("CASES", os.path.expanduser("~/claudeExp/elpi/cases"))

# stage -> (Elpi dump arguments, Rocq expression of a well-formed function f)
STAGES = {
    "derivative-tangent": (["derivative", "tangent"], "tangent (annotate false (normalize {f}))"),
    "derivative-adjoint": (["derivative", "adjoint"], "adjoint false (annotate false (normalize {f}))"),
    "derivative-adjoint-value": (["derivative", "adjoint-value"], "adjoint true (annotate true (normalize {f}))"),
    "simplified-tangent": (["simplified", "tangent"], "simplify (tangent (annotate false (normalize {f})))"),
    "simplified-adjoint": (["simplified", "adjoint"], "simplify (adjoint false (annotate false (normalize {f})))"),
    "simplified-adjoint-value": (["simplified", "adjoint-value"], "simplify (adjoint true (annotate true (normalize {f})))"),
}
# stage -> (Elpi main mode, Rocq expression of a function, before lowering)
CXX = {
    "cxx-tangent": ("tangent", "simplify (tangent (annotate false (normalize {f})))"),
    "cxx-adjoint": ("adjoint", "simplify (adjoint false (annotate false (normalize {f})))"),
    "cxx-adjoint-value": ("adjoint-value", "simplify (adjoint true (annotate true (normalize {f})))"),
}
MODULES = "Syntax Anf Normalize WellFormed Annotate Derivative Tangent Dump"
avail = [s for s in STAGES if (("adjoint" not in s or os.path.exists(os.path.join(ROCQ, "Adjoint.vo")))
                              and ("simplified" not in s or os.path.exists(os.path.join(ROCQ, "Simplify.vo"))))]
if os.path.exists(os.path.join(ROCQ, "Cxx.vo")): avail += list(CXX)
stages = sys.argv[2:] or avail
if os.path.exists(os.path.join(ROCQ, "Adjoint.vo")): MODULES += " Adjoint"
if os.path.exists(os.path.join(ROCQ, "Simplify.vo")): MODULES += " Simplify"
if os.path.exists(os.path.join(ROCQ, "Cxx.vo")): MODULES += " Lower Cxx"

tmp = tempfile.mkdtemp()
runner = os.path.join(tmp, "run.elpi")
open(runner, "w").write("accumulate torocq.\naccumulate primal.\n")


def elpi(case, *args, extra=()):
    out = subprocess.run(["elpi", "-I", CODE, "-I", TOOLS, "-I", case, *extra, "-exec", *args],
                         capture_output=True, text=True, stdin=subprocess.DEVNULL)
    return [l for l in (out.stdout + out.stderr).splitlines()
            if l and not re.match(r"(Success:|Constraints:|State:|Time:|.*time:)", l)]


def blocks(lines):
    """The functions of a dump: name -> lines (a function starts unindented)."""
    out, cur = {}, None
    for l in lines:
        if not l.startswith(" ") and not l.startswith("//"):
            cur = l.split("(")[0]; out[cur] = [l]
        elif cur:
            out[cur].append(l)
    return out


def rocq_strings(text):
    return [s.replace('""', '"') for s in re.findall(r'"((?:[^"]|"")*)"', text)]


total = bad = 0
for c in sorted(os.listdir(CASES)):
    case = os.path.join(CASES, c)
    if not os.path.exists(os.path.join(case, "primal.elpi")):
        continue
    defs = elpi(case, "to-rocq", extra=[runner])
    names = [re.match(r"Definition (\S+)_fn", d).group(1) for d in defs]
    # the diagnostics of Elpi
    diag = {}
    dfile = os.path.join(case, "diagnostics.txt")
    if os.path.exists(dfile):
        for l in open(dfile):
            n, m = l.rstrip("\n").split(": ", 1); diag[n] = m
    src = ["From Stdlib Require Import String List ZArith.", f"From ElpiDiff Require Import {MODULES}.",
           "Import ListNotations.", "Open Scope Z_scope.", "Open Scope string_scope.", "Set Printing Depth 1000000."] + defs
    for n in names:
        src.append(f'Compute (well_formed (normalize {n}_fn)).')
    wf = [n for n in names if n not in diag]
    for st in stages:
        if st in CXX:
            if wf:
                fs = "; ".join("(" + CXX[st][1].format(f=n + "_fn") + ")" for n in wf)
                src.append(f'Compute header_string "cases/{c}/primal.elpi" (lower_all [{fs}]).')
            continue
        for n in wf:
            src.append(f"Compute pr_dfunction ({STAGES[st][1].format(f=n + '_fn')}).")
    vfile = os.path.join(tmp, "T" + re.sub(r"\W", "_", c) + ".v")
    open(vfile, "w").write("\n".join(src) + "\n")
    out = subprocess.run(["rocq", "compile", "-R", ROCQ, "ElpiDiff", vfile], capture_output=True, text=True)
    if out.returncode:
        print(f"{c}: Rocq error\n{out.stderr[:1500]}"); bad += 1; continue
    results = re.split(r"\n\s*= ", "\n" + out.stdout)[1:]
    k = 0
    for n in names:                                   # diagnostics
        r = results[k]; k += 1; total += 1
        rocq_d = "ok" if r.startswith("Ok") else (rocq_strings(r) or ["?"])[0]
        elpi_d = diag.get(n, "ok")
        if rocq_d != elpi_d:
            bad += 1; print(f"  {c} {n}: diagnostic Rocq «{rocq_d}» Elpi «{elpi_d}»")
    for st in stages:
        if st in CXX:
            if not wf:
                continue
            out_dir = os.path.join(tmp, c + "-" + st); os.makedirs(out_dir, exist_ok=True)
            subprocess.run(["elpi", "-I", CODE, os.path.join(CASES, c, "primal.elpi"), "-exec", "main", "--",
                            f"cases/{c}", CXX[st][0], out_dir], capture_output=True, text=True,
                           stdin=subprocess.DEVNULL, cwd=os.path.dirname(CASES))
            want = open(os.path.join(out_dir, CXX[st][0] + ".hpp")).read()
            got = rocq_strings(results[k]); k += 1; total += 1
            got = got[0] if got else ""
            if got != want:
                bad += 1; print(f"  {c} {st}: the header differs")
                import difflib
                for l in list(difflib.unified_diff(want.splitlines(), got.splitlines(), "elpi", "rocq", lineterm=""))[:12]:
                    print("    " + l)
            continue
        eb = blocks(elpi(case, "dump", "--", *STAGES[st][0], extra=[os.path.join(case, "primal.elpi")]))
        for n in names:
            if n in diag:
                continue
            got = rocq_strings(results[k]); k += 1; total += 1
            mode = STAGES[st][0][1].replace("-", "_")
            want = eb.get(f"{n}_{mode}", ["(missing in Elpi)"])
            if got != want:
                bad += 1
                print(f"  {c} {n} {st}: differs")
                import difflib
                for l in list(difflib.unified_diff(want, got, "elpi", "rocq", lineterm=""))[:12]:
                    print("    " + l)
    print(f"{c}: {len(names)} functions")
print(f"== {total} comparisons ({', '.join(stages)} and diagnostics), {bad} differences")
