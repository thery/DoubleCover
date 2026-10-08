#!/usr/bin/env python3
"""adjspectest.py [rocq dir]: checks the statement of the adjoint theorem
(rocq/AdjointSpec.v, AdjointMode.v) on every reference case, symbolically. For
each primal function f, both modes (adjoint, adjoint-value), Rocq runs over
the reals, on symbolic arguments x, initial adjoints xb, seed yb and tangent
dx, the simplified tangent program and the simplified adjoint program, and
proves with `ring` that <tangent output, yb> = <seed dx, g>, g the gradient of
adjoint_output, that g has one real per real of x, and that adjoint-value
gives the value back (value_given) unless f writes an inout argument. The
integer arguments are fixed (INT). The functions the tool refuses (not
well-formed) are reported and skipped.
"""
import os, re, subprocess, sys, tempfile

ROCQ = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "rocq")
CODE = os.path.dirname(ROCQ)
TOOLS = os.path.dirname(os.path.abspath(__file__))
CASES = os.environ.get("CASES", os.path.expanduser("~/claudeExp/elpi/cases"))
INT = 3

HEADER = r"""From Stdlib Require Import String ZArith List Bool Reals.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Normalize WellFormed
  Annotate Tangent Adjoint Simplify DualsDerive AdjointSpec.
From ElpiDiff Require TangentTop.
Import ListNotations. Open Scope list_scope.

Definition check (cv : bool) f x xb yb dx : Prop :=
 match exec_dfunction reals (simplify (tangent (annotate false (normalize f))))
         (TangentTop.tangent_inputs (TangentTop.decls f) x dx),
       exec_dfunction reals (simplify (adjoint cv (annotate cv (normalize f))))
         (adjoint_inputs (TangentTop.decls f) x xb yb) with
 | Some o1, Some o2 =>
     match TangentTop.tangent_output (TangentTop.decls f) o1, adjoint_output (TangentTop.decls f) x xb o2 with
     | Some (v, w), Some g =>
         dotl (reals_of_val w) yb = dotl (TangentTop.seed (TangentTop.decls f) x dx) g /\
         length g = length (reals_of_args x) /\
         (cv = true -> writes_inout (TangentTop.decls f) = false -> value_given (TangentTop.decls f) o2 = Some v)
     | _, _ => False end
 | _, _ => False end.

Ltac go := intros; cbv -[Rplus Rmult Rminus Ropp Rdiv Rinv sin cos exp ln sqrt pow IZR];
  repeat split; try discriminate; try (intros; reflexivity); try ring.
"""


def elpi(case, *args, extra=()):
    out = subprocess.run(["elpi", "-I", CODE, "-I", TOOLS, "-I", case, *extra, "-exec", *args],
                         capture_output=True, text=True, stdin=subprocess.DEVNULL)
    return [l for l in (out.stdout + out.stderr).splitlines()
            if l and not re.match(r"(Success:|Constraints:|State:|Time:|.*time:)", l)]


tmp = tempfile.mkdtemp()
runner = os.path.join(tmp, "run.elpi")
open(runner, "w").write("accumulate torocq.\naccumulate primal.\n")

total = bad = refused = 0
for c in sorted(os.listdir(CASES)):
    case = os.path.join(CASES, c)
    if not os.path.exists(os.path.join(case, "primal.elpi")):
        continue
    for d in elpi(case, "to-rocq", extra=[runner]):
        name = re.match(r"Definition (\S+)_fn", d).group(1)
        args = re.findall(r'Arg "(\w+)" (Real|Integer|Boolean|\(Array (\d+)\)) (\w+)', d)
        x, xs, n = [], [], 0
        for _, t, k, _ in args:
            if t == "Real":
                x.append(f"VReal r{n}"); xs.append(f"r{n}"); n += 1
            elif t == "Integer":
                x.append(f"VInt {INT}")
            elif t == "Boolean":
                x.append("VBool true")
            else:
                l = [f"r{n + j}" for j in range(int(k))]
                x.append("VArray [" + "; ".join(l) + "]"); xs += l; n += int(k)
        res = re.search(r"Body \((Returns Real|Writes \(Var x(\d+)\))\)", d)
        m = 1 if res.group(1) == "Returns Real" else (lambda t: 1 if t[1] == "Real" else int(t[2]))(args[int(res.group(2)) - 1])
        rs = " ".join(xs); xbs = " ".join(f"b{j}" for j in range(n)); dxs = " ".join(f"d{j}" for j in range(n))
        ys = " ".join(f"y{j}" for j in range(m))
        lst = lambda p, k: "[" + "; ".join(f"{p}{j}" for j in range(k)) + "]"
        src = HEADER + d + "\n"
        src += (f"Goal forall (cv : bool) ({rs} {xbs} {ys} {dxs} : R), check cv {name}_fn [{'; '.join(x)}] "
                f"{lst('b', n)} {lst('y', m)} {lst('d', n)}.\nProof. destruct cv; go. Qed.\n")
        v = os.path.join(tmp, "Check.v")
        open(v, "w").write(HEADER + d + f"\nGoal well_formed (normalize {name}_fn) = Ok.\nProof. vm_compute; reflexivity. Qed.\n")
        if subprocess.run(["rocq", "compile", "-R", ROCQ, "ElpiDiff", v], capture_output=True).returncode != 0:
            refused += 1
            print(f"{c} {name}: refused (not well-formed)")
            continue
        open(v, "w").write(src)
        out = subprocess.run(["rocq", "compile", "-R", ROCQ, "ElpiDiff", v], capture_output=True, text=True)
        total += 1
        if out.returncode == 0:
            print(f"{c} {name}: ok")
        else:
            bad += 1
            print(f"{c} {name}: FAIL\n{out.stderr[-1500:]}")
print(f"== {total} functions, {bad} failures ({refused} refused)")
