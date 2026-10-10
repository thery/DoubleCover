#!/usr/bin/env python3
"""Link the Rocq names in the Markdown documentation to their definitions.

mdlinks.py [code dir]: in README.md and rocq/{README,DEFINITIONS,TUTORIAL}.md,
every inline `name` that is defined (Lemma, Theorem, Definition, ...) in
exactly one rocq/*.v file becomes [`name`](path/File.v#Lline), a link GitHub
opens at the definition. Fenced code blocks and existing links are left
alone. Run it again after editing the .v files: it refreshes the line
numbers of the links it made.
"""
import os
import re
import sys

CODE = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else
                       os.path.join(os.path.dirname(__file__), ".."))
ROCQ = os.path.join(CODE, "rocq")
KW = (r"Lemma|Theorem|Corollary|Definition|Fixpoint|Inductive|Record|Fact|"
      r"Remark|Ltac|CoInductive|Class|Instance|Notation|Variant|Scheme")
DEF = re.compile(r"^\s*(?:Local\s+|Program\s+)?(?:" + KW + r")\s+([A-Za-z_][\w']*)")

defs = {}
for f in sorted(os.listdir(ROCQ)):
    if not f.endswith(".v") or f.startswith("rocq_mcp_cache"):
        continue
    for n, line in enumerate(open(os.path.join(ROCQ, f), encoding="utf-8"), 1):
        m = DEF.match(line)
        if m:
            defs.setdefault(m.group(1), []).append((f, n))
unique = {k: v[0] for k, v in defs.items() if len(v) == 1}

# An inline code span, possibly already linked by a previous run.
SPAN = re.compile(r"\[`([A-Za-z_][\w']*)`\]\(([^)]*\.v#L\d+)\)|(?<![\[`])`([A-Za-z_][\w']*)`(?!\])")


def link(md, prefix):
    out, fence, count = [], False, 0
    for line in open(md, encoding="utf-8").read().split("\n"):
        if line.lstrip().startswith("```"):
            fence = not fence
            out.append(line)
            continue
        if fence:
            out.append(line)
            continue

        def rep(m):
            nonlocal count
            name = m.group(1) or m.group(3)
            if name not in unique:
                return m.group(0)
            f, n = unique[name]
            count += 1
            return f"[`{name}`]({prefix}{f}#L{n})"
        out.append(SPAN.sub(rep, line))
    open(md, "w", encoding="utf-8").write("\n".join(out))
    return count


for md, prefix in [(os.path.join(CODE, "README.md"), "rocq/"),
                   (os.path.join(ROCQ, "README.md"), ""),
                   (os.path.join(ROCQ, "DEFINITIONS.md"), ""),
                   (os.path.join(ROCQ, "TUTORIAL.md"), "")]:
    print(f"{os.path.relpath(md, CODE)}: {link(md, prefix)} links")
