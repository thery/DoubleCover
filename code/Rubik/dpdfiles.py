#!/usr/bin/env python3
# The local files each theorem really uses, read off unfold.dpd and fold.dpd,
# against the files its Require closure pulls in.
import os, re
here = {f[:-2] for f in os.listdir('.') if f.endswith('.v')}
# generated: GENERATED in the header, or not in git (P1Fdec, P1Table)
tracked = set(os.popen('git ls-files "*.v"').read().split())
gen = {m for m in here if m + '.v' not in tracked
       or 'GENERATED' in ''.join(open(m + '.v').readlines()[:4]).upper()}
def used(dpd):
    return {p for p in re.findall(r'path="([^".]*)', open(dpd).read())
            if p in here}
def closure(root):
    dep = {}
    for m in here:
        s = re.sub(r'\(\*.*?\*\)', '', open(m + '.v').read(), flags=re.S)
        dep[m] = {w.split('.')[-1] for r in re.findall(
            r'Require\s+(?:Import|Export)?\s*([^.]*(?:\.\w[^.]*)*)\.\s', s) for w in r.split()
            if w.split('.')[-1] in here}
    seen, st = set(), [root]
    while st:
        x = st.pop()
        if x not in seen:
            seen.add(x); st += dep[x]
    return seen
def lines(S): return sum(sum(1 for _ in open(m + '.v')) for m in S)
lb = closure('Diam20') | gen
for dpd, root in (('unfold.dpd', 'RowCubDone'), ('fold.dpd', 'RowFoldCubDone')):
    u, c = used(dpd) | {root}, closure(root)
    print(f'{root}: required {len(c - lb)}, used {len(u - lb)} '
          f'({lines(u - lb)} lines), not in the lower bound')
    print('  required but unused:', ' '.join(sorted(c - u - lb)))
