#!/usr/bin/env python3
# canon.py FILE: the generated header with the locals of each function (t<n>,
# i<n>, r<n>, with their _dot/_bar/_tape suffixes) renamed by order of first
# occurrence, so that two headers equal modulo binder names print the same.
import re, sys
text = open(sys.argv[1]).read()
out = []
for chunk in re.split(r'(?=^template <typename T>)', text, flags=re.M):
    names = {}
    def rename(m):
        k = m.group(0)
        if k not in names:
            names[k] = f"{m.group(1)}#{sum(1 for v in names if v[0] == k[0])}"
        return names[k]
    out.append(re.sub(r'(?<![\w#])([tir])\d+(?![\d])', rename, chunk))
sys.stdout.write("".join(out))
