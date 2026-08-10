#!/usr/bin/env python3
# Report Require Import entries that contribute no reference.
#
# Reads the .glob files rocq writes beside each .vo, so it costs nothing and
# compiles nothing.  A .glob records every identifier occurrence with the
# library it came from; the Require line itself emits an entry of kind "lib",
# which is why those are skipped.
#
# CANDIDATES, NOT A VERDICT.  A module can still be needed for a coercion, a
# canonical structure or an instance, none of which .glob attributes.  Check
# a removal by compiling, once, at the end.
#
#   ./unusedreq.py            every file with a .glob
#   ./unusedreq.py Fast.v     just that one

import glob, os, re, sys


def requires(path):
    """The Rubik modules a file requires, in order."""
    text = re.sub(r"\(\*.*?\*\)", " ", open(path, errors="ignore").read(), flags=re.S)
    names = []
    for m in re.finditer(
        r"^\s*(?:From\s+(\S+)\s+)?Require\s+(?:Import|Export)?\s*([^.]*)\.", text, re.M
    ):
        if m.group(1) in (None, "Rubik"):
            names += m.group(2).split()
    return names


def referenced(globfile):
    """The Rubik modules a file actually refers to."""
    libs = set()
    for line in open(globfile, errors="ignore"):
        if not line.startswith("R"):
            continue
        parts = line.split()
        if len(parts) >= 3 and parts[-1] != "lib" and parts[1].startswith("Rubik."):
            libs.add(parts[1].split(".", 1)[1])
    return libs


def main(argv):
    sources = argv[1:] or sorted(glob.glob("*.v"))
    rows, seen = [], 0
    for src in sources:
        stem = os.path.splitext(src)[0]
        if not os.path.exists(stem + ".glob"):
            continue
        seen += 1
        used = referenced(stem + ".glob")
        unused = [r for r in requires(src)
                  if r not in used and os.path.exists(r + ".v")]
        if unused:
            rows.append((stem, len(requires(src)), unused))
    rows.sort(key=lambda r: -len(r[2]))
    for stem, total, unused in rows:
        print("%-16s %2d of %2d unused: %s" % (stem, len(unused), total,
                                               " ".join(unused)))
    print("\n%d of %d files flagged" % (len(rows), seen))


if __name__ == "__main__":
    main(sys.argv)
