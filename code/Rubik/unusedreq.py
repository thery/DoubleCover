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
# A STARRED candidate is the only kind that changes what a build loads: the
# others are required again by something the file does refer to, so dropping
# them is legibility and nothing else.  Weigh that against the rebuild -- a
# Require in Fold.v costs the twelve checks and the twenty seven slices.
#
#   ./unusedreq.py                    every file with a .glob beside it
#   ./unusedreq.py Fast.v             just that one
#   ./unusedreq.py --globs glob/g     the .glob files are over there instead,
#                                     which is where a set copied off another
#                                     machine lands

import glob, hashlib, os, re, sys

# ssrint63 gives notations and instances and almost no named reference, so it
# is flagged in nearly every file that plainly needs it.  Never a candidate.
NOTATION_ONLY = {"ssrint63"}


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


def current(globfile, src):
    """Was this .glob written from the source that is here now?

    Its first line is DIGEST <md5 of the .v>.  A .glob carried over from
    another machine or an older run answers about a file that no longer
    exists, and every answer it gives is then wrong."""
    with open(globfile, errors="ignore") as f:
        head = f.readline().split()
    if len(head) != 2 or head[0] != "DIGEST":
        return False
    return head[1] == hashlib.md5(open(src, "rb").read()).hexdigest()


def closure(mods):
    """Everything requiring `mods' ends up loading."""
    seen, todo = set(), list(mods)
    while todo:
        m = todo.pop()
        if m in seen or not os.path.exists(m + ".v"):
            continue
        seen.add(m)
        todo += requires(m + ".v")
    return seen


def main(argv):
    globdir = "."
    if len(argv) > 2 and argv[1] == "--globs":
        globdir, argv = argv[2], argv[:1] + argv[3:]
    sources = argv[1:] or sorted(glob.glob("*.v"))
    rows, seen, stale = [], 0, []
    for src in sources:
        stem = os.path.splitext(src)[0]
        gfile = os.path.join(globdir, stem + ".glob")
        if not os.path.exists(gfile):
            continue
        if not current(gfile, src):
            stale.append(stem)
            continue
        seen += 1
        req = requires(src)
        used = referenced(gfile)
        loaded = closure([r for r in req if r in used] + list(NOTATION_ONLY))
        unused = [(r, r not in loaded) for r in req
                  if r not in used and r not in NOTATION_ONLY
                  and os.path.exists(r + ".v")]
        if unused:
            rows.append((stem, len(req), unused))
    rows.sort(key=lambda r: -len(r[2]))
    for stem, total, unused in rows:
        names = " ".join(r + ("*" if outside else "") for r, outside in unused)
        print("%-16s %2d of %2d unused: %s" % (stem, len(unused), total, names))
    print("\n%d of %d files flagged, %d starred (not loaded another way)"
          % (len(rows), seen, sum(o for _, _, u in rows for _, o in u)))
    if stale:
        print("skipped, .glob is from another version of the file: %s"
              % " ".join(stale))


if __name__ == "__main__":
    main(sys.argv)
