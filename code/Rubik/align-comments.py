#!/usr/bin/env python3
"""Align the closing ``*)`` of block comments to column 80 in Coq/Rocq files.

House style for this development (see the project memory / CLAUDE notes):

  * every source line is at most 80 characters, AND
  * for a multi-line block comment ``(* ... *)`` the closing ``*)`` is padded
    so that the ``)`` lands EXACTLY on column 80 (the ``*`` on column 79).

If some lines of a block stop short of column 80 and others reach it, the
right margin "waves"; this script straightens it.

What it does
------------
For every line that ends in ``*)`` preceded by at least one space (i.e. an
alignment line, not an inline ``foo. (* note *)``), it rewrites the run of
spaces before ``*)`` so the line is exactly 80 characters:

    <text><spaces>*)      ->      <text> padded so ``)`` is at column 80

A line already 80 chars with a single trailing space is left untouched.

Lines whose *text* already extends past column 78 cannot be closed at column
80 by padding alone; these are REPORTED (never silently mangled) so you can
reword them by hand.

Usage
-----
    ./align-comments.py [FILE ...]        fix files in place (default: *.v in cwd)
    ./align-comments.py --check [FILE ...]  report only, exit 1 if any problem
    ./align-comments.py --diff  [FILE ...]  show what would change, exit 1 if any

Exit status is non-zero when (a) ``--check``/``--diff`` finds work to do, or
(b) any file still contains lines that need manual rewording. Suitable as a
pre-commit hook or CI gate.
"""
import re
import sys
import glob

WIDTH = 80
# text (non-greedy), then a run of >=1 spaces, then the closing "*)".
PAT = re.compile(r'^(.*?)( +)\*\)$')


def fix_line(line):
    """Return (new_line, status).

    status is 'ok' (unchanged/aligned) or 'fixed' (repadded).  Lines whose
    text is too long to close at column 80 are left untouched here and caught
    afterwards by the generic over-length check in ``process``.
    """
    m = PAT.match(line)
    if not m:
        return line, 'ok'
    core, spaces = m.group(1), m.group(2)
    # Leave genuine inline comments that are already within the margin alone.
    if len(spaces) == 1 and len(line) == WIDTH:
        return line, 'ok'
    pad = WIDTH - 2 - len(core)      # so len(core)+pad+len("*)") == WIDTH
    if pad < 0:
        return line, 'ok'            # can't pad; reported as over-length later
    new = core + (' ' * pad) + '*)'
    return new, ('ok' if new == line else 'fixed')


def process(path, mode):
    with open(path) as f:
        lines = f.read().split('\n')
    out, fixed, overflow = [], [], []
    for i, line in enumerate(lines, 1):
        new, status = fix_line(line)
        out.append(new)
        if status == 'fixed':
            fixed.append(i)
    if mode == 'fix' and fixed:
        with open(path, 'w') as f:
            f.write('\n'.join(out))
    # Any remaining over-long line (glued-*) overflow, long comment text, or
    # over-long code) can only be fixed by hand -- report, never mangle.
    overflow = [(i, len(l), l) for i, l in enumerate(out, 1) if len(l) > WIDTH]
    return fixed, overflow


def main(argv):
    mode = 'fix'
    args = []
    for a in argv:
        if a == '--check':
            mode = 'check'
        elif a == '--diff':
            mode = 'diff'
        elif a in ('-h', '--help'):
            print(__doc__)
            return 0
        else:
            args.append(a)
    files = args or sorted(glob.glob('*.v'))
    if not files:
        print('no files given and no *.v in cwd', file=sys.stderr)
        return 2

    problems = 0
    for path in files:
        fixed, overflow = process(path, mode)
        if fixed:
            verb = 'would repad' if mode != 'fix' else 'repadded'
            print(f'{path}: {verb} {len(fixed)} line(s): '
                  f'{", ".join(map(str, fixed))}')
            if mode != 'fix':
                problems += 1
        if overflow:
            problems += 1
            print(f'{path}: {len(overflow)} line(s) over {WIDTH} chars, need '
                  f'MANUAL rewrap/rewording (comment text, glued *), or code):')
            for ln, length, text in overflow:
                print(f'  L{ln} (len {length}): {text}')
    return 1 if problems else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
