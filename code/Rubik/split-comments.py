#!/usr/bin/env python3
"""Give every line of a block comment its own ``(* ... *)``.

House style for this development: a comment that spans several lines is
written as one self-contained comment per line, with the closing ``)`` on
column 80, rather than as a single block whose middle lines carry no
delimiter of their own.  So

    (* OUTSIDE the section below, and that is not tidiness.  Inside it the
       context holds p1checkStep, and every trailing `done' then tries
       `assumption'.                                                        *)

becomes

    (* OUTSIDE the section below, and that is not tidiness.  Inside it the   *)
    (* context holds p1checkStep, and every trailing `done' then tries       *)
    (* `assumption'.                                                        *)

What is rewritten
-----------------
Only a comment that starts a line (optional whitespace, then ``(*``), spans
more than one line, and closes at the end of its last line.  Left alone:

  * single-line comments, and comments that follow code on the same line;
  * blocks that already have a ``(*`` on every line -- the file headers;
  * blocks holding a comment inside a comment, since splitting those would
    unbalance the delimiters;
  * blocks with a line whose text cannot fit before column 78, which are
    REPORTED so they can be reworded by hand, never silently mangled.

Indentation inside the block is preserved relative to the comment's own
column, so a displayed command or a table keeps its shape.

Usage
-----
    ./split-comments.py [FILE ...]          rewrite in place
    ./split-comments.py --check [FILE ...]  report only, exit 1 if any work
"""

import sys

WIDTH = 80


def blocks(lines):
    """Yield (start, end) of each own-line block comment, 0-based inclusive."""
    i = 0
    while i < len(lines):
        s = lines[i].lstrip()
        if s.startswith('(*'):
            depth = lines[i].count('(*') - lines[i].count('*)')
            j = i
            while depth > 0 and j + 1 < len(lines):
                j += 1
                depth += lines[j].count('(*') - lines[j].count('*)')
            if depth == 0 and j > i:
                yield i, j
            i = j + 1
        else:
            i += 1


def split_block(lines, i, j):
    """The replacement lines for block i..j, or None to leave it alone."""
    base = len(lines[i]) - len(lines[i].lstrip())
    body = []

    first = lines[i].lstrip()[2:]            # after the opening (*
    body.append(first)
    for k in range(i + 1, j + 1):
        body.append(lines[k])
    last = body[-1].rstrip()
    if not last.endswith('*)'):
        return None
    body[-1] = last[:-2]

    # already one comment per line: nothing to do
    if all(l.lstrip().startswith('(*') for l in body[1:] if l.strip()):
        return None
    # a comment inside the comment would come out unbalanced
    if any('(*' in l or '*)' in l for l in body):
        return None

    # the text column the middle lines are aligned on, relative to the (*
    texts = []
    for n, l in enumerate(body):
        if n == 0:
            texts.append(l.strip())
        else:
            stripped = l.rstrip()
            if not stripped.strip():
                texts.append('')
            else:
                ind = len(stripped) - len(stripped.lstrip())
                texts.append(' ' * max(0, ind - (base + 3)) + stripped.strip())

    texts = reflow(texts, WIDTH - 6 - base)

    out = []
    for t in texts:
        line = ' ' * base + '(* ' + t
        pad = WIDTH - 2 - len(line)
        if pad < 1:
            return None                      # cannot close on column 80
        out.append(line + ' ' * pad + '*)')
    return out


def reflow(texts, width):
    """Rewrap the prose paragraphs to *width*, leaving the rest alone.

    Prose is a run of consecutive lines with no indentation of their own.  A
    line that carries its own indentation is a display -- a command, a table,
    a piece of a goal -- and is left exactly as it is, because rewrapping it
    would destroy the shape that made it worth displaying.
    """
    out, para = [], []

    def flush():
        if not para:
            return
        words, line = ' '.join(para).split(), ''
        for w in words:
            if not line:
                line = w
            elif len(line) + 1 + len(w) <= width:
                line += ' ' + w
            else:
                out.append(line)
                line = w
        if line:
            out.append(line)
        para.clear()

    for t in texts:
        if t.strip() and not t.startswith(' '):
            para.append(t.strip())
        else:
            flush()
            out.append(t)
    flush()
    return out


def do(path, check):
    lines = open(path).read().split('\n')
    todo, skipped, out, at = [], [], [], 0
    for i, j in blocks(lines):
        rep = split_block(lines, i, j)
        if rep is None:
            if any(not l.lstrip().startswith('(*') for l in lines[i + 1:j + 1]
                   if l.strip()):
                skipped.append(i + 1)
            continue
        todo.append((i, j, rep))
    if not todo and not skipped:
        return 0
    if check:
        if todo:
            print('%s: would split %d block(s): %s' %
                  (path, len(todo), ', '.join(str(i + 1) for i, _, _ in todo)))
        if skipped:
            print('%s: %d block(s) left alone (nested, or text past column 78):'
                  ' %s' % (path, len(skipped), ', '.join(map(str, skipped))))
        return 1
    for i, j, rep in todo:
        out.extend(lines[at:i])
        out.extend(rep)
        at = j + 1
    out.extend(lines[at:])
    open(path, 'w').write('\n'.join(out))
    print('%s: split %d block(s)' % (path, len(todo)) +
          ('; %d left alone: %s' % (len(skipped), ', '.join(map(str, skipped)))
           if skipped else ''))
    return 0


def main(argv):
    check = '--check' in argv
    files = [a for a in argv if not a.startswith('-')]
    if not files:
        print('usage: ./split-comments.py [--check] FILE ...', file=sys.stderr)
        return 2
    bad = 0
    for f in files:
        bad |= do(f, check)
    return bad if check else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
