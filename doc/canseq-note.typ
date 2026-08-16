#set page(paper: "a4", margin: 2.4cm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading: it => block(above: 1.2em, below: 0.7em)[#it]
#show raw: set text(font: "DejaVu Sans Mono", size: 9pt)

// File names link to the sources on GitHub.
#let repo = "https://github.com/thery/DoubleCover/blob/main/code/Rubik/"
#let src(f) = link(repo + f, raw(f))

// A table: header row in bold, light rules, first column left aligned.
#let tbl(headers, ..rows) = align(center)[
  #table(
    columns: headers.len(),
    stroke: none,
    inset: (x: 7pt, y: 3.5pt),
    align: (col, _) => if col == 0 { left } else { right },
    table.hline(),
    table.header(..headers.map(h => text(weight: "bold", h))),
    table.hline(stroke: 0.5pt),
    ..rows.pos().flatten(),
    table.hline(),
  )
]

#align(center)[
  #text(size: 17pt)[*Counting the move sequences* \ *a redundancy rule leaves*]

  #v(0.9em)
  #text(size: 11pt)[Laurent Théry]

  #v(0.2em)
  #text(size: 9.5pt)[INRIA, Stamp Team \ #link("mailto:Laurent.Thery@inria.fr")[Laurent.Thery\@inria.fr]]
]

#v(1.4em)

#align(center)[#block(width: 88%, inset: (x: 0pt))[
  #set text(size: 9.8pt)
  #set par(justify: true)
  #set align(left)
  *Abstract.* A search of the Rubik's cube tree does not try all eighteen moves
  at every node. A rule drops the moves that can only repeat work. Rokicki,
  Kociemba, Davidson and Dethridge @rokicki2013diameter count what the rule
  leaves with an eighteen by eighteen matrix, collapsed to six by six, and
  read off
  $q(n) = 12 q(n-1) + 18 q(n-2)$. This note gives the same count with two
  numbers instead of a matrix, and states the proof exactly as it is carried
  out in the Rocq prover @rocq in #src("Canseq.v"). Everything here is proved
  there, and nothing there is assumed.
]]

#v(0.6em)

= The rule

A move turns one of the six faces by one of three amounts, so there are
eighteen moves. Number the faces $0, 1, 2, 3, 4, 5$ in the order
$U, R, F, D, L, B$. Opposite faces are then three apart: the opposite of $f$ is
$f + 3$ modulo six.

Two moves in a row are wasteful in two cases. Turning the same face twice in a
row is the same as one turn of that face, so it is forbidden. Turning two
opposite faces commutes, so the two orders give the same position, and one of
them may be forbidden. Which one is a free choice, and the choice made here is
to keep the order the faces are numbered in.

So after a move of face $f$, a move of face $g$ is allowed when

$ g != f quad "and" quad g != f + 3. $

The second condition needs no modular arithmetic. If $f$ is one of $U, R, F$
then $f + 3$ is a face and it is the opposite one. If $f$ is one of $D, L, B$
then $f + 3$ is six or more, so it is no face at all and the condition is
free. This is `allowed` in #src("Canseq.v"), and it is the rule the search
itself uses, `okfc` in #src("Searchr.v").

Counting successors: one of $U, R, F$ is followed by four faces, hence by
twelve moves; one of $D, L, B$ is followed by five faces, hence by fifteen.

= The amount of a turn is free

The rule looks at faces only. A sequence of $n$ moves is therefore a sequence
of $n$ faces obeying the rule, together with one of three amounts for each
move, and these choices are independent. Writing $p(n)$ for the number of face
sequences of length $n$ that obey the rule, and $q(n)$ for the number of move
sequences,

$ q(n) = 3^n p(n). $

Faces are what has to be counted. The factor $3^n$ never interacts with the
rule again.

= Two classes of face

Call $U, R, F$ the *first three* faces and $D, L, B$ the *last three*. The rule
treats all three faces of a class alike: what is forbidden after $f$ is $f$
itself, and the opposite face when $f$ is one of the first three. So the number
of continuations depends on the class of $f$ and not on $f$.

Let $a(n)$ be the number of face sequences of length $n$ that obey the rule and
begin with one of $D, L, B$, and $b(n)$ the number of those that begin with one
of $U, R, F$. Length one gives $a(1) = b(1) = 3$. Counting the successors of
each class,

$ a(n+1) = 2 a(n) + 3 b(n), quad quad b(n+1) = 2 a(n) + 2 b(n). $

The first says that a sequence beginning with one of $D, L, B$ is that face
followed by a sequence beginning with any of its five successors, two of them
in its own class and three in the other. The second says the same for a
sequence beginning with one of $U, R, F$, which has two successors in each
class.

Adding, $p(n) = a(n) + b(n)$, and eliminating $a$ and $b$ between the two lines,

$ p(n+2) = 4 p(n+1) + 2 p(n), quad quad q(n+2) = 12 q(n+1) + 18 q(n). $

The second is the published recurrence. It is the first multiplied by $3^2$ on
one side and $3$ on the other.

= What is counted, and the one bijection

Fix a face $f$ and let $c_n (f)$ be the number of face sequences of length $n$
that obey the rule and may follow a move of face $f$. So $c_0 (f) = 1$, the
empty sequence, and the sequences of length $n + 1$ that obey the rule are
counted by $sum_f c_n (f)$: choose the first face, then a continuation.

The one step that is not arithmetic is this.

#block(inset: (left: 1.2em))[
  *Lemma 1.* $ c_(n+1) (f) = sum_(g "allowed after" f) c_n (g). $
]

Peel the first face off. A sequence counted on the left is a face $g$ allowed
after $f$, followed by a sequence of length $n$ allowed after $g$; putting the
two back together is the inverse. The map is a bijection, so the two sides
count the same set. In #src("Canseq.v") this is `cntS`, and it is where the
work is: the sum over sequences of length $n + 1$ is reindexed along
$(g, s) |-> g :: s$, and the sum over pairs is then split into a sum over $g$
of a sum over $s$.

= The induction

#block(inset: (left: 1.2em))[
  *Lemma 2.* $ 3 c_n (f) = cases(
    b(n+1) & "if" f "is one of" U\, R\, F,
    a(n+1) & "if" f "is one of" D\, L\, B.
  ) $
]

The factor three is the three faces of a class: $a$ and $b$ count sequences,
and a sequence is a first face and then a continuation, so $a$ and $b$ are
three times a continuation count.

The proof is by induction on $n$. For $n = 0$ both sides are three, since
$c_0 (f) = 1$ and $a(1) = b(1) = 3$. For the step, apply Lemma 1 and count the
successors of $f$ by class. Let $u$ be any of $U, R, F$ and $d$ any of
$D, L, B$; by the induction hypothesis $3 c_n (u) = b(n+1)$ and
$3 c_n (d) = a(n+1)$, whichever ones are picked. If $f$ is one of $U, R, F$ it
has two successors in each class, so

$ 3 c_(n+1) (f) = 2 dot 3 c_n (u) + 2 dot 3 c_n (d)
  = 2 b(n+1) + 2 a(n+1) = b(n+2). $

If $f$ is one of $D, L, B$ it has three successors in the first class and two
in the last, so $3 c_(n+1) (f) = 3 b(n+1) + 2 a(n+1) = a(n+2)$. Those are the
two lines of Section 3. This is `cntE`, and in Rocq the six faces are taken one
by one: six goals, each of them arithmetic.

Two consequences follow by cancelling the factor three.

#block(inset: (left: 1.2em))[
  *Corollary.* $c_n (f) = c_n (g)$ whenever $f$ and $g$ are in the same class.
  #linebreak()
  *Theorem.* $sum_f c_n (f) = p(n+1)$, and $p$ obeys the recurrence of
  Section 3.
]

These are `cnt_class`, `canseq_pc` and `canseq_rec`. `Print Assumptions` on
them reports *closed under the global context*: no axiom, no hypothesis, no
computation left to a table.

= The values

#tbl(([length], [face sequences $p$], [move sequences $q$]),
  ([1], [6], [18]),
  ([2], [27], [243]),
  ([3], [120], [3 240]),
  ([4], [534], [43 254]),
  ([5], [2 376], [577 368]),
)

The last column is Table 5.1 of @rokicki2013diameter. The two are the same
count: $3^4 dot 534 = 43 thin 254$ and $3^5 dot 2376 = 577 thin 368$. In
#src("Canseq.v") the index is shifted by one, `pc n` and `qc n` being the
counts at length $n + 1$, because `cnt` counts what follows a face.

The growth from one length to the next tends to the larger root of
$x^2 = 12 x + 18$, which is $6 + sqrt(54) = 13.348 dots$

= What the count does not say

This is the size of the tree the rule leaves. It is not the size of the tree a
search walks, because a search also has a table that cuts branches. The two
differ by a great deal. At length nineteen the recurrence gives
$3.18 dot 10^21$ move sequences, while the depth-nineteen run described in the
companion note visited $146 thin 065 thin 078 thin 152$ positions, about
$2 dot 10^10$ times fewer. The rule alone does not make the search possible;
the table does.

What the rule does decide is the shape of the work. A second move that turns
one of $D, L, B$ leaves fifteen branches where the others leave twelve, and
that is why the two pieces of the run that begin that way are the long ones.

#v(0.8em)

*The sources* are at
#link("https://github.com/thery/DoubleCover/tree/main/code/Rubik")[`github.com/thery/DoubleCover/code/Rubik`],
the count in #src("Canseq.v"). The companion note, `doc/rubik20-note.typ`,
describes the search itself.

#pagebreak(weak: true)

#bibliography("rubik20-note.bib", title: [References], style: "springer-mathphys")
