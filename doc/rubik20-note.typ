#set page(paper: "a4", margin: 2.4cm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading: it => block(above: 1.2em, below: 0.7em)[#it]
#show raw: set text(font: "DejaVu Sans Mono", size: 9pt)
#show figure.caption: set text(size: 9pt)
// Every drawing sits in a light frame.
#show figure: it => block(width: 100%)[
  #block(width: 100%, stroke: 0.4pt + luma(140), inset: 9pt, radius: 2pt,
         align(center, it.body))
  #v(0.35em)
  #align(center, it.caption)
]

#import "@preview/cetz:0.3.4"

// File names link to the sources on GitHub.
#let repo = "https://github.com/thery/DoubleCover/blob/main/code/Rubik/"
#let src(f) = link(repo + f, raw(f))

// ---- small helpers -------------------------------------------------------

// A figure table: header row in bold, light rules, first column left aligned.
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

// ---- flat drawings, all cetz -------------------------------------------- //

// A 3x3 face of the unfolded cube, top left corner at (ox, oy), stickers
// labelled row by row with the centre given separately.  A label in `hi` is
// shaded.
// The six faces, in tints pale enough to write numbers on.
#let pW = rgb("#f4f4f2")
#let pY = rgb("#faefc4")
#let pG = rgb("#d8eedd")
#let pB = rgb("#dbe4f6")
#let pR = rgb("#f7dcd7")
#let pO = rgb("#fbe7d2")
#let darker(c) = c.darken(22%)

#let s = 0.62
#let flatface(ox, oy, labels, centre, hi: (), tint: pW) = {
  import cetz.draw: *
  let k = 0
  for row in (0, 1, 2) {
    for col in (0, 1, 2) {
      let x = ox + col * s
      let y = oy - row * s
      let centred = row == 1 and col == 1
      let l = if centred { centre } else { labels.at(k) }
      rect((x, y), (x + s, y - s), stroke: 0.4pt,
           fill: if centred or l in hi { darker(tint) } else { tint })
      content((x + s / 2, y - s / 2),
              text(size: 8pt, weight: if centred { "bold" } else { "regular" })[#l])
      if not centred { k = k + 1 }
    }
  }
}

// A single row of three stickers: the top row of a side face.
#let flatrow(ox, oy, labels, tint) = {
  import cetz.draw: *
  for i in (0, 1, 2) {
    let x = ox + i * s
    rect((x, oy), (x + s, oy - s), stroke: 0.4pt, fill: tint)
    content((x + s / 2, oy - s / 2), text(size: 8pt)[#labels.at(i)])
  }
}

// The top face together with the top row of each side face, which is
// everything a turn of the top face moves.
#let topband(y0, u, l, f, r, b) = {
  flatface(3 * s, y0, u, "U", tint: pW)
  flatrow(0, y0 - 3 * s, l, pO)
  flatrow(3 * s, y0 - 3 * s, f, pG)
  flatrow(6 * s, y0 - 3 * s, r, pR)
  flatrow(9 * s, y0 - 3 * s, b, pB)
}

// The search tree: a node, an edge, a centred caption under a node.
#let tnode(x, y) = {
  import cetz.draw: *
  circle((x, y), radius: 0.07, fill: black)
}
#let tedge(x1, y1, x2, y2) = {
  import cetz.draw: *
  line((x1, y1), (x2, y2), stroke: 0.5pt)
}
#let tlbl(x, y, body) = {
  import cetz.draw: *
  content((x, y), text(size: 8.5pt, body))
}

// ---- the cube in perspective, drawn with cetz --------------------------- //
// Vector sum and scaling, on plain (x, y) pairs.
#let vadd(p, q) = (p.at(0) + q.at(0), p.at(1) + q.at(1))
#let vmul(k, p) = (k * p.at(0), k * p.at(1))

// One face of the cube: a parallelogram at `o` spanned by `a` (columns, left
// to right) and `b` (rows, top to bottom), cut into nine stickers and
// labelled row by row, the centre last.
#let face3d(o, a, b, labels, centre, shade, hi: ()) = {
  import cetz.draw: *
  line(o, vadd(o, a), vadd(vadd(o, a), b), vadd(o, b),
       close: true, fill: shade, stroke: 0.7pt)
  let k = 0
  for row in (0, 1, 2) {
    for col in (0, 1, 2) {
      let centred = row == 1 and col == 1
      let l = if centred { centre } else { labels.at(k) }
      let p = vadd(vadd(o, vmul(col / 3, a)), vmul(row / 3, b))
      let c = vadd(vadd(o, vmul((col + 0.5) / 3, a)), vmul((row + 0.5) / 3, b))
      if centred or l in hi {
        line(p, vadd(p, vmul(1 / 3, a)), vadd(vadd(p, vmul(1 / 3, a)), vmul(1 / 3, b)),
             vadd(p, vmul(1 / 3, b)), close: true, fill: darker(shade), stroke: 0.4pt)
      }
      content(c, text(size: 7.5pt, weight: if centred { "bold" } else { "regular" })[#l])
      if not centred { k = k + 1 }
    }
  }
  for i in (1, 2) {
    line(vadd(o, vmul(i / 3, a)), vadd(vadd(o, vmul(i / 3, a)), b), stroke: 0.4pt)
    line(vadd(o, vmul(i / 3, b)), vadd(vadd(o, a), vmul(i / 3, b)), stroke: 0.4pt)
  }
}

// The six colours, and a face drawn as nine coloured stickers.
#let cW = luma(252)
#let cY = rgb("#f0cf3c")
#let cG = rgb("#2f9e52")
#let cB = rgb("#3060bd")
#let cR = rgb("#cf3b2c")
#let cO = rgb("#e8862a")

#let face3dc(o, a, b, cols) = {
  import cetz.draw: *
  for row in (0, 1, 2) {
    for col in (0, 1, 2) {
      let p = vadd(vadd(o, vmul(col / 3, a)), vmul(row / 3, b))
      line(p, vadd(p, vmul(1 / 3, a)), vadd(vadd(p, vmul(1 / 3, a)), vmul(1 / 3, b)),
           vadd(p, vmul(1 / 3, b)), close: true,
           fill: cols.at(row * 3 + col), stroke: 0.5pt)
    }
  }
  line(o, vadd(o, a), vadd(vadd(o, a), b), vadd(o, b), close: true, stroke: 0.8pt)
}

// A whole cube in perspective, its three visible faces given as colours.
#let cube3dc(dx, up, front, right) = {
  let w = (0, 1.55)
  let rb = (1.35, 0.75)
  let lb = (-1.35, 0.75)
  let ft = vadd((dx, 0), w)
  face3dc(vadd(vadd(ft, rb), lb), vmul(-1, lb), vmul(-1, rb), up)
  face3dc(vadd(ft, lb), vmul(-1, lb), vmul(-1, w), front)
  face3dc(ft, rb, vmul(-1, w), right)
}

// A face whose nine stickers are marked by the kind of piece they sit on:
// corner at the four corners, edge at the four sides, centre in the middle.
#let cCor = rgb("#c9d6e8")
#let cEdg = rgb("#eee2c8")
#let cCen = luma(170)
#let face3dt(o, a, b, centre) = {
  import cetz.draw: *
  for row in (0, 1, 2) {
    for col in (0, 1, 2) {
      let corner = (row != 1) and (col != 1)
      let centred = row == 1 and col == 1
      let p = vadd(vadd(o, vmul(col / 3, a)), vmul(row / 3, b))
      let c = vadd(vadd(o, vmul((col + 0.5) / 3, a)), vmul((row + 0.5) / 3, b))
      line(p, vadd(p, vmul(1 / 3, a)), vadd(vadd(p, vmul(1 / 3, a)), vmul(1 / 3, b)),
           vadd(p, vmul(1 / 3, b)), close: true, stroke: 0.5pt,
           fill: if centred { cCen } else if corner { cCor } else { cEdg })
      content(c, text(size: 7.5pt, weight: if centred { "bold" } else { "regular" })[
        #if centred { centre } else if corner { "c" } else { "e" }])
    }
  }
  line(o, vadd(o, a), vadd(vadd(o, a), b), vadd(o, b), close: true, stroke: 0.8pt)
}

#let cube3dt(dx) = {
  let w = (0, 1.8)
  let rb = (1.55, 0.87)
  let lb = (-1.55, 0.87)
  let ft = vadd((dx, 0), w)
  face3dt(vadd(vadd(ft, rb), lb), vmul(-1, lb), vmul(-1, rb), "U")
  face3dt(vadd(ft, lb), vmul(-1, lb), vmul(-1, w), "F")
  face3dt(ft, rb, vmul(-1, w), "R")
}

// The numbered cube: up, front and right, at a horizontal offset.
#let cube3dn(dx, hi: ()) = {
  let w = (0, 1.95)
  let rb = (1.7, 0.95)
  let lb = (-1.7, 0.95)
  let ft = vadd((dx, 0), w)
  let bt = vadd(vadd(ft, rb), lb)
  face3d(bt, vmul(-1, lb), vmul(-1, rb), (0, 1, 2, 3, 4, 5, 6, 7), "U",
         pW, hi: hi)
  face3d(vadd(ft, lb), vmul(-1, lb), vmul(-1, w),
         (16, 17, 18, 19, 20, 21, 22, 23), "F", pG, hi: hi)
  face3d(ft, rb, vmul(-1, w), (24, 25, 26, 27, 28, 29, 30, 31), "R",
         pR, hi: hi)
}

// One small cubie in the same perspective, with one of its three visible
// stickers marked.  Used to show what the summary of a position records.
#let cubie(o, marked) = {
  import cetz.draw: *
  let w = (0, 0.8)
  let rb = (0.7, 0.39)
  let lb = (-0.7, 0.39)
  let ft = vadd(o, w)
  let quad(p, a, b, fill) = line(p, vadd(p, a), vadd(vadd(p, a), b), vadd(p, b),
                                 close: true, fill: fill, stroke: 0.6pt)
  let mark(which) = if which == marked { luma(120) } else { white }
  quad(vadd(vadd(ft, rb), lb), vmul(-1, lb), vmul(-1, rb), mark("top"))
  quad(vadd(ft, lb), vmul(-1, lb), vmul(-1, w), mark("front"))
  quad(ft, rb, vmul(-1, w), mark("right"))
}

#align(center)[
  #text(size: 17pt)[*God's number is at least 20:* \ *proving it in Rocq*]

  #v(0.9em)
  #text(size: 11pt)[Laurent Théry]

  #v(0.2em)
  #text(size: 9.5pt)[INRIA, Stamp Team \ #link("mailto:Laurent.Thery@inria.fr")[Laurent.Thery\@inria.fr]]
]

#v(1.4em)

#align(center)[#block(width: 88%, inset: (x: 0pt))[
  #set text(size: 9.8pt)
  #set par(justify: true)
  *Abstract.* God's number, the largest number of face turns needed to solve a
  Rubik's cube, is twenty. We describe a proof in the Rocq prover of the lower
  half of that statement: one position, the superflip, cannot be solved in
  nineteen moves. The search is pruned by a table of two billion entries that
  is never proved correct, only checked.

  #v(0.4em)
  *Keywords.* Rubik's cube, God's number, formal proof, Rocq, pruning table.
]]

#v(0.6em)

= The problem

A Rubik's cube is built from twenty-six small cubes: *eight corner pieces*
with three stickers each, *twelve edge pieces* with two, and *six centre
pieces* with one. The centres are attached to the core. They spin in place but
never travel, so they are the frame that everything else is measured against:
the white face is wherever the white centre is. A face turn moves four corners
and four edges, and nothing else.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    cube3dt(0)
    let key(y, fill, label, body) = {
      rect((3.1, y), (3.55, y - 0.45), fill: fill, stroke: 0.5pt)
      content((3.325, y - 0.225), text(size: 7.5pt)[#label])
      content((3.75, y - 0.225), text(size: 9pt)[#body], anchor: "west")
    }
    key(3.3, cCor, "c", [8 corner pieces, 3 stickers each])
    key(2.6, cEdg, "e", [12 edge pieces, 2 stickers each])
    key(1.9, cCen, "U", [6 centre pieces, 1 sticker, fixed])
  }),
  caption: [The three kinds of piece. Every face shows four corner stickers,
    four edge stickers and one centre.],
) <pieces>

Not every arrangement of the pieces can be reached by turning faces. Those
that can number

$ 8! dot 3^7 dot 12! dot 2^11 slash 2 = 43 space 252 space 003 space 274
  space 489 space 856 space 000 approx 4.3 dot 10^19, $

which reads: the eight corners in any order ($8!$), each twisted one of three
ways except that the last is forced by the other seven ($3^7$); the twelve
edges in any order ($12!$), each flipped or not with the last again forced
($2^11$); and a final halving, because corners and edges cannot be rearranged
independently of each other.

Three details of the pieces will matter later, and they are worth naming now.
Every corner carries exactly one sticker of the top or bottom colour, and that
sticker sits either on the top of the corner or on one of its two sides: which
of the three is the corner's *twist*. Every edge has a right way round, and can
sit in its slot *turned over*, showing its two colours the other way about. And the four edges
lying in the *middle layer*, the slice between the top and bottom faces,
occupy four of the twelve edge slots; which four is the third thing to keep
track of.

Turning one face is a _move_, and a half turn counts as one move just like a
quarter turn. Every scramble can be undone; the question is how many moves the
worst scramble needs. That number is called *God's number*.

In 2010 Rokicki, Kociemba, Davidson and Dethridge showed that it is *20*
@rokicki2013diameter. The answer comes in two halves, and they are not equally
hard.

- *Twenty moves are always enough.* This is the huge half: every one of the
  43 quintillion states has to be accounted for. It took about a billion
  seconds of processor time, donated by Google, after the states had been
  grouped into 55 882 296 families.
- *Twenty moves are sometimes needed.* For this it is enough to point at one
  scramble and show it cannot be solved in 19.

This note is about the second half, and about one scramble: the *superflip*,
drawn in @sflip beside a solved cube. Every corner sticker is where it belongs,
and every edge is in its own place but turned over, so it shows the colour of
the face beside it. Turn the whole cube in your hands, or look at it in a
mirror, and the same pattern comes back: the superflip is one of the rare
positions that all 48 ways of looking at a cube leave unchanged, and that will
matter later. A 20-move solution for it is known. What has to be
proved is that no solution of 19 moves exists.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    cube3dc(0,
      (cW, cW, cW, cW, cW, cW, cW, cW, cW),
      (cG, cG, cG, cG, cG, cG, cG, cG, cG),
      (cR, cR, cR, cR, cR, cR, cR, cR, cR))
    content((0, -0.45), text(size: 9pt)[solved])
    cube3dc(4.4,
      (cW, cB, cW, cO, cW, cR, cW, cG, cW),
      (cG, cW, cG, cO, cG, cR, cG, cY, cG),
      (cR, cW, cR, cG, cR, cB, cR, cY, cR))
    content((4.4, -0.45), text(size: 9pt)[the superflip])
  }),
  caption: [A solved cube, and the superflip.],
) <sflip>

That is still a big computation. There are 18 possible moves at each step, so
19 moves means something like $18^19$ words, far more than could ever be
listed. Nobody searches like that: the search is cut short using a precomputed
table, and that is where both the interest and the difficulty lie.

Why do it in a proof assistant at all, here the Rocq prover @rocq (the system
formerly called Coq)? Because then the result no longer depends on a
search program being right. What is checked instead is a proof,
verified by a small kernel, starting from the definition of the cube itself.

= The cube as permutations

The cube is easier to reason about if we stop thinking about it as a solid
object. Only the coloured stickers matter. There are six faces of nine
stickers, and the six centre stickers never move relative to each other, so a
move is just a rearrangement of the *48 remaining stickers*. Number them 0 to
47, as in @cube3d and @net: eight to a face, taken left to right and top to
bottom with the centre skipped, so up gets 0--7, left 8--15, front 16--23,
right 24--31, back 32--39 and down 40--47. These are the numbers the sources
use, which is what makes the definition of a move checkable against a
picture.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    cube3dn(0)
    // the turn of the top face, clockwise seen from above
    bezier((-1.15, 3.75), (1.15, 3.75), (0, 4.55), mark: (end: ">"), stroke: 0.7pt)
    content((0, 4.75), text(size: 9pt)[the move $U$])
  }),
  caption: [Three of the six faces, and the turn of the top one.],
) <cube3d>

#figure(
  cetz.canvas(length: 1cm, {
    flatface(3 * s, 0, (0, 1, 2, 3, 4, 5, 6, 7), "U", tint: pW)
    flatface(0, -3 * s, (8, 9, 10, 11, 12, 13, 14, 15), "L", tint: pO)
    flatface(3 * s, -3 * s, (16, 17, 18, 19, 20, 21, 22, 23), "F", tint: pG)
    flatface(6 * s, -3 * s, (24, 25, 26, 27, 28, 29, 30, 31), "R", tint: pR)
    flatface(9 * s, -3 * s, (32, 33, 34, 35, 36, 37, 38, 39), "B", tint: pB)
    flatface(3 * s, -6 * s, (40, 41, 42, 43, 44, 45, 46, 47), "D", tint: pY)
  }),
  caption: [The cube unfolded, with all forty-eight places numbered.],
) <net>

With the places numbered, a move is written down by saying, for each place,
where the sticker sitting there goes. Turning the top face clockwise carries
the sticker in corner 0 to corner 2, the one in 2 to 7, the one in 7 to 5 and
the one in 5 back to 0. That is a four step cycle, written
$(0 space 2 space 7 space 5)$. The four edge stickers of that face do the same,
$(1 space 4 space 6 space 3)$. But the turn does not only move the top face:
it also carries the top row of each side face round to the next one, front to
left, left to back, back to right, right to front. That is three more cycles,
$(8 space 32 space 24 space 16)$ and its two companions. @uturn shows the whole
of it, each square saying which sticker sits there afterwards: the top row of
the left face holds 16, 17, 18, the stickers that came round from the front.
The other forty stickers are untouched, and the six centres never move at
all.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    topband(0, (0, 1, 2, 3, 4, 5, 6, 7),
            (8, 9, 10), (16, 17, 18), (24, 25, 26), (32, 33, 34))
    content((-0.75, -1.24), text(size: 9pt)[before])
    line((6 * s, -4.35 * s), (6 * s, -5.05 * s), mark: (end: ">"), stroke: 0.7pt)
    topband(-5.4 * s, (5, 3, 0, 6, 1, 7, 4, 2),
            (16, 17, 18), (24, 25, 26), (32, 33, 34), (8, 9, 10))
    content((-0.75, -1.24 - 5.4 * s), text(size: 9pt)[after])
  }),
  caption: [Everything a clockwise turn of the top face moves.],
) <uturn>

Six clockwise quarter turns generate everything: up, right, front, down, left
and back. Each of them can also be done twice or backwards, which gives the
*eighteen moves*

#align(center)[
  $U, space U^2, space U^(-1), quad R, space R^2, space R^(-1), quad
    F, space F^2, space F^(-1), quad D, space D^2, space D^(-1), quad
    L, space L^2, space L^(-1), quad B, space B^2, space B^(-1)$
]

A scramble is a product of moves, for instance $R U R^(-1) U^(-1)$, a word of
length 4.
The set of all scrambles is a group $G$: the *cube group*. Solving a scramble
in $d$ moves means writing it as a word of $d$ moves, so "solvable in at most
$d$ moves" says exactly that the scramble lies in the *ball of radius $d$*
around the solved cube. God's number is the largest distance that occurs, the
diameter of that ball structure.

== What this looks like in Rocq

The development is built on *mathcomp* @mathcomp, a large library of formalised
mathematics that already knows about permutations, groups and products. The
cube file is then just a transcription of the paragraphs above, and it is
short:

```coq
Definition facelet := 'I_48.

Definition Umove : {perm facelet} :=
  cyc [:: 0@; 2@; 7@; 5@] * cyc [:: 1@; 4@; 6@; 3@] *
  cyc [:: 8@; 32@; 24@; 16@] * cyc [:: 9@; 33@; 25@; 17@] *
  cyc [:: 10@; 34@; 26@; 18@].
  (* ... and five more, one per face ... *)

Definition faces : seq {perm facelet} :=
  [:: Umove; Rmove; Fmove; Dmove; Lmove; Bmove].
Definition moves : seq {perm facelet} :=
  flatten [seq [:: g; g ^+ 2; g ^-1] | g <- faces].
Definition G : {group {perm facelet}} := <<Sset>>.
```

Word by word:

- `'I_48` is the type of the whole numbers *below* 48, so the places are
  numbered *0 to 47* and not 1 to 48, everywhere in the sources and in the
  pictures of this note.
- `{perm facelet}` is the type of *permutations* of those places: a way of
  sending each place to a place, no two of them landing on the same one. That
  is exactly what a scramble is.
- `cyc [:: 0@; 2@; 7@; 5@]` is the *cycle* that sends 0 to 2, 2 to 7, 7 to 5
  and 5 back to 0, leaving the other forty-four places where they are. The
  `@` is local notation turning a plain number into a place.
- `*` composes two permutations, so `Umove` is the five cycles of @uturn done
  together, and `g ^+ 2` and `g ^-1` are the same turn done twice and undone.
- `seq` is a list, and `faces` is the list of the six clockwise quarter turns.
  `moves` runs through it and keeps three moves per face, which is the
  eighteen.
- `<<Sset>>` is the group generated by a set: everything reachable by
  composing moves, which is the cube group.

The superflip is written down the same way, as the twelve swaps that exchange
the two stickers of each edge. That makes it a permutation of the stickers, but
by itself it says nothing about the cube: a permutation is a legal position
only if the faces can actually be turned to reach it, that is, only if it lies
in $G$. Nothing in the definition gives that, and it has to be proved. The
proof is to exhibit a maneuver, since the superflip is the result of

#align(center)[
  $U space R^2 space F space B space R space B^2 space R space U^2 space L
    space B^2 space R space U^(-1) space D^(-1) space R^2 space F space
    R^(-1) space L space B^2 space U^2 space F^2$
]

and both sides of that equality are pushed onto tables of 48 entries, where it
becomes one comparison of two lists. Since each of the twenty letters is one of
the generators, membership in $G$ follows, and the same maneuver is what gives
the upper bound of 20 for this particular cube.

Nothing here is assumed. There is no axiom stating what a cube is, and a reader
who wants to check the model only has to compare the six lists of cycles
against @net. After this file, stickers are never mentioned again.

= How the search works

Two classical ideas make the search possible.

== An estimate that is never too big

The idea is not new, and neither is the way the estimate is obtained. A
depth-first search that deepens step by step and prunes on an estimate that
never over-estimates is Korf's IDA\* @korf1985ida; taking the estimate from a
table of exact distances in a simplified version of the puzzle is a _pattern
database_ @culberson1998pattern, and Korf solved the cube optimally with three
of them @korf1997rubik. The summary used here is Kociemba's, from his two-phase
solver @kociemba.

Suppose we have a way of estimating, for any scramble, how many moves it needs
: an estimate that is never larger than the truth, and that changes by at
most one when a move is made. Call it $h$.

Such an estimate is a pair of scissors. Walk down the tree of moves, keeping
track of how many are left. If the estimate for a position is 20 while only 18
moves remain, that whole branch can be dropped: it cannot possibly reach the
solved cube in time. @tree shows the picture: below every position the table is
consulted, and a branch whose estimate exceeds the moves still available is
abandoned without ever being explored. The estimate is allowed to be too small,
which only means less cutting; it is never allowed to be too large.

#figure(
  cetz.canvas(length: 1cm, {
    tlbl(0, 0.35, [the superflip, 19 moves left])
    tnode(0, 0)
    for x in (-5.4, -1.8, 1.8) {
      tedge(0, -0.1, x, -0.95)
      tnode(x, -1.05)
    }
    tedge(0, -0.1, 4.6, -0.95)
    tlbl(-7.3, -1.05, [after one move:])
    tlbl(-5.4, -1.45, [the table says 17])
    tlbl(-1.8, -1.45, [the table says 20])
    tlbl(1.8, -1.45, [the table says 11])
    tlbl(5.1, -1.05, [$dots.h$])
    tlbl(5.4, -1.45, [and fifteen more])
    tlbl(-1.8, -1.85, text(fill: rgb("#b00"))[#sym.times ~ cut: 20 > 18])
    for x in (-5.4, 1.8) {
      tedge(x, -1.6, x - 0.9, -2.4)
      tedge(x, -1.6, x + 0.9, -2.4)
      tlbl(x, -2.65, [18 moves left])
    }
  }),
  caption: [The search, and its scissors.],
) <tree>

== Where the estimate comes from

The trick is to forget most of the cube. Keep only part of the information,
say how the corners are twisted and where the four middle-layer edges sit, and
call what is left a *summary*. Many different scrambles share a summary.
Moves act on summaries just as well as on cubes, and there are few enough
summaries that a computer can work out, once and for all, the exact distance
from the solved summary to every other summary. That table of distances is the
estimate: a scramble needs at least as many moves as its summary does.

And here is where the numbering of the stickers earns its keep: a summary is
read straight off them. @encoding shows the three questions it asks. A corner
has one sticker belonging to the up or down face, and that sticker sits in one
of three places, which is 0, 1 or 2. An edge is either the right way round or
turned over, which is 0 or 1. And the four edges of the middle layer occupy
four of the twelve edge slots; the figure shades them on the two visible faces,
where three of the four can be seen. Nothing else about the position is
recorded.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    content((-4.4, 4.5), text(size: 9pt)[*a corner*: where is its up sticker?])
    cubie((-6.2, 2.5), "top")
    cubie((-4.4, 2.5), "front")
    cubie((-2.6, 2.5), "right")
    content((-6.2, 2.15), text(size: 9pt)[0])
    content((-4.4, 2.15), text(size: 9pt)[1])
    content((-2.6, 2.15), text(size: 9pt)[2])
    content((-4.4, 1.5), text(size: 9pt)[*an edge*: is it turned over?])
    cubie((-5.3, -0.4), "top")
    cubie((-3.5, -0.4), "front")
    content((-5.3, -0.75), text(size: 9pt)[0])
    content((-3.5, -0.75), text(size: 9pt)[1])
    content((3.4, 4.5), text(size: 9pt)[*the middle layer*: which four slots?])
    cube3dn(3.4, hi: (19, 20, 27, 28))
  }),
  caption: [The three questions a summary asks.],
) <encoding>

The summary is the product of the three answers:

#tbl(([summary], [values], []),
  ([how the eight corners are twisted], [2 187], [$= 3^7$]),
  ([how the twelve edges are flipped], [2 048], [$= 2^11$]),
  ([where the four middle-layer edges sit], [495], [4 places among 12]),
  ([*the phase 1 summary, all three together*], [*2 217 093 120*], []),
)

Two billion is small next to 43 quintillion: *every summary stands for exactly
19 508 428 800 real scrambles* (that is the division, and it comes out even).
The table records, for each summary, its distance from the solved summary. No
entry in it is larger than 12, that being how deep the deepest summary lies
rather than the value of any position in particular. So four bits hold one
entry, and the whole table is *1.18 GB*.

== And why a failed search is a proof

The search answers "maybe solvable in $d$ moves" or "no". The *no* is the
trustworthy side: it means every branch was cut, either because the depth ran
out or because the table said so. So a negative answer to "is the superflip
solvable in 19 moves?" is exactly the theorem wanted.

Better still, the answer does not depend on the table being right. If an entry
of the table were too small, the search would merely cut less and take longer.
Only the two local properties matter: the solved summary has distance 0, and
one move changes the value by at most one. That is what makes the whole thing
formalisable at a sane cost: a table with two billion entries never has to be
proved correct, only checked.

= The search in Rocq

The general principle is one file of about a hundred lines, #src("Search.v"),
which does not mention the cube at all. It takes a group, a set of moves, an
estimate $h$, and the two assumptions:

```coq
Hypothesis h1    : h 1 = 0.
Hypothesis hstep : forall g m, m \in S -> h g <= (h (g * m)).+1.

Fixpoint search (d : nat) (g : gT) : bool :=
  (h g <= d) &&
  ((g == 1) ||
   (if d is d'.+1 then has (fun m => search d' (g * m)) Sseq else false)).

Corollary searchN d g : search d g = false -> g \notin ball S d.
```

Again word by word:

- `gT` is the group the file works in. It is a variable, so nothing here is
  about the cube; the cube is what it gets instantiated with later.
- `1` is the unit of that group, which for the cube is the *solved* position.
  So `h 1 = 0` says the estimate of a solved cube is zero, and `g == 1` asks
  whether the search has arrived.
- `Sseq` is the list of moves, the eighteen of them, in the order the search
  walks over them. `S` is the same thing seen as a set.
- `g * m` is the position `g` followed by the move `m`. The order takes some
  getting used to: mathcomp applies permutations on the right, so `(g * m) f`
  is `m (g f)`, and the product reads left to right like a sequence of moves
  rather than right to left like a composition of functions.
- `h g <= d` is the cut, and `(h (g * m)).+1` is the estimate after a move
  plus one, which is the assumption that one move changes the estimate by at
  most one.
- `has (fun m => search d' (g * m)) Sseq` tries every move with one fewer
  move available, and answers as soon as one of them succeeds.

The last line is the contract of the whole development: *if the search returns
false, the position is not within $d$ moves.*

That is a theorem, proved once, about any estimate satisfying the two
assumptions. Everything else in the development exists either to discharge
those two assumptions for the real table, or to make the search fast enough to
run.

*What the table has to satisfy, and what it does not.* #src("Coord.v") shows that a summary
`coord`, the action `act` of a move on summaries, and any table `D` at all give
a legal estimate as soon as `D` passes these two checks:

```coq
Hypothesis D0    : D (coord 1) = 0.
Hypothesis Dstep : forall x m, m \in Sset -> D x <= (D (act x m)).+1.
```

The first says the solved summary has value zero. The second says that applying
a move to a summary lowers its value by at most one. Nothing else is required.
In particular the table is never proved to hold the true distances; what is
proved of it is only that it is a valid under-estimate, which is a strictly
weaker property.

That weaker property is not cheaper to check. Exactness is local too: a table
holds the true distances exactly when it satisfies the two conditions above and
also, at every summary but the solved one, some move lowers its value by
exactly one. That is the same single sweep over the table. What the weaker
property buys is not speed but freedom, and it is what section 5 spends: the
folded table of the last optimisation is *not* the true distance function and
would fail an exactness check, yet it passes these two and is therefore just as
good a certificate. So it can
be produced by any program in any language, and here an OCaml generator writes
it out as Rocq source, to be checked afterwards by evaluating the two
conditions on every entry. Those checks are large computations in their own
right: the second one runs over each of the 2.2 billion summaries and each of
the eighteen moves. They are what the _certificate_ files do, each ending in
its own `Qed`.

*Two reductions cut the top of the tree.* First, the superflip looks the same
from every angle. There are 48 ways of putting a cube back into the space it
came from: any of the six faces can be turned to the top, each of them in four
positions, which makes twenty-four, and each of those seen in a mirror as
well.
Relabelling the superflip's stickers by any of the 48 gives the superflip back
again. Being unchanged by all 48, it lets the search take the first move to be
$U$ or $U^2$ instead of any of the eighteen. Second, no shortest solution ever turns the same face twice in a row, nor turns
two opposite faces in both orders.

Fixing the first two moves then splits the depth-19 search into $2 times 18 =
36$ searches of depth 17. The second move ranges over all eighteen, including
the three that turn the U face again: those are redundant, but they are left in
at this level and the redundancy rules do their work inside the search, which
keeps the statement of the split as simple as "any first move from `Sroot`,
any second move from `moves`". The 36 are packed into *eighteen files*, one per
second move, each carrying both first moves, and that is how the work is spread
over the cores of a machine: eighteen files, eighteen `Qed`s, nothing shared.

= What had to be optimised

The first version worked and was far too slow. Closing the gap between "runs"
and "finishes" took a series of changes, each one measured before and after.

*Counting in unary is the enemy.* The numbers used by the mathcomp library are
Peano numbers: 5 is literally the successor of the successor of the successor
of the successor of the successor of zero, so adding $n$ costs $n$ steps and
comparing costs as much again. Rocq also offers machine integers, 63 bits wide
with the missing bit going to the garbage collector, and *persistent arrays* of
them @armand2010imperative, both of which cost what the hardware costs. That is also how the table is stored: fifteen of its
four-bit entries to a machine integer. Measured here: a machine-integer operation takes
about 0.05 microseconds and a Peano-number operation about 1 microsecond, and
converting between the two costs about 0.07 microseconds _per unit_, so that
converting the number 495 costs 36 microseconds all by itself. Rewriting the
inner loop so that indices, table values and the depth comparison never leave
machine integers gave:

#tbl(([operation], [before], [after]),
  ([reading the summary of a position], [32.0 µs], [*0.10 µs*]),
  ([applying a move to a summary], [4.60 µs], [*0.12 µs*]),
  ([reading one entry of the packed table], [2.99 µs], [*0.13 µs*]),
)

*`and` and `or` are function calls.* Rocq evaluates both sides of a boolean
test before combining them, so a guard written "either the value is out of
range, or the expensive check holds" runs the expensive check on _every_ value.
Rewritten as a nested `if`, it runs only on the values that get past the guard.
Two otherwise identical certificates, one of each shape: *719.7 s against about
80 s*. The same mistake in the search cost a further factor of 27.8 on one
guard. Every guard in the development is a nested `if` now.

*The search itself, twelve times faster.* Before the list of changes, here is
what the search of #src("Farp1.v") actually carries at each position, since
none of them make sense otherwise. Four things:

- `a`, the position itself as a 48-entry array saying where each sticker went.
  It is used for one purpose only, to ask "is this the solved cube?", and a
  fresh one is built for each child by composing `a` with the move's own array.
- `x`, the three views: for each of the three, the pair of numbers that is its
  summary, the corner twist and the flip-and-slice index. A move takes each
  pair to another pair by two lookups in a move table.
- `p`, which face was turned last, from which the list of moves worth trying
  next is read off.
- `d`, how many moves are left.

The estimate is the largest of *nine* lookups: three tables, at each of the
three views. Now the chain of seven versions in #src("Fast.v"), each proved
equal to the one before, so that no trust is transferred. Measured on one piece
at depth 14:

#tbl(([version], [seconds], [what it removes]),
  ([the original], [70.0], []),
  ([2], [39.1], [Peano arithmetic inside the loop: move indices, the depth
                 test and the list of allowed moves all become machine
                 integers, computed once]),
  ([3], [16.5], [building the child's 48-entry array before looking at the
                 estimate, when the estimate then rejects the child]),
  ([4], [13.4], [comparing all 48 entries against the solved position when the
                 first difference already settles it]),
  ([5], [9.7],  [the last of the nine lookups once one of them already exceeds
                 the moves left]),
  ([6], [8.0],  [computing the summaries of all three views when the first view
                 already cuts]),
  ([7], [*5.9*], [keeping `a` up to date at every position: the list of moves
                  is carried instead, and the position rebuilt from it only for
                  the solved test]),
  ([], [*11.9x*], []),
)

Four of those six steps are the same mistake in different clothes: work being
done that a lazier evaluator would have skipped.

*Three views of the same position.* Rotating the whole cube about a corner
axis gives the same position seen differently, and its summary is then a
different entry of the same table. Each of the three views therefore yields a
lower bound on the number of moves left, so the largest of them is a lower
bound too, and never a smaller one than any single view gives. Three times the
lookups at each position, in exchange for a sharper cut and so a smaller tree.
This is standard practice in cube solvers, Kociemba's included; what is new
here is only that the three views are proved to be legitimate.

*How the table is written down costs more than the table.* The phase 1 table
is emitted as Rocq source, one file per block of 2 097 152 entries, 71 of them.
Written as a list, a block is a term: two million nested applications of the
list constructor, each holding a machine integer. That term is what the `.vo`
stores and what `Require` loads, and it is far larger than the 17 MB of data in
it. Written instead as an array literal, that is, as a definition whose body
has already been evaluated to a primitive array, the `.vo` holds one compact
block of memory. Measured on the same 2 097 152 entries:

#tbl(([the block, written as], [its `.vo`], [loaded]),
  ([a list], [37.8 MB], [877 MB]),
  ([an array literal], [*6.0 MB*], [*281 MB*]),
)

Over all 71 blocks that is 21.5 GB against *5 GB*, and it is what allowed nine
parallel workers instead of two on a 62 GB machine.

*Folding the table by symmetry.* The summary is built around the up-down axis:
the twist counts where each corner's up-or-down sticker sits, and the slice
says where the four edges between the top and bottom faces are. So a symmetry
that leaves that axis in place turns a summary into another summary, while one
that tips the cube onto another axis does not act on these summaries at all.
Sixteen of the 48 keep the axis, and they sort the 1 013 760 flip-and-slice
values into *64 430 families*, a factor of *15.73*. Two values in the same
family are the same distance from solved, so one entry per family is enough: a
lookup first replaces the value by its family's representative, carrying the
twist through the same symmetry, and then reads a table 15.73 times smaller.

That is a different use of symmetry from the three views above, and the two are
worth telling apart. The three views ask the *same* table three questions and
keep the largest answer, which sharpens the estimate and cuts the tree. The
fold asks the *same* question of a *smaller* table, and the estimate does not
change at all. Symmetry-reduced tables of this kind are standard in cube
solvers; what the development adds is a proof that the folded table still
satisfies the two conditions, which is all it has to satisfy, since it is never
claimed to hold true distances.

The fold costs the search, measured at 1.61 times slower at depth 16, and pays
everywhere else: a search worker drops from 4.15 GB to *0.85 GB*, so all
eighteen pieces now run at once instead of in two waves, and checking the table
drops from about 5.4 processor hours to *1.35*.

*What remains.* Against the OCaml program running the same search, Rocq needs
about 165 microseconds per position against 0.79, a factor of *209*. That
factor, not the algorithm, is why the run takes hours rather than minutes.

= The files

Forty-six hand-written Rocq files. What each group does.

#tbl(([the cube, as mathematics], []),
  ([`Cyc.v`], [cyclic permutations, built from the list of points they move]),
  ([`Rubik333.v`], [facelets, the six faces, the eighteen moves, the cube group]),
  ([`Sym.v`, `Sym16.v`], [the 48 symmetries of the cube; the 16 used by the fold]),
  ([`Ball.v`], [balls of radius $d$, and what "the diameter is at most $d$" means]),
  ([`Diameter.v`], [the superflip, its 20-move sequence, and the final statement]),
)

#tbl(([the search, in the abstract], []),
  ([`Search.v`], [the search and its contract: a false answer is a proof]),
  ([`Coord.v`], [any summary plus any checked table gives a legal estimate]),
  ([`Root.v`], [the first move, up to symmetry: $U$ or $U^2$]),
  ([`Searchr.v`, `Redun.v`], [the rules that forbid redundant move sequences]),
)

#tbl(([data structures], []),
  ([`Table.v`], [permutations written as the table of their images]),
  ([`Tabi.v`], [the same on machine integers and arrays, and the bridge between]),
  ([`ssrint63.v`], [the machine-integer toolbox used throughout]),
)

#tbl(([the summaries and their tables], []),
  ([`Coordfs.v`, `Coordfsi.v`], [the edge-flip and slice summary, packed into 24 bits]),
  ([`Fstab.v`, `FsTable.v`, `Fsparity.v`], [its table and the checks it must pass]),
  ([`Phase1.v`], [the phase 1 estimate, its table and its certificate, 2215 lines]),
  ([`Moves.v`], [the eighteen moves and the superflip, as tables]),
)

#tbl(([the search on the real data], []),
  ([`Farp1.v`], [the three viewing angles and the search built on them, 1404 lines]),
  ([`Far.v`], [the assembly: the superflip is not within $d$ moves, 1124 lines]),
  ([`Fast.v`, `FastP.v`], [the fast search, and the proof that it is the same search]),
  ([`Runp1_00.v` .. `_17.v`], [the eighteen pieces, written by a script]),
  ([`Farp1main.v`], [the theorem over _any_ table: 8 seconds, and no data at all]),
  ([`Farp1inst.v`], [the same at the real table and the eighteen real runs]),
)

The *certificates* are the files that run the checks, each with its own `Qed`:
three for the move and distance tables, one for the second summary table, two
for the main table split sixteen ways, and nine more for the folded table.
Three of the last group hold the actual numbers and are deliberately kept out
of the project file, since they do not exist until the generator has run.

*Outside Rocq*, `ocaml/rubik_par.ml` and `ocaml/rubik_lb.ml` are the reference
implementation. The Rocq search reproduces their node counts exactly, which is
how a discrepancy gets caught early, and `bench/p1gen.ml` generates the tables.
The `bench/` directory also keeps the experiments that settled design
questions, each with its measurements.

= The development in figures

#tbl(([], []),
  ([hand-written Rocq], [*46 files, 14 033 lines*]),
  ([generated table sources, in the repository], [about 156 000 lines]),
  ([generated table sources, too big to store], [about 165 MB of literals]),
  ([OCaml reference programs and generators], [2 749 lines]),
  ([build and run scripts], [1 031 lines]),
)

Positions visited, measured, and matching the OCaml program exactly:

#tbl(([search depth], [one piece], [all 18 pieces]),
  ([14], [42 320], [784 572]),
  ([15], [547 580], [10 185 576]),
  ([16], [7 100 612], [130 430 424]),
  ([17], [91 377 680], [about 1 700 000 000]),
)

The last figure is the only one not counted but computed, as the measured
depth 16 total multiplied by the measured growth of 12.87 from one depth to
the next.

Some build costs on the reference machine, a dual-socket Xeon with 62 GB and
twelve physical cores, all measured:

#tbl(([], []),
  ([the phase 1 estimate and its theory], [41 s]),
  ([the search file over the real tables], [1 min 30]),
  ([checking the folded table, in 27 slices], [9 min, about 1.35 processor hours]),
  ([the structural checks of the fold], [about 101 s]),
  ([compiling one table block to native code], [about 6 min, 9--10 GB]),
)

= The theorem, its cost, and what is left

The statement proved at the top of the chain is

```coq
Theorem superflip_p1far_real : superflip \notin ball Sset p1depth.
```

In words, the superflip is not within `p1depth` moves of the solved cube, where
the depth is set by one script before the run. It has *no hypotheses left*: the six
computations it rests on, namely the two summary tables, the three move and
distance tables and the eighteen searches, each live in their own file
behind their own `Qed`. Asking Rocq what the proof assumes reports only the
primitives of its machine-integer and array interface. Nothing in the chain is
admitted.

At depth 19 this says precisely that the superflip cannot be solved in 19
moves, which is *God's number $>= 20$*.

The runs, measured, eighteen pieces on nine workers:

#tbl(([radius], [search depth], [wall clock], [processor time]),
  ([17], [15], [13 min 05], [35 min 29]),
  ([18], [16], [54 min 37], [6 h 57]),
  ([*19*], [*17*], [*11 h 13 min*], [*85 h 11*]),
)

*Memory.* A worker holds the loaded table and nothing else that grows: the
search walks down and back up, so only the current sequence of moves is kept.
Measured at *4.15 GB* per worker, identical to three decimals across the nine
and the same at every depth, and *0.85 GB* since the table was folded,
which is what lets all eighteen pieces run at once. The 19-move run above was
made before the fold.

*What is left.* Two things, stated plainly.

+ The 19-move run predates the fold becoming the official table check. Through
  the fold the chain has been run at 16 and at 18; running it at 19 is
  projected at about 13 hours of wall clock, by multiplying the measured 18
  figure by the measured growth of 12.87. That same method predicted the
  earlier run to within 4 %.
+ `Diameter.v` still contains the sentence "the superflip is not within 19
  moves" as an admitted placeholder, because that file sits at the bottom of
  the chain and cannot refer to the search that sits at the top. Both ends
  exist; a short file at the top has to join them.

And the other half of God's number, that 20 moves always suffice, is not
proved here. `Diameter.v` does contain the reduction for it, stated in terms of
exactly what an exhaustive search would have to supply: that the 55.9 million
families cover every case up to symmetry, and that each of them is solvable in
20 moves. That computation is several orders of magnitude larger than the one
this note describes.

= Acknowledgements

This development was written with *Claude*, Anthropic's coding assistant, as a
working partner. The Rocq sources, the OCaml programs they are checked against
and this note were produced in three weeks, between 23 July and 12 August 2026,
and 267 of the 268 commits touching `code/Rubik` record Claude as a co-author.
The division of labour was the natural one: I said what was to be proved, chose
what to formalise and what to throw away, and rejected what was wrong; Claude
wrote and rewrote the proofs and the generators, ran the experiments and
measured them.

What makes such a collaboration workable is that almost nothing has to be taken
on trust. Every claim about the cube ends in the Rocq kernel, which does not
care who wrote the proof, and the tables are checked rather than believed. What
does have to be watched is everything outside that: the numbers, the claims
about what was measured and what was only estimated, and the statement of the
final theorem itself, since a theorem can be true and say less than one thinks.

#pagebreak(weak: true)

#bibliography("rubik20-note.bib", title: [References], style: "springer-mathphys")
