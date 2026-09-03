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
#let ftbl(headers, ..rows) = table(
  columns: (10.5em, 1fr),
  stroke: none,
  inset: (x: 7pt, y: 3.5pt),
  align: left,
  table.hline(),
  table.header(..headers.map(h => text(weight: "bold", h))),
  table.hline(stroke: 0.5pt),
  ..rows.pos().flatten(),
  table.hline(),
)

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
  nineteen moves. The search is pruned by a table of two billion entries, every
  one of them checked inside the prover. Counting a half turn as the two
  quarter turns it is made of gives a second number, twenty-six, and the lower
  half of that is proved here too: Michael Reid's position of 1998 cannot be
  solved in twenty-five quarter turns.

  #v(0.4em)
  *Keywords.* Rubik's cube, God's number, quarter turn, formal proof, Rocq,
  pruning table.
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

Not every arrangement of the pieces can be reached by turning faces. The number
of arrangements that can be reached is

$ 8! dot 3^7 dot 12! dot 2^11 slash 2 = 43 space 252 space 003 space 274
  space 489 space 856 space 000 approx 4.3 dot 10^19, $

which reads: the eight corners in any order ($8!$), each twisted one of three
ways except that the last is forced by the other seven ($3^7$); the twelve
edges in any order ($12!$), each flipped or not with the last again forced
($2^11$); and a final halving, because corners and edges cannot be rearranged
independently of each other.

Three details of the pieces matter later. They are named here.

Each corner has exactly one sticker of the top colour or the bottom colour.
That sticker can be in three places on the corner: on top, or on one of the
corner's two sides. Which of the three is the corner's *twist*.

Each edge has a right way round. Put back the other way round, it shows its two
colours the wrong way about. That is the edge's *flip*.

Four of the twelve edges belong in the middle layer, the *slice* between the
top and the bottom face. A move can send them to any of the twelve edge slots.
Which four slots they are in is the third thing to follow.

Turning one face is a _move_, and a half turn counts as one move just like a
quarter turn. Every scramble can be undone; the question is how many moves the
worst scramble needs. That number is called *God's number*.

Counting a half turn as one move is a choice. It can also be counted as the
two quarter turns it is made of, which gives a second number for the same
cube. This note proves a lower bound for each of the two.

In 2010 Rokicki, Kociemba, Davidson and Dethridge showed that it is *20*
@rokicki2013diameter. Their result has two halves. That twenty moves are always
enough is the huge half, and how it was obtained is left to the last section of
this note. That twenty moves are sometimes needed is the other half, and for
that it is enough to exhibit one scramble and show it cannot be solved in 19.

This note is about the second half, and about one scramble: the *superflip*,
drawn in @sflip beside a solved cube. Every corner sticker is where it belongs,
and every edge is in its own place but turned over, so it shows the colour of
the face beside it. Turn the whole cube in your hands, or look at it in a
mirror, and the same pattern comes back: the superflip is one of the rare
positions that all 48 ways of looking at a cube leave unchanged, and that will
matter later. A 20-move solution for it is known, so
showing that no 19-move solution exists puts the superflip at distance exactly
20. That is what is proved here.

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
  #grid(
    columns: (auto,) * 6,
    column-gutter: 1.6em,
    row-gutter: 0.5em,
    align: center,
    $U$, $R$, $F$, $D$, $L$, $B$,
    $U^2$, $R^2$, $F^2$, $D^2$, $L^2$, $B^2$,
    $U^(-1)$, $R^(-1)$, $F^(-1)$, $D^(-1)$, $L^(-1)$, $B^(-1)$,
  )
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
the two stickers of each edge:

```coq
Definition Spcyc : seq (seq facelet) :=
  [:: [:: 1@; 33@]; [:: 3@; 9@]; [:: 4@; 25@];
      (* ... nine more, one per edge ... *) ].

Definition superflip : {perm facelet} := \prod_(l <- Spcyc) cyc l.
```

That makes it a permutation of the stickers, but by itself it says nothing
about the cube. A permutation is a legal position only if the faces can
actually be turned to reach it, that is, only if it lies in $G$. Nothing in the
definition above gives that, and it has to be proved.

The proof is one equality. On the left, the superflip as just defined. On the
right, a word of twenty moves:

#align(center)[
  $U space R^2 space F space B space R space B^2 space R space U^2 space L
    space B^2 space R space U^(-1) space D^(-1) space R^2 space F space
    R^(-1) space L space B^2 space U^2 space F^2$
]

Both sides are permutations of the 48 stickers. Each is written out as the list
of the 48 places it sends each place to, and the equality becomes one
comparison of two lists. Every letter on the right is one of the eighteen
moves, so the superflip lies in $G$. That same word is also what gives the
upper bound of 20 for this one position.

Nothing here is assumed. There is no axiom stating what a cube is, and a reader
who wants to check the model only has to compare the six lists of cycles
against @net. After this file, stickers are never mentioned again.

= How the search works

Two classical ideas make the search possible.

== The pruning estimate

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

The name comes from Kociemba's solving algorithm, which works in two phases.
Its first phase has to bring exactly these three answers to zero, and the
summary is what it watches while doing so. The algorithm itself plays no part
here. Only the name is borrowed, because it is the one everybody uses for this
table.

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

*What the table has to satisfy, and what it does not.* #src("Coord.v") asks for
three things and checks two:

```coq
Variable coord : {perm facelet} -> X.
Variable act   : X -> {perm facelet} -> X.
Hypothesis coordM : forall g m, coord (g * m) = act (coord g) m.

Variable D : X -> nat.
Hypothesis D0    : D (coord 1) = 0.
Hypothesis Dstep : forall x m, m \in Sset -> D x <= (D (act x m)).+1.
```

`coord` is the summary of a position, `X` being whatever the summaries happen
to be. `act` is how a move acts on a summary directly, without going back to
the position it came from: for the phase 1 summary it is two lookups in a move
table. `coordM` is what makes the pair worth having, and it is the one thing proved
about the summary itself. It says that summarising after a move gives the same
answer as acting on the summary. So the search never computes a summary from a
position. It carries the summary beside the position and brings it up to date
one move at a time, at the cost of a lookup. It still carries the position: the
summary cannot say whether the cube is solved, only the position can.

Put beside the `search` of #src("Search.v"), the search that actually runs has
this shape. Names are simplified and the machine-integer details left out; the
real one is `searchz3` in #src("Farp1.v"):

```coq
Fixpoint search (d : nat) (g : gT) (x : summary) (p : move) : bool :=
  (D x <= d) &&
  ((g == 1) ||
   (if d is d'.+1
    then has (fun m => search d' (g * m) (act x m) m) (allowed p)
    else false)).
```

Two things travel down the tree instead of one, and each is used for exactly
one job:

- `D x <= d` is the cut. It reads the table at the summary `x`, and never looks
  at the position.
- `g == 1` asks whether the cube is solved. It reads the position `g`, and
  never looks at the summary.
- `g * m` moves the position and `act x m` moves the summary, side by side, one
  move at a time. That step is `coordM` being used, and it is why the summary
  never has to be recomputed from the position.
- `p` is the move just played, and `allowed p` is the list of moves the rules
  permit after it. That is where redundant sequences are dropped.

*The two conditions.* `D` is the estimate. It takes a summary and gives back a
number, and that number is read from the table. `D0` and `Dstep` are everything
asked of it. `D0` says the solved cube gets zero. `Dstep` says that one move
lowers the estimate by at most one.

That is a weak demand, and it is worth seeing how weak. The table is never
proved to hold the true distance to the solved cube. A table of zeros passes
both conditions. It would prune nothing, and the search would run for ever, but
it would not make the search give a wrong answer.

*How the two conditions are checked.* Look again at `Dstep`. Unlike `D0`, it
does not mention `coord` at all. It speaks of every value `x` in `X`, and not
only of those values that are the summary of a real position. That is
deliberate, and it is what makes the check possible. `X` is a finite set of 2.2
billion values, so the check runs over all of them, and it never has to know
which of them come from a cube. `D0`
is then one lookup, and `Dstep` is one sweep: 2.2 billion summaries, eighteen
moves each, one comparison apiece. Those sweeps are what the _certificate_
files do: #src("FsmChk.v"), #src("FsrChk.v"), #src("SlrChk.v"),
#src("P1TsChk.v") and #src("Farp1chk.v"), listed again at the end of this note,
each ending in its own `Qed`.

Nothing in this asks where the table came from. It can be written by any
program in any language. Here an OCaml generator writes it out as Rocq source,
and the two conditions are checked on it afterwards.

*Three cuts at the top of the tree.* They are three different arguments and it
is worth keeping them apart. The first two apply once each, to the first move
and to the second. The third applies at every move from the third on.

*The first move: eighteen become two.* The superflip looks the same from every
angle. There are 48 ways of putting a cube back into the space it came from:
any of the six faces can be turned to the top, each of them in four positions,
which makes twenty-four, and each of those seen in a mirror as well.
Relabelling the superflip's stickers by any of the 48 gives the superflip back
again. So the first move may be taken to be $U$ or $U^2$, and the other sixteen
need not be tried.

*The second move: eighteen become fifteen.* The three that turn the top face
again are dropped. Turning the top face twice running merges into a single
turn, so those give a word of nineteen moves or fewer, and the proof covers
shorter words at a smaller depth rather than by a search of their own.

The three that turn the *bottom* face look just as droppable, and are not. It
is worth saying why, because it is the case everyone gets wrong. The two turns
commute, so $U D$ can be rewritten $D U$; but the first move is already pinned
to the top face by symmetry, and turning the cube over to bring that $D$ back
to the top gives $U D$ once more. It is a fixed point of both rewritings, so
neither rewriting removes it. Reid's proof meets the same case and pays for it
elsewhere: he keeps the bottom-face second move, and uses the symmetries that
fix the pair of opposite faces to cut his *third* move instead.

Our own OCaml program had this wrong. It dropped the three bottom-face second
moves and so searched 24 prefixes where it had to search 30. Nothing about the
program looked wrong: it ran for hours, it exhausted its tree, and it reported
that no solution of length 19 exists, which is the answer we expected. The
error only came out when the same reduction had to be proved in Rocq, and the
proof of the bottom-face case could not be written. This is the whole argument
for proving a search rather than trusting it. A cut that is too greedy does not
make a search fail. It makes it faster, and it makes it agree with you.

*From the third move on: eighteen become fifteen or twelve.* This one is not
about the superflip and not about the top of the tree. It is one rule, applied
at every node. A shortest word never turns the same face twice running, since
the two turns merge into one; and of two opposite faces it never uses both
orders, since $U D$ and $D U$ give the same position, so fixing one order
loses nothing. At a node whose last move was on the top, right or front face,
both halves of the rule bite and *twelve* moves are left. At a node whose last
move was on the bottom, left or back face, only the first half bites, because
the opposite pair has already been cut in the other order, and *fifteen* are
left.

Applying that rule to the third move is not an extra assumption. The word after
the second move is reduced like any other, and the proof already knew it; the
search had simply been throwing the fact away and trying all eighteen.

None of the three is obvious, and they interact. The bottom-face second move
survives only because the rule used from the third move on would otherwise cut
the same pair of opposite faces twice, once by symmetry and once by the order
convention. Arguments of that shape are easy to get wrong and hard to test,
since getting one wrong makes the search faster and leaves the answer looking
the same. This is what Rocq is for here. Every cut has to be proved before the
search is allowed to use it, so a cut that does not hold is refused rather than
rewarded, and cuts that would otherwise be too delicate to trust can be taken.

So the depth-19 search becomes $2 times 15 = 30$ searches of depth 17. The 30
are packed into *seventeen files*, #src("Runp1_03.v") to #src("Runp1_17.v"),
one per second move and numbered by it, each holding both first moves.

Two of them run far longer than the rest, and they are the two whose second
move turns the bottom face, $D$ and $D^(-1)$, where the rule above leaves
fifteen branches and not twelve. Each is cut in two, one first move to a file:
#src("Runp1_09a.v") and #src("Runp1_09b.v") in place of a single `Runp1_09.v`,
and #src("Runp1_11a.v") and #src("Runp1_11b.v") in place of `Runp1_11.v`.
Fifteen second moves, two of them split, makes seventeen files. Without the
split, the run would finish long before those two files did, and would have to
wait for them.

That is how the work is spread over the cores of a machine: seventeen files,
seventeen `Qed`s, nothing shared.

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
satisfies the two conditions.

This is where the weakness of the two conditions pays. Nowhere does the proof
say that the folded table holds distances. It says the table passes `D0` and
`Dstep`, and the search needs nothing more. Had the conditions been written to
demand true distances instead, the fold would have had to be shown to preserve
them, which is a harder statement about the sixteen symmetries and about what
sharing an entry between two summaries does to it. None of that has to be
faced. The check is run on the folded table just as it was on the flat one, and
it is the same check.

Nor would demanding more have cost more. A table of true distances is
recognised by the same single sweep: it holds them exactly when it passes the
two conditions and, at every summary but the solved one, some move lowers the
value by exactly one. Asking for less does not buy a cheaper check. It buys the
freedom to hand the search a table like this one.

The fold costs the search, measured at 1.61 times slower at depth 16, and pays
everywhere else: a search worker drops from 4.15 GB to *0.85 GB*, so all
the pieces now run at once instead of in two waves, and checking the table
drops from about 5.4 processor hours to *1.35*.

*What remains.* The same search written in OCaml is about three times faster.
Both were run at radius 19 on the reference machine. The OCaml program visits
146 065 078 152 positions in 26.4 processor-hours, which is 0.65 microseconds a
position; Rocq takes 87.6 processor-hours over the same tree, which is 2.16. A
factor of *3.3*.

That the two walk the same tree is not assumed. Dividing each of the seventeen
Rocq pieces by the positions its OCaml counterpart visited gives between 1.98
and 2.52 microseconds, across pieces that differ in size by a factor of two. A
Rocq search cutting differently anywhere would show up as scatter there, and
there is none.

So the run takes a night because the tree has 146 billion nodes in it, not
because the prover is slow. In OCaml the same tree still costs 26
processor-hours.

= The files

The proof of the twenty is forty-six hand-written Rocq files. What each group
does. The sources carry
their own #src("README.md"), which lists the same files, the scripts beside
them, and how to run the whole thing.

#ftbl(([the cube, as mathematics], []),
  ([`Cyc.v`], [cyclic permutations, built from the list of points they move]),
  ([`Rubik333.v`], [facelets, the six faces, the eighteen moves, the cube group]),
  ([`Sym.v`, `Sym16.v`], [the 48 symmetries of the cube; the 16 used by the fold]),
  ([`Ball.v`], [balls of radius $d$, and what "the diameter is at most $d$" means]),
  ([`Diameter.v`], [the superflip, its 20-move sequence, and what the upper bound would need]),
)

#ftbl(([the search, in the abstract], []),
  ([`Search.v`], [the search and its contract: a false answer is a proof]),
  ([`Coord.v`], [any summary plus any checked table gives a legal estimate]),
  ([`Root.v`], [the first move, up to symmetry: $U$ or $U^2$]),
  ([`Searchr.v`, `Redun.v`], [the rules that forbid redundant move sequences]),
)

#ftbl(([data structures], []),
  ([`Table.v`], [permutations written as the table of their images]),
  ([`Tabi.v`], [the same on machine integers and arrays, and the bridge between]),
  ([`ssrint63.v`], [the machine-integer toolbox used throughout]),
)

#ftbl(([the summaries and their tables], []),
  ([`Coordfs.v`, `Coordfsi.v`], [the edge-flip and slice summary, packed into 24 bits]),
  ([`Fstab.v`, `FsTable.v`, `Fsparity.v`], [its table and the checks it must pass]),
  ([`Phase1.v`], [the phase 1 estimate, its table and its certificate, 2215 lines]),
  ([`Moves.v`], [the eighteen moves and the superflip, as tables]),
)

#ftbl(([the search on the real data], []),
  ([`Farp1.v`], [the three viewing angles and the search built on them, 1404 lines]),
  ([`Far.v`], [the assembly: the superflip is not within $d$ moves, 1124 lines]),
  ([`Fast.v`, `FastP.v`], [the fast search, and the proof that it is the same search]),
  ([`Runp1_03.v` .. `_17.v`], [the seventeen pieces, written by a script]),
  ([`Farp1main.v`], [the theorem over _any_ table: 8 seconds, and no data at all]),
  ([`Farp1inst.v`], [the same at the real table and the seventeen real runs]),
  ([`Diam20.v`], [and hence God's number is at least 20]),
)

The *certificates* are the files that run the checks, each with its own `Qed`.
Four of them cover the move and distance tables and the second summary table:
#src("FsmChk.v"), #src("FsrChk.v"), #src("SlrChk.v") and #src("P1TsChk.v").
#src("Farp1chk.v") checks the shape of the main table. Two more check the main
table itself, split sixteen ways, and the folded table is checked by the
`Fold` group, whose slices are #src("FoldOrbit_00.v") to `FoldOrbit_26.v`.
Three of the files that hold the actual numbers are deliberately kept out of
the project file, since they do not exist until the generator has run.

*Outside Rocq*, `ocaml/rubik_par.ml` and `ocaml/rubik_lb.ml` are the reference
implementation. The Rocq search reproduces their node counts exactly, which is
how a discrepancy gets caught early, and `bench/p1gen.ml` generates the tables.
The `bench/` directory also keeps the experiments that settled design
questions, each with its measurements.

= The development in figures

#tbl(([], []),
  ([hand-written Rocq, about the cube], [*45 files, 12 725 lines*]),
  ([`ssrint63.v`, a general int63 toolbox], [1 308 lines]),
  ([generated table sources, in the repository], [about 156 000 lines]),
  ([generated table sources, too big to store], [about 165 MB of literals]),
  ([OCaml reference programs and generators], [2 749 lines]),
  ([build and run scripts], [1 031 lines]),
)

Positions visited by the radius-19 search, counted by the OCaml program. The
Rocq search walks the same tree, and reproduces these counts exactly at the
smaller depths where counting it is cheap:

#tbl(([], [positions]),
  ([the smallest piece, `Runp1_11b`], [5 575 767 076]),
  ([the largest piece, `Runp1_10`], [10 554 835 820]),
  ([*all seventeen*], [*146 065 078 152*]),
)

The tree grows by 12.22 from one level to the next, measured between depths 17
and 19.

Building the tables costs the same whatever radius is searched afterwards.
Measured end to end from a clean tree on the reference machine, a dual-socket
Xeon with 62 GB and twelve physical cores:

#tbl(([], [wall clock], [processor time]),
  ([emitting the tables and compiling them to native code], [17 min 21], [52 min 13]),
  ([the coordinate and summary tables], [22 min 46], [21 min 15]),
  ([the search and the estimate, over no data at all], [11 min 02], [30 min 45]),
  ([the four certificates for the move and distance tables], [56 s], [2 min 27]),
  ([the fold: twelve checks and twenty-seven slices], [9 min 52], [47 min 57]),
  ([the shape check against the dummy table], [18 s], [16 s]),
  ([*in total*], [*1 h 02*], [*2 h 35*]),
)

Two things that table says. The second line is *serial* — 21 minutes of
processor time inside 23 minutes of wall clock — so it is the longest stage by
the clock and no number of cores shortens it. And the first and fifth lines
together are 100 of the 155 processor-minutes, both dominated by the OCaml
compiler turning a table into native code.

= The theorem and its cost

The statement proved at the top of the chain is

```coq
Theorem superflip_p1far_real : superflip \notin ball Sset p1depth.
```

In words, the superflip is not within `p1depth` moves of the solved cube, where
the depth is set by one script before the run. It has *no hypotheses left*: the six
computations it rests on, namely the two summary tables, the three move and
distance tables and the searches, each live in their own file
behind their own `Qed`. Asking Rocq what the proof assumes reports only the
primitives of its machine-integer and array interface. Nothing in the chain is
admitted.

At depth 19 this says precisely that the superflip cannot be solved in 19
moves. Two lines then turn it into *God's number $>= 20$*, in
#src("Diam20.v"): that file is where the two ends of the development meet, the
cube being defined at the bottom of the chain and the search sitting at the
top, and it first checks that the searches were indeed run at 19.

The run that proves it, measured on the reference machine, twice: once before
the fold and the two reductions and once after, the same theorem both times.

#tbl(([radius 19, search depth 17], [before], [after]),
  ([pieces], [18], [*17*]),
  ([workers], [9], [*18*]),
  ([memory per worker], [4.15 GB], [*0.85 GB*]),
  ([wall clock], [11 h 13], [*6 h 36*]),
  ([processor time], [85 h 11], [*87 h 36*]),
)

The pieces do not all take the same time. The shortest took 3 h 38 and the
longest 6 h 36, read from the times at which they finished. The run ends when
the longest piece ends, so the other sixteen workers are idle before that. Two
of the fifteen search positions, the ninth and the eleventh, are cut in half
for this reason. Were they not cut, each would take about 9 h 50, and the whole
run would take that long. If the work were shared evenly over eighteen workers
it would take 4 h 54. So about 1 h 40 is lost to idle workers, and to save it
the eight longest pieces would have to be cut in half as well.

The two columns say that the fold and the two reductions cut the wall clock by
41% and left the processor time as it was, 3% higher. The gain in wall clock
comes from the memory: a worker needs 0.85 GB, so seventeen pieces fit at once,
where 4.15 GB allowed only nine. The processor time is a surprise. On the small
test used while the reductions were written, the fold was 1.61 times slower and
the reductions 1.86 times faster. Together that is a saving of about a sixth,
and the run shows no saving at all. That small test is not to be trusted: it
subtracts two large numbers, 245 processor-seconds of table loading from 391
for the whole run, to get 146 of search. The run above is the number to trust
for the cost of the theorem. Why the two factors do not add up has not been
measured.

*Memory.* A worker holds the loaded table and nothing else that grows: the
search walks down and back up, so only the current sequence of moves is kept.
The 4.15 GB is identical to three decimals across the nine workers and the same
at every depth, and the fold is what brings it to 0.85 and lets all seventeen
pieces run at once.

*What is left.* The proof that God's number is at least 20 costs 87
processor-hours and one night. That is a measured cost, not an estimate. Two
savings are in sight and neither is large. The first is the 1 h 40 of idle
workers at the end of the run, which is a matter of how the work is shared out
and not of mathematics. The second is the factor of 3.3 against OCaml, and even
winning all of it would leave 26 processor-hours. The cost is the tree, and the
tree is 146 billion positions. Nothing else in the chain is known to be
wasteful.

= Counting in quarter turns

Counted in quarter turns there are twelve moves: the six faces one way and the
same six back. A half turn is two moves. The answer in that count is *26*
(#link("http://cube20.org")[cube20.org]). What is proved here is the lower
half: one position cannot be solved in 25 quarter turns.

== The position, and why 25 comes down to 24

The superflip is 24 quarter turns from solved, so it is not far enough away. In
August 1998 Reid posted a better position to the Cube-Lovers list
@reid1998fourspot: the *four-spot* with the superflip composed onto it. That
post is the source of this section and is transcribed beside this note.

The four-spot exchanges the front and back colours and the left and right
colours. The centres cannot move, so each of those four faces keeps its own
colour in one square, which is the spot the pattern is named after. The
superflip then turns every edge over.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    cube3dc(0,
      (cW, cW, cW, cW, cW, cW, cW, cW, cW),
      (cB, cB, cB, cB, cG, cB, cB, cB, cB),
      (cO, cO, cO, cO, cR, cO, cO, cO, cO))
    content((0, -0.45), text(size: 9pt)[the four-spot])
    cube3dc(4.4,
      (cW, cG, cW, cR, cW, cO, cW, cB, cW),
      (cB, cW, cB, cR, cG, cO, cB, cY, cB),
      (cO, cW, cO, cB, cR, cG, cO, cY, cO))
    content((4.4, -0.45), text(size: 9pt)[and with the superflip on it])
  }),
  caption: [The four-spot, and Reid's position.],
) <fspot>

Reid's position is 26 quarter turns from solved. His word for it is

#align(center)[
  $U^2 space D^2 space L space F^2 space U^(-1) space D space R^2 space B
    space U^(-1) space D^(-1) space R space L space F^2 space R space U space
    D^(-1) space R^(-1) space L space U space F^(-1) space B^(-1)$
]

That is 21 face turns, five of them half turns. It is checked by multiplying out
both sides and comparing two lists of 48 places.

Ruling out 25 is ruling out 24. A quarter turn is five four-cycles of the 48
stickers, so it is odd, and a manoeuvre of odd length gives an odd position.
Reid's position is even, so every manoeuvre for it has even length and the
searches stop at 24.

== Reid's six beginnings

The argument has two halves and only the second is a computation.

The first is Reid's Proposition 2: a manoeuvre that cannot be shortened can be
rewritten, at the same length, to begin with one of six sequences.

#align(center)[
  #grid(
    columns: (auto,) * 6,
    column-gutter: 1.6em,
    row-gutter: 0.5em,
    align: center,
    $U$, $R$, $F$, $D$, $L$, $B$,
    $U^2$, $R^2$, $F^2$, $D^2$, $L^2$, $B^2$,
    $U^(-1)$, $R^(-1)$, $F^(-1)$, $D^(-1)$, $L^(-1)$, $B^(-1)$,
  )
]

The rewriting uses three operations that change neither the product nor the
length: conjugation by one of the sixteen symmetries that fix the position,
inversion, and cyclic shift with the letters that move to the end relabelled.
The last is why this position was chosen. #src("HProp2.v") is that argument in
Rocq, and #src("HBridge.v") carries it to the orientation the search uses.

Reid does not state one hypothesis his proof needs: the manoeuvre cannot be
shortened. Without it the third turn may cancel the second. The Rocq statement
carries the hypothesis, at no cost, since a shortest manoeuvre is what is
wanted anyway.

Six searches follow. The first beginning is two turns long and is searched 22
further, the other five are three long and are searched 21 further. Each
reaches 24 turns.

== The summary, and its table

The estimate is built as before, by keeping a summary of the cube:

#block(breakable: false)[
  #tbl(([summary], [values], []),
    ([where the four middle-layer edges sit, each of them
      the right way round or not], [190 080], [$= 24 dot 22 dot 20 dot 18$]),
    ([which four corner places hold the four top corners], [70],
     [4 places among 8]),
    ([how the eight corners are twisted], [2 187], [$= 3^7$]),
    ([*the three together*], [*29 099 347 200*], []),
  )
]

The 24, 22, 20 and 18 fall by two each time because a place taken by an edge is
taken whichever way round that edge is. These summaries are the cosets of
Reid's H, which is where the H at the front of the file names comes from.

The table holds the distance from solved of each of the 29 billion summaries.
How many lie at each distance agrees with the column Reid published in 1998,
and that check is run first. The table is then folded: the sixteen symmetries
that keep the up-down axis sort the 190 080 edge values into 12 094 families, a
factor of 15.72, and one entry is kept per family. That is 883 MB, measured at
3.86 GB once loaded into the prover.

== The files

#ftbl(([Reid's argument], []),
  ([`HCoord.v`], [the three coordinates of a position, on facelet tables]),
  ([`HRoot.v`], [Reid's six positions, and the three views of them]),
  ([`HProp2.v`], [manoeuvres as words, and the three rewritings of them]),
  ([`HReid.v`], [what Proposition 2 rests on]),
  ([`HBridge.v`], [from Proposition 2 to the position the run searches]),
)

#ftbl(([the search], []),
  ([`HSearch.v`], [the quarter-turn search over Reid's table]),
  ([`HCanon.v`], [the rule the search plays by loses no manoeuvre]),
  ([`HCut.v`], [a cut throws no manoeuvre away]),
  ([`HPrefix.v`], [playing a word is stepping the state]),
  ([`HPok.v`], [the positions the search meets, and the triples it carries]),
  ([`HRunS.v`, `HSound.v`], [a search that fails is a proof that no word exists]),
)

#ftbl(([the tables, and the assembly], []),
  ([`HChk.v`], [the move tables against the coordinates]),
  ([`HEdge.v`, `HCorner.v`], [a turn acts on the datum, for edges and for corners]),
  ([`HAgree.v`], [the coordinates agree with the tables, everywhere]),
  ([`HSweepC.v`], [the three sweeps over the move tables, in six slices]),
  ([`HSweep.v`], [the sweep over the distance table, cut into twelve jobs]),
  ([`HAdmis.v`], [what that sweep buys: the estimate is never too big]),
  ([`HGlue.v`, `HBound.v`], [what the run has to give, and what it gives]),
  ([`HFinal.v`, `HAll.v`], [the bound assembled, and `qdiam25`]),
)

== The theorem, and what it cost

```coq
Theorem qdiam25 : ~ diam_le Sq 25.
```

`Sq` is the set of the twelve quarter turns, and `diam_le Sq 25` says every
position is within 25 of them. The line says it is not. Reid's position is the
witness and his word puts it at 26. Rocq reports only the primitives of its
machine-integer and array interface.

#tbl(([], [wall clock], [processor time]),
  ([building the table, in OCaml], [9 min 50], [1 h 43]),
  ([the same table as fifty-nine Rocq files], [3 h 13], [6 h 50]),
  ([the three sweeps over the move tables], [], [1 min 20]),
  ([the sweep over the distance table, twelve jobs], [2 h 51], [31 h 42]),
  ([the six searches, seventy-two pieces, twelve workers], [4 h 00], [45 h 54]),
  ([*the whole chain in Rocq*], [*10 h 32*], [*87 h 29*]),
)

The last row is not the sum of the others. It is the whole chain measured end
to end from a directory where nothing is built. The OCaml table on the first
row is built once by hand and is not part of that run.

The sweeps and the searches are nearly nine tenths of the cost. Checking the
table rather than trusting it costs about two thirds of what the searches cost.
The quarter-turn work adds eighteen hand-written Rocq files and 6 008 lines.

= One coset of the upper half

Everything above is a lower bound, and a lower bound rests on one position and
one search that finds nothing: the superflip for the twenty face turns, the
four-spot with the superflip on it for the twenty-six quarter turns.

The other half of God's number, that twenty moves always suffice, is the huge
one, and it is not proved here. What #src("Diameter.v") contains is the
reduction for it, and that reduction rests on one assumption.

The published proofs do not solve all 43 quintillion positions one at a time.
They cut the cube group into the 2 217 093 120 cosets of a subgroup and solve a
whole coset at once: one search settles every one of the 19 508 428 800
positions in it. The positions in a coset are not all the same distance from
solved; what the search shows is that none of them is more than 20. A symmetry
of the cube carries one coset to another, and the image is solved by the same
manoeuvres relabelled, so only one coset per symmetry class is searched. Two
things are then needed: that the cosets searched cover every class, and that
each search really settles its whole coset.

The first is not a computation, and #src("Canon.v") proves it. Take as
representative the least member of each class, in the order the finite type
already carries; the covering property holds because a finite set has a least
element. It is eighty lines and assumes nothing.

The second is the computation itself, the one Rokicki, Kociemba, Davidson and
Dethridge ran: about a billion seconds of processor time, more than thirty
processor years, donated by Google, over 55 882 296 families of cosets. There
is no prospect of repeating that here. What can be done is one coset, to see
what one costs and whether the pieces are in place. This section reports that
one coset, the superflip's.

== Cosets

The subgroup is generated by ten of the eighteen moves: the three turns of the
top face, the three of the bottom face, and the half turns of the other four.
Call them the ten. They generate Reid's H, met above. A coset of H is the set of positions
reached by playing the ten from a fixed position. Every position of the cube lies in exactly one coset.

#tbl(([], [count]),
  ([positions of the cube], [43 252 003 274 489 856 000]),
  ([cosets], [2 217 093 120]),
  ([positions in a coset], [19 508 428 800]),
  ([cosets we did], [1]),
)

One coset is not the upper bound and is not offered as one.

== A coset is one map

A position of a coset is named by three numbers: how the eight top and bottom
corners sit, how the eight top and bottom edges sit, and how the four middle
edges sit. The map holds one bit for each, 812 851 200 machine words of
twenty-four bits, which is 19 508 428 800 bits.

The search starts at the superflip and plays words, setting the bit of every
position of the coset it reaches. When every bit is set the theorem follows.
Thirty-two positions are not reached; each is given a word of twenty moves by
hand in #src("RowWits.v"). The words are not trusted: #src("RowWitsChk.v")
plays each one back and asks for the solved cube.

== What is reused, and what is new

Nearly everything is reused: the search, the map, the tables that step a whole
map, the ranking of the three numbers, the replay of the leftover words, the
phase one table and the program that generates it, the cube, the permutations
and the machine-integer tools.

Four things are new, and none of them is about searching.

- The rank and the sign of a permutation on machine integers. Rocq's library
  has both, but for permutations that cannot be computed.
- That a position of a coset *is* its three numbers, in both directions. Only one
  direction was there. Without the other the theorem is about triples of
  numbers and not about the cube.
- The link between the summary the search carries and the position it stands
  for. The summary is one machine word, the position forty-eight.
- Checks on the tables, one per file, so that each reports separately.

== What the proof found

Cutting a branch on the table is sound: a table that says too little only cuts
less. Stopping on it is not. The search used to stop when the table said zero
and take the position it had reached as one of the coset. A table of zeros still
says too little, so it is still allowed, yet it would stop the search everywhere
and the theorem would say nothing.

The search now stops on the position. At the bottom it tests the position it is
carrying. No part of the proof reads the table, and it costs one comparison.

== Folding the map

The map is 40 320 pages of 20 160 groups, one page for each way the eight top
and bottom corners can sit. Sixteen renamings of the cube keep the top and
bottom faces in place, send the ten to the ten and leave the superflip alone.
Two pages related by a renaming hold the same answer, so one page of each
family is enough: 2 768 of the 40 320, a factor of 14.6. A level of the search
is one pass over the map, so there is 14.6 times less of it to walk. The price
is undoing a renaming whenever a kept page is read.

The fold has to be proved as well as written: that a renaming sends a member of
the coset to a member of the coset, that undoing it gives back the position the
page stood for, and that a map sound after one level is sound after the next.
That is the largest single part of the coset's proof.

== The files

#ftbl(([the coset and its members], []),
  ([`Row.v`], [a coset, its members, and each member as a bit]),
  ([`RowMemb.v`, `RowMembi.v`], [the cube a member names, and the member a cube gives]),
  ([`RowMembChk.v`], [that bridge, with nothing left open]),
  ([`RowLeaf.v`, `RowInH.v`], [a position of H is its three ranks]),
  ([`RowInst.v`, `RowReal.v`], [the instance: the superflip's own coset]),
)

#ftbl(([ranking, and the moves], []),
  ([`Lehmer.v`], [the rank and the sign of a permutation, on machine integers]),
  ([`RowUp8ok.v` .. `RowUp4inv.v`], [unranking is a permutation, and undoes the ranking]),
  ([`RowPar8.v`, `RowPar4.v`, `RowParity.v`], [the parity tables, and how a move shifts a parity]),
  ([`RowPartC.v`, `RowPartM.v`, `RowPartU.v`], [each of the three parts is a permutation]),
  ([`RowMoveH.v`, `RowMoveC.v`, `RowMoveM.v`, `RowMoveU.v`], [a move of H is its three halves, each following its table]),
  ([`RowTab.v`, `RowTabL.v`, `RowTabP.v`, `RowTabF.v`], [the tables themselves, and the checks they pass]),
)

#ftbl(([the map and the search], []),
  ([`RowMap.v`], [the map of a coset, and the pass that steps it]),
  ([`RowRun.v`], [the search, the level loop, and what each owes]),
  ([`RowLvl.v`], [the pass again, one chunk a page instead of one a word]),
  ([`RowMask.v`], [the folded phase one table, and the moves worth trying]),
  ([`RowSrch.v`, `RowSrchP.v`], [the search with the cuts and the early stop, and its proof]),
  ([`RowMark.v`], [the leftover words marked into the map the run leaves]),
  ([`RowWits.v`, `RowWitsChk.v`], [those words, and the replay that checks them]),
  ([`RowFinal.v`], [every member of the coset is within twenty moves]),
)

#ftbl(([the fold], []),
  ([`RowFold.v`], [the map folded by the sixteen renamings]),
  ([`RowFoldSym.v`, `RowFoldConj.v`], [the fold tables are the renamings, and they conjugate]),
  ([`RowFoldPart.v`, `RowFoldSrc.v`, `RowFoldGath.v`], [a page renamed, then moved]),
  ([`RowFoldWrite.v`, `RowFoldLvl.v`], [what one write costs, and that a level keeps the map sound]),
  ([`RowFoldMem.v`, `RowFoldOk.v`], [two members that fold together stand or fall together]),
  ([`RowFoldTot.v`, `RowFoldPorb.v`], [the fold tables land in range at every index]),
  ([`RowFoldEmpty.v`, `RowFoldFinal.v`], [the map the run starts from, and the one it leaves]),
  ([`RowFoldRun.v`, `RowFoldSrch.v`], [the folded search and the folded run are sound]),
  ([`RowFoldSrchI.v`, `RowFoldSrchIP.v`], [the same search with the depth as an int, and the two are equal]),
)

#ftbl(([the two runs], []),
  ([`RowCub.v`, `RowCubi.v`, `RowCubInst.v`], [a position as twenty cubies, carried through the search]),
  ([`RowCubDef.v`, `RowFoldCubDef.v`, `RowFoldCubDefI.v`], [what each run needs, and not one proof]),
  ([`RowCubBoolI.v`, `RowFoldCubBoolI.v`], [the two runs: one boolean each, and nothing else]),
  ([`RowCubReal.v`, `RowFoldCubReal.v`], [the coset on each map, with only that boolean left open]),
  ([`RowCubProof.v`, `RowCubProofI.v`, `RowFoldCubProof.v`, `RowFoldCubProofI.v`], [what a true boolean buys]),
  ([`RowCubDoneI.v`, `RowFoldCubDoneI.v`], [run and proof joined: the two theorems]),
)

== What it cost

The coset adds sixty-six hand-written Rocq files and 15 782 lines to the work
above, besides the generated tables.

The search ran twice, over the folded map and over the unfolded one, with the
same search in both, and both times it filled the map.

#tbl(([the run], [wall clock], [processor time]),
  ([over the folded map], [6 h 00], [5 h 59]),
  ([over the unfolded map], [19 h 05], [10 h 16]),
)

The fold is worth 3.2 times on the wall clock and 1.7 times on processor time.
The two figures differ because the unfolded run spent 46% of its wall clock off
the processor and the folded run 0.5%: the unfolded map is 6.5 GB against
454 MB, so the waiting is part of what the fold saves rather than an artefact
of the machine. Either way the run does not follow the size of the map, which
is 14.6 times smaller.

An earlier folded run, identical but for holding the depth left as a unary
numeral instead of a machine integer, took 8 h 13. Counting in unary is the
enemy here too.

The phase one table is 2.9 GB of Rocq source and 4.5 GB once checked, 8 h 48 of
processor time. It is generated once and shared with the lower-bound work.

The statement has no hypothesis left.

```coq
Theorem real_row_superflip_fold_runi m :
  m \in H -> superflip * m \in ball Sset 20.
```

`H` is the group of the ten and a coset is one of its cosets. Every position of
the superflip's coset is within twenty moves. Rocq reports only the primitives of
its machine-integer and array interface. The unfolded run proves the same
statement from its own map.

= Conclusion

Two lower bounds are proved. No position of the cube is solved in 19 face
turns, and none in 25 quarter turns. In each case one position is the witness,
the superflip for the first and the four-spot with the superflip on it for the
second, and in each case the proof is a search that comes back empty over a
table of estimated distances.

That 20 and 26 always suffice is not proved here. The upper half is a different
computation: not one search that finds nothing, but two billion searches that
must each find everything. One of the two billion was done, and the section
above says what it cost.

The three share a trunk. The cube itself, as permutations of the forty-eight
facelets, with the eighteen moves and the group they generate. Balls, and what
it means for a position to be within $d$ moves. The abstract search, whose
contract is that a false answer is a proof. The rule that any summary of a
position, together with any table that passes one check, gives an estimate that
is never too big. And the tables themselves, held as machine integers in arrays
rather than as lists of unary numbers.

What each of the three needed of its own:

- *The twenty face turns.* The phase one summary, which is the edge flips and
  the slice, its table, and the certificate that checks the table. Three
  viewing angles of the same search, and seventeen pieces run side by side.
- *The twenty-six quarter turns.* Reid's Proposition 2, which is the one piece
  of the development argued by hand rather than computed, and the parity
  argument that turns 25 into 24. A second and much larger summary, 29 billion
  values, with a table of its own and a sweep of its own.
- *One coset.* A coset held as a map of bits rather than as a tree of
  positions. That needs the rank and the sign of a permutation on machine
  integers, the bijection between a position and its three ranks, a pass that
  steps a whole map one move at a time, the fold by the sixteen renamings, and
  words supplied by hand for the positions the search does not reach.

The whole development, counted in hand-written Rocq and leaving out the
generated tables, is 36 294 lines. Each line of the table counts what that
piece adds to the ones above it.

#tbl(([], [files], [lines]),
  ([the superflip, for the twenty face turns], [53], [14 504]),
  ([the four-spot, for the twenty-six quarter turns], [18], [6 008]),
  ([one coset of the upper bound], [66], [15 782]),
  ([*in all*], [*137*], [*36 294*]),
)

One point is worth recording. Our own OCaml prototype for the first bound
dropped six of the thirty beginnings it should have tried. It ran for hours and
gave the expected answer. The Rocq proof is what found it. A cut that is too
greedy does not make a search fail; it makes it faster, and it makes it agree
with you.

This development was written with the help of Claude, Anthropic's coding
assistant, which is recorded as a co-author of 656 of the 682 commits of
`code/Rubik`.

The sources are at
#link("https://github.com/thery/DoubleCover/tree/main/code/Rubik")[`github.com/thery/DoubleCover/code/Rubik`],
with the note, its figures and Reid's transcribed post beside them.


#pagebreak(weak: true)

#bibliography("rubik20-note.bib", title: [References], style: "springer-mathphys")
