#set page(paper: "a4", margin: 2.4cm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1", supplement: [section])
#set list(marker: [-])
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
// A word of moves in raw type, with the pairs starting at the turns in `un`
// underlined and those starting at the turns in `ov` overlined (turns count
// from 1).  A turn may be in one pair of each kind.
#let markword(w, un, ov) = {
  let ws = w.split(" ")
  let n = ws.len()
  for i in range(n) {
    let k = i + 1
    let t = raw(ws.at(i))
    if un.any(a => a == k or a + 1 == k) { t = underline(offset: 3.5pt, t) }
    if ov.any(a => a == k or a + 1 == k) { t = overline(offset: -9pt, t) }
    t
    if k < n {
      let sp = raw(" ")
      if un.contains(k) { sp = underline(offset: 3.5pt, sp) }
      if ov.contains(k) { sp = overline(offset: -9pt, sp) }
      sp
    }
  }
}

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
  #text(size: 17pt)[*Playing with the Rubik's Cube and its God's number in Rocq*]

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
  *Abstract.* 
  One needs no more than 20 turns to solve any Rubik's cube position.
  This is called God's number and was computed in 2010. This note presents
  3 smaller results
  about the Rubik's cube that are proved in Rocq. First, we prove that 20 is a
  lower bound. Second, we change
  metric (counting half turns as 2 moves) and
  prove that in this case 26 is a lower bound. Finally, the published
  computation of God's number (35 CPU years) splits the cube into the 2 217 093 120 cosets of a subgroup, one
  search to a coset. We formalise
  the correctness of the coset search, and certify the computation on one such
  coset.

  #v(0.4em)
  *Keywords.* Rubik's cube, God's number, formal proof, Rocq, group theory.
]]

#v(0.6em)

= The problem

A Rubik's cube is built from 26 small cubes: 8 corners with 3 stickers each,
12 edges with 2 stickers each and 6 centres. The centres do not move. A turn
moves 4 corners and 4 edges, and rotates a centre.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    cube3dt(0)
    let key(y, fill, label, body) = {
      rect((3.1, y), (3.55, y - 0.45), fill: fill, stroke: 0.5pt)
      content((3.325, y - 0.225), text(size: 7.5pt)[#label])
      content((3.75, y - 0.225), text(size: 9pt)[#body], anchor: "west")
    }
    key(3.3, cCor, "c", [8 corners])
    key(2.6, cEdg, "e", [12 edges])
    key(1.9, cCen, "U", [6 centres])
  }),
  caption:[Anatomy of the cube],
) <pieces>

Not every arrangement of the pieces can be reached by turning faces. The number
of possible arrangements is

$ 8! dot 3^7 dot 12! dot 2^11 slash 2 = 43 space 252 space 003 space 274 space 489 space 856 space 000 approx 4.3 dot 10^19. $

The 8 corners can be in any order ($8!$). Their orientations are free, except
for the last one ($3^7$). The same holds for the 12 edges ($12!$ and $2^11$).
The result is divided by 2, because corners and edges are not independent.

Turning one face is a _move_. A half turn counts as one move, like a quarter
turn. The number of moves needed by the worst position is called _God's
number_. Counting a half turn as one move is a choice. A half turn can also
count as 2 moves. This gives a second number for the same cube. We prove a
lower bound for each.

We take one position: the *superflip*.
Every small cube is at its right position, but all the edges have the wrong
orientation.
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
The superflip is left unchanged by 
all 48 symmetries of the cube.
We use it to prove the lower bound.

= The cube as permutations

There are several ways to represent the Rubik's cube. We use stickers. There
are 6 faces of 9 stickers. We remove the 6 centre stickers, which never move.
The other 48 stickers are numbered from 0 to 47, as in @cube3d and @net. A move
is then a rearrangement of the 48 stickers. Each face has 8 of them, taken left
to right and top to bottom, with the centre skipped. Up gets 0--7, left 8--15, front 16--23, right
24--31, back 32--39 and down 40--47.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    cube3dn(0)
    // the turn of the top face, clockwise seen from above
    bezier((-1.15, 3.75), (1.15, 3.75), (0, 4.55), mark: (end: ">"), stroke: 0.7pt)
    content((0, 4.75), text(size: 9pt)[the move $U$])
  }),
  caption: [The top, front and right faces, and the turn of the top one.],
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
  caption: [The cube unfolded, with all 48 places numbered.],
) <net>

A move sends each sticker to a new place. For example,
if we turn the top face clockwise,
the sticker in corner 0 goes to
corner 2, the one in 2 to 7, the one in 7 to 5 and the one in 5 back to 0. This is a cycle of 4 steps, written $(0 space 2 space 7 space 5)$. The 4 edge
stickers of that face do the same: $(1 space 4 space 6 space 3)$. The turn also
moves the top row of each side face to the next side face: front to left, left
to back, back to right, right to front. This gives 3 more cycles,
$(8 space 32 space 24 space 16)$ and 2 similar ones. @uturn shows the whole
move. Each square shows the sticker that is there after the turn. For example,
the top row of the left face now holds 16, 17 and 18, the stickers that came
from the front. 

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

There are 6 clockwise quarter turns: up, right, front, down, left and back.
Each of them can also be done twice or backwards. This gives the _18 moves_:

#align(center)[
  #grid(
    columns: (auto,) * 6,
    column-gutter: 1.6em,
    row-gutter: 0.5em,
    align: center,
    `U`, `R`, `F`, `D`, `L`, `B`,
    `U2`, `R2`, `F2`, `D2`, `L2`, `B2`,
    `U'`, `R'`, `F'`, `D'`, `L'`, `B'`,
  )
]
A move done _twice_ is written `U2`, and a move done _backwards_ is written
`U'`. A position is a product of moves, written as a _word_. For example,
`R U R' U'` is a word of length 4. The set of all positions is a group $G$, the
_cube group_. A position solved in $d$ moves is a word of $d$ moves. The
positions solved in at most $d$ moves form the _ball of radius $d$_ around the
solved cube. God's number is the diameter of the Cayley graph.

== The cube in Rocq

We use the Rocq prover @rocq and its Mathcomp library @mathcomp. The file
#src("Rubik333.v") is a direct translation of the paragraphs above:

```coq
Definition facelet := 'I_48.

Definition Umove : {perm facelet} := cyc [:: 0@; 2@; 7@; 5@] * cyc [:: 1@; 4@;
6@; 3@] * cyc [:: 8@; 32@; 24@; 16@] * cyc [:: 9@; 33@; 25@; 17@] * cyc [:: 10@;
34@; 26@; 18@]. (* ... and five more, one per face ... *)

Definition faces : seq {perm facelet} :=
  [:: Umove; Rmove; Fmove; Dmove; Lmove; Bmove].
Definition moves : seq {perm facelet} :=
  flatten [seq [:: g; g ^+ 2; g ^-1] | g <- faces].
Definition G : {group {perm facelet}} := <<Sset>>.
```

Line by line:

- `'I_48` is the type of numbers below 48. It is a finite type.
- `{perm facelet}` is the type of _permutations_ of those facelets.
- `cyc [:: 0@; 2@; 7@; 5@]` is the _cycle_ that sends 0 to 2, 2 to 7, 7 to 5
  and 5 back to 0, leaving the other 44 places where they are. The
  `@` is local notation turning a plain number into a facelet.
- The symbol `*` composes 2 permutations. So `Umove` is the cycles of @uturn
  put together. `g ^+ 2` is the turn done twice, and `g ^-1` the turn undone.
  The order of composition is the opposite of the usual one. Mathcomp applies
  permutations on the right, so `(g * m) f` is `m (g f)`.
- `seq` is a list. `faces` is the list of the 6 clockwise quarter turns.
  `moves` takes 3 moves for each face, which gives the 18 moves.
- `<<Sset>>` is the group generated by the moves: all the positions that we
  can reach by composing moves. This is the cube group.

The superflip is defined in #src("Diameter.v"). It is made of 12 swaps, one
for each edge, that exchange the 2 stickers of the edge:

```coq
Definition Spcyc : seq (seq facelet) :=
  [:: [:: 1@; 33@]; [:: 3@; 9@]; [:: 4@; 25@];
      (* ... nine more, one per edge ... *) ].

Definition superflip : {perm facelet} := \prod_(l <- Spcyc) cyc l.
```

This makes it a permutation, but not yet a legal position. For this, we have to
prove that it belongs to $G$. The proof is one equality, with this word of 20
moves:

#align(center)[`U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2`]

= Searching for the lower bound <lowerbound>

We want to show that the superflip cannot be solved in 19 moves or less. The
simple approach is to try every word of at most 19 moves from the superflip. If
the solved cube never appears, 20 is a lower bound. But a tree of depth 19 with
18 branches at each node has $18^19$ words. This is far too many. We need to
refine the search.

== The pruning estimate

A first refinement is a test that cuts early the branches that cannot succeed.
For this, we give each position a rough lower bound $h$ on the number of moves
still needed. If $h$ is 20 and only 18 moves remain, the branch cannot reach
the solved cube in time. It is cut, with everything below it, as @tree shows.

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
    tlbl(-5.4, -1.45, [$h = 17$])
    tlbl(-1.8, -1.45, [$h = 20$])
    tlbl(1.8, -1.45, [$h = 11$])
    tlbl(5.1, -1.05, [$dots.h$])
    tlbl(5.4, -1.45, [and 15 more])
    tlbl(-1.8, -1.85, text(fill: rgb("#b00"))[#sym.times ~ cut: 20 > 18])
    for x in (-5.4, 1.8) {
      tedge(x, -1.6, x - 0.9, -2.4)
      tedge(x, -1.6, x + 0.9, -2.4)
      tlbl(x, -2.65, [18 moves left])
    }
  }),
  caption: [The search, and its scissors.],
) <tree>

Such a lower bound is called an *admissible* estimate. A depth-first search
that increases its depth step by step and cuts with such an estimate is Korf's
IDA\* @korf1985ida.

== Getting a cheap estimate

The idea behind our estimate is to forget most of the cube. We keep only part
of the information, for example how the corners are twisted and where the 4
middle-layer edges are. We call what is left a _summary_. Many positions share
the same summary, and they get the same estimate. Moves act on summaries as
well as on cubes. There are few summaries, so we can precompute the exact distance of each one to the solved summary,
and store it in a table. This
gives $h$: take a position, compute its summary and read its distance in the
table. The idea comes from Culberson and Schaeffer, who call such a table a
_pattern database_ @culberson1998pattern. Korf solved the cube optimally with 3
of them @korf1997rubik.

We use Kociemba's summary, from his two-phase solver @kociemba. We call it the
_phase 1 summary_. @encoding shows the 3 things it records. A corner has one
sticker of the up or down face. This sticker is in one of 3 places, numbered
0, 1 or 2. An edge is either the right way round or turned over,
numbered 0 or 1. The 4 edges of the middle layer are in 4 of the 12 edge slots. The figure
shades these slots on the 2 visible faces, where 3 of the 4 can be seen.
Nothing else is recorded.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    content((-4.4, 4.5), text(size: 9pt)[*a corner*: the place of its up sticker])
    cubie((-6.2, 2.5), "top")
    cubie((-4.4, 2.5), "front")
    cubie((-2.6, 2.5), "right")
    content((-6.2, 2.15), text(size: 9pt)[0])
    content((-4.4, 2.15), text(size: 9pt)[1])
    content((-2.6, 2.15), text(size: 9pt)[2])
    content((-4.4, 1.5), text(size: 9pt)[*an edge*: turned over or not])
    cubie((-5.3, -0.4), "top")
    cubie((-3.5, -0.4), "front")
    content((-5.3, -0.75), text(size: 9pt)[0])
    content((-3.5, -0.75), text(size: 9pt)[1])
    content((3.4, 4.5), text(size: 9pt)[*the middle layer*: its 4 slots])
    cube3dn(3.4, hi: (19, 20, 27, 28))
  }),
  caption: [The 3 things a summary records.],
) <encoding>

The summary is the product of the 3 values:

#tbl(([summary], [values], []),
  ([how the 8 corners are twisted], [2 187], [$= 3^7$]),
  ([how the 12 edges are flipped], [2 048], [$= 2^11$]),
  ([where the 4 middle-layer edges sit], [495], [4 places among 12]),
  ([*the summary*], [*2 217 093 120*], []),
)

Every summary stands for exactly 19 508 428 800 positions. The table gives,
for each summary, its distance from the solved summary. A distance is never
more than 12, so 4 bits hold one entry, and a 63-bit machine word holds 15
entries. The whole table is _1.18 GB_. The cut is very effective. A search at
depth 14 visits only 445 398 nodes. Without the cut, the same tree has
$1.03 dot 10^15$ nodes. 

== Searching in Rocq

The search is generic. It is defined in the file #src("Search.v"). It takes a
group, a set of moves, an estimate $h$ and 2 hypotheses on $h$:

```coq
Hypothesis h1    : h 1 = 0.
Hypothesis hstep : forall g m, m \in S -> h g <= (h (g * m)).+1.

Fixpoint search (d : nat) (g : gT) : bool := (h g <= d) && ((g == 1) || (if d is
d'.+1 then has (fun m => search d' (g * m)) Sseq else false)).

Corollary searchN d g : search d g = false -> g \notin ball S d.
```

Line by line:

- `gT` is the group. It is then instantiated with the cube group.
- `1` is the unit of that group, the solved position for the cube. So with
  `h 1 = 0` we ask the estimate to be 0 on the solved cube, and `g == 1` tests
  whether the search has reached the solved position.
- `Sseq` is the list of the 18 moves, and `S` is the same thing seen as a set.
- `g * m` is the position `g` followed by the move `m`.
- `h g <= d` is the cut. `(h (g * m)).+1` is the estimate after `m` plus
  one, so by `hstep` one move changes the estimate by at most one.
- `has (fun m => search d' (g * m)) Sseq` tries every move with one fewer move
  left, and answers as soon as one of them succeeds.

The last line is what we need. If the search returns false, the position is
not in the ball of radius $d$. The next subsections describe the improvements
that give our final search.

== Searching with a summary

The estimate is built in a second generic file, #src("Coord.v"). It takes the
summary of a position, the action of a move on a summary and the table of
distances. It asks one condition on the summary and 2 on the table.

```coq
Variable coord : {perm facelet} -> X.
Variable act   : X -> {perm facelet} -> X.
Hypothesis coordM : forall g m, coord (g * m) = act (coord g) m.

Variable D : X -> nat.
Hypothesis D0    : D (coord 1) = 0.
Hypothesis Dstep : forall x m, m \in Sset -> D x <= (D (act x m)).+1.
```

`X` is the type of summaries, and `coord` gives the summary of a position.
`act` applies a move directly to a summary, without going back to the
position. By `coordM`, the two agree: applying a move and then taking the
summary gives the same result as `act`.

The search of #src("Search.v") is refined to carry the summary with the
position. The summary is updated with `act` at each move. The position is still
needed, to test whether the cube is solved. Here is the refined search, with
simpler names and some details left out. The real one is `searchz3` in
#src("Farp1.v").

```coq
Fixpoint search (d : nat) (g : gT) (x : summary) (p : move) : bool :=
  (D x <= d) &&
  ((g == 1) ||
   (if d is d'.+1
    then has (fun m => search d' (g * m) (act x m) m) (allowed p)
    else false)).
```
Here are some explanations:

- `D x <= d` is the cut. It reads the table at the summary `x`.
- `g == 1` tests whether the cube is solved.
- `g * m` moves the position and `act x m` moves the summary. The summary
  never has to be recomputed from the position.
- `p` is the last move, and `allowed p` is the list of moves allowed after
  it. This is explained in @redundant.

== Verifying the table <verify>

For the phase 1 summary, `D` is a lookup in the phase 1 table, so `D0` and
`Dstep` become 2 statements about that table:

- the entry of the solved summary is 0;
- every entry is at most one more than the entry reached from it by any of the
  18 moves.

The table is produced by an OCaml program, and it gives the exact distance.
But the table is not trusted. The 2 statements above are checked in Rocq by
computation. A table full of zeros would also pass these checks, but then the
search would cut nothing. The entries of the table do not depend on each other.
So the second check, the most expensive one, is cut into slices, one file for
each slice. The files are checked in parallel, since Rocq compiles files
separately. This takes 10 minutes. All the timings in this note are measured on
the same machine, the _reference machine_: a dual-socket Intel Xeon E5-2667 at
2.9 GHz, with 12 cores, 24 threads and 62 GB of memory.

== Removing redundant moves <redundant>

Many words lead to the same position. We use 2 ideas to leave some of them
out. The first idea is to avoid repetition. For example, after a `U` we do not
need to try `U`, `U2` or `U'`. Shorter words, at a smaller depth, already reach
these positions. This leaves 15 moves instead of 18. Opposite faces give a
weaker form of the same argument. `U D` and `D U` give the same position, so we
keep only one of the 2 orders. We privilege the top, right or front face first. We
call this the _order convention_. From the second move on, it leaves 15 moves
after a turn of the top, right or front face, and 12 after a turn of the
bottom, left or back face. The second idea is symmetry. The superflip is
unchanged by all 48 symmetries of the cube. So for the first move we only need
the turns of one face. We choose the top face. By symmetry again, we only need
`U` and `U2`, since `U'` is the mirror image of `U`. 
The search is then parallelised at depth 2: 2 first moves times 15
second moves is 30 _prefixes_, and each prefix is searched in a file of its
own.

== Composing summaries 

We can turn the whole cube around the axis through 2 opposite corners. We get
the same position, seen from another side. Its summary gives another entry of
the same table. So each position has 3 summaries, and the maximum of the 3
values is still an admissible estimate. This costs 3 reads of the table
instead of one. But it is worth it, because the tree is much smaller.

== Folding the table <foldtab>

The summary is built around the up-down axis. Of the 48 symmetries, 16 keep
this axis. They turn one summary into another. They sort the 1 013 760 values
of flip and slice into 64 430 families. One entry for each family is enough, so
the table can be made smaller. In the code, the change is one definition. The
lookup was

```coq
Definition Dp1i (tw x : int) : int := p1get (p1idx tw x).
```

and it became

```coq
Definition Dp1ri (tw r : int) : int :=
  p1get (p1foldi (frep r) (twsym tw (fsym r))).
```

`frep r` is the representative of the family. `fsym r` is the symmetry that
sends the value to it. `twsym tw (fsym r)` is the twist sent by the same
symmetry. Each lookup costs 3 more reads, in a table 15.73 times smaller.

Tables reduced by symmetry are common in cube solvers. With the fold, the
search is 1.61 times slower at depth 16. But a search worker goes down from
4.15 GB to 3.6 GB, so 18 of them can run at the same time. And checking the
table goes down from about 5.4 processor hours to 1.35.

== Conclusion on the first lower bound

The development for this lower bound has 44 files: 9 about the cube (2 500
lines), 15 about the search (4 900 lines) and 20 about the tables (5 200
lines). Building the tables costs the same for any radius of the search. Here
are the times, measured from a clean tree on the reference machine:

#tbl(([], [wall clock], [processor time]),
  ([emitting the tables and compiling them to native code], [17 min 21], [52 min 13]),
  ([the coordinate and summary tables], [22 min 46], [21 min 15]),
  ([the search and the estimate, over no data at all], [11 min 02], [30 min 45]),
  ([the 4 certificates for the move and distance tables], [56 s], [2 min 27]),
  ([the fold: 12 checks and 27 slices], [9 min 52], [47 min 57]),
  ([the shape check against the dummy table], [18 s], [16 s]),
  ([*in total*], [*1 h 02*], [*2 h 35*]),
)

The second line runs on one core, so more cores do not help. The first and
fifth lines are mostly the OCaml compiler, turning a table into native code.
Together they take 100 of the 155 processor-minutes.

The search visits 137 607 893 106 positions. The smallest piece has
3 067 879 204 and the largest 8 527 685 275. Between depths 17 and 19, the tree
grows by 12.22 from one level to the next. We measured the run twice, once
before the fold and once after. The theorem is the same
both times.

#tbl(([radius 19, search depth 17], [before], [after]),
  ([pieces], [18], [*30*]),
  ([workers], [9], [*18*]),
  ([memory per worker], [4.15 GB], [*3.6 GB*]),
  ([wall clock], [11 h 13], [*5 h 48*]),
  ([processor time], [85 h 11], [*89 h 27*]),
)
The 30 pieces balance the run. Each piece is one prefix of 2 moves. They are
compiled longest first, since make starts them in the order it is given. The
pieces are far from equal. The longest takes 5 h 43 of processor time, and the
shortest 1 h 43. So the longest piece sets the wall clock. The wall clock, 5 h 48, is only 5
minutes more than the best that any order of these 30 pieces can give. 

= Counting in quarter turns <quarter>

We have proved that God's number is at least 20. We now count the moves
differently. In quarter turns there are 12 moves: the 6 faces turned one way,
and the same 6 turned back. A half turn counts as 2 moves. In this count, the
answer is *26* (#link("http://cube20.org")[cube20.org]). 
== The position

The superflip is only 24 quarter turns from solved, so it is not far enough.
Reid posted a better position to the Cube-Lovers list in August 1998
@reid1998fourspot: the superflip composed with four spot, the four-spot pattern
with the superflip on top of it. In the following, we call it *superflip4*.

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
  caption: [The four-spot, and superflip4.],
) <fspot>

Superflip4 is 26 quarter turns from solved. Here is the word given for it, with
the half turns written out:

#align(center)[`U U D D L F F U' D R R B U' D' R L F F R U D' R' L U F' B'`]
We want to prove that this position cannot be solved in 25 quarter turns.
The parity of permutations saves one level of search (24 instead of 25). A cycle of 4 stickers is
the product of 3 swaps, so it is an odd permutation. A quarter turn is 5 cycles
of 4 stickers, so it is odd too. So a word of even length gives an even permutation, and a word of odd length
gives an odd one. This argument is in #src("HBound.v").

Because of this word of 26 moves, superflip4 is even. So all its words have an
even length. If superflip4 has no word of at most 24 moves, it is exactly 26
moves from solved. 
== The 6 prefixes

Every shortest word for superflip4 can be rewritten, at the same length, so that
it begins with one of 6 prefixes @reid1998fourspot:

#align(center)[
  #grid(
    columns: (auto,) * 3,
    column-gutter: 2.4em,
    row-gutter: 0.5em,
    align: center,
    `R U`, `R' U D`, `R' U F'`,
    `R' U R'`, `R' U B'`, `R' U L'`,
  )
]

The searches start from those 6. In order to prove this fact, we split the
12 quarter turns into 2 sets:

#align(center)[
  $cal(A) = {$ `U`, `U'`, `D`, `D'` $}$, #h(2em)
  $cal(C) = {$ `R`, `R'`, `F`, `F'`, `L`, `L'`, `B`, `B'` $}$.
]

A word made only of turns from $cal(A)$ leaves the 4 middle edges untouched,
and superflip4 has them flipped, so no such word gives superflip4. A word made
only of turns from $cal(C)$ never flips an edge, and superflip4 has every edge
flipped, so no such word gives it either. Any word for superflip4 therefore uses
turns from both sets, so somewhere in it there is a two-letter subword made of a letter of $cal(A)$ and a letter of $cal(C)$.

Each of the 6 prefixes starts with a turn from $cal(C)$ followed by a turn
from $cal(A)$, so we want a word for superflip4 that starts with such a
subword.
Recall the word we gave for it:

#align(center)[#markword("U U D D L F F U' D R R B U' D' R L F F R U D' R' L U F' B'",
  (7, 12, 19, 23), (4, 9, 14, 21, 24))]
Reading along it, 4 two-letter subwords have the right order and 5 have the
wrong order. We take the first one with the right order, `F U'`, and call it
$q$. A word may have had only subwords with the wrong order. In 
that case, we would then
invert it first: superflip4 is its own inverse, so the inverse is again a word
for it, of the same length, and 
the orders are swapped. Here the inverse is

#align(center)[#markword("B F U' L' R D U' R' F' F' L' R' D U B' R' R' D' U F' F' L' D' D' U' U'",
  (2, 5, 12, 17, 22), (3, 7, 14, 19))]

with, as expected, 5 subwords in the right order and 4 in the wrong order.

Let us go back to our two-letter subword $q$. It has 6 turns before it. Write
$x$ for them, `U U D D L F`, and $w$ for what follows $q$, so that $x q w = P$,
where $P$ is superflip4. Then $q w = x^(-1) P$, and therefore

#align(center)[
  $q w (P^(-1) x P) = x^(-1) P P^(-1) x P = P .$
]

$P^(-1) x P$ is not longer than $x$:

#align(center)[
  $P^(-1) x P = (P^(-1) mono(U) P) (P^(-1) mono(U) P) (P^(-1) mono(D) P)
    (P^(-1) mono(D) P) (P^(-1) mono(L) P) (P^(-1) mono(F) P)
    = mono(U) space mono(U) space mono(D) space mono(D) space mono(R) space
      mono(B) .$
]

The first step is done: $q w$ followed by those 6 turns is a word for
superflip4 of the same length, beginning with $q$.

#align(center)[`F U' D R R B U' D' R L F F R U D' R' L U F' B' U U D D R B`]

The second step uses symmetries. A symmetry of the cube that leaves
superflip4 unchanged carries a word for it to another word for it, of the same
length. Of the 48 symmetries, 16 do that. The superflip is unchanged by
all 48, but the four-spot is not: it leaves the top and bottom faces alone and
exchanges the colours of the other 4 in pairs, so it singles out the up-down
axis, the line through the centres of the top and bottom faces. A symmetry
that moves that axis carries the four-spot to the same pattern about another
axis, which is another position. The 16 that keep the axis are the ones
that leave superflip4 alone. They make the letter of $q$ from $cal(A)$ into `U`,
and the letter from $cal(C)$ into `R` or `R'`, so $q$ becomes `R U` or `R' U`.
In our example $q$ is `F U'`. The mirror that swaps left and right fixes the
front face and reverses the direction of every turn, so `F U'` becomes `F' U`. A
quarter rotation about the up-down axis then carries the front face to the right
one, and `F' U` becomes `R' U`.

A word starting with `R U` needs nothing more, which is the prefix of 2
turns. When it starts with `R' U` we look at the third turn. For 6 of the
possible turns, we get words that a symmetry or an inversion brings back to the
`R U` case, and 5 do not. Those 5 are the prefixes of 3 turns.

== The summary, and its table

The estimate is built as before. We take the summary Reid uses in the
quarter-turn count. Against the phase 1 summary of the first bound, it keeps
the corner twist, the same 2 187 values, and replaces the edge flips and the
slice by where the 4 middle edges sit with their flips, and by which 4
corner places hold the top corners.

#block(breakable: false)[
  #tbl(([summary], [values], []),
    ([where the 4 middle-layer edges sit, each of them
      the right way round or not], [190 080], [$= 24 dot 22 dot 20 dot 18$]),
    ([which 4 corner places hold the 4 top corners], [70],
     [4 places among 8]),
    ([how the 8 corners are twisted], [2 187], [$= 3^7$]),
    ([*the 3 together*], [*29 099 347 200*], []),
  )
]

Each of the 4 edges can sit in any free slot, either way round. That gives 24
choices for the first, and 2 fewer for each of the others, since a slot taken
is taken whichever way round the edge in it lies. A summary is the coset of a
subgroup H of the cube group, which is why the file names of this section start
with H. It is not the subgroup of the first bound, and the summaries are
13 times as many, 29 billion against 2.2 billion.

The table holds the distance from solved of each of the 29 billion summaries.
The number of summaries at each distance agrees with the column published in
1998, and we check that first. The table is then folded. The 16 symmetries
that keep the up-down axis sort the 190 080 edge values into 12 094 families, a
factor of 15.72, and one entry is kept per family. That is 883 MB, and 3.86 GB
once loaded into the prover.

== Conclusion on the second lower bound

The word of 26 moves and the 6 searches together show that superflip4 is
exactly 26 quarter turns from solved. So in quarter turns, God's number is at
least 26. The development for this lower bound has 19 files (6 100 lines). The
argument for the 6 prefixes is in #src("HProp2.v"), the search in
#src("HSearch.v"), the checks in #src("HSweep.v") and the bound in
#src("HAll.v"). Here are the times, measured from a clean tree on the reference
machine:

#tbl(([], [wall clock], [processor time]),
  ([building the table, in OCaml], [9 min 50], [1 h 43]),
  ([the same table as 59 Rocq files], [3 h 13], [6 h 50]),
  ([checking the 3 move tables], [], [1 min 20]),
  ([checking the distance table, 12 jobs], [2 h 51], [31 h 42]),
  ([the 6 searches, 72 pieces, 12 workers], [4 h 00], [45 h 54]),
  ([*the whole chain in Rocq*], [*10 h 32*], [*87 h 29*]),
)

The last row is measured end to end, from a directory where nothing is built.
It is not the sum of the others. The OCaml table of the first row is built once
by hand, and it is not part of that run. The checks and the searches are nearly
nine tenths of the cost. Checking the table, instead of trusting it, costs
about two thirds of what the searches cost.

= One coset of the upper half

So far we have dealt with lower bounds. This section is about the upper
bound. Every position of the cube is solved in 20 moves or fewer. The idea of the big computation is the following.
Take a subgroup $H$ of $G$. Every position $p$ lies in
exactly one coset $x H$. 
So the problem of proving that the
diameter of $G$ is at most 20 is reduced to many
independent smaller problems:
every position of $x H$ is at most 20 moves from solved.
In this note, we are not going to tackle the problem 
of how the representatives of the cosets are generated.
We are going to prove the algorithm that checks 
that, given an arbitrary $x$,
every position of $x H$ is at most 20 moves from solved. As an application, we then run it inside Rocq with the superflip for $x$. This shows that all the positions of
the superflip's coset are at distance at most 20.

== Marking algorithm

To check that every position of a coset is at most 20 moves from solved,
we use a _marking_ algorithm. Each position of $x H$ gets one bit.
This bit is initially set to 0. The marking works iteratively. For each
level $d$, from 0 to 20, we list the words of length $d$. A word gives a
position. If this position is in $x H$, we set its bit to 1. At the end,
the bits set to 1 are exactly the positions of $x H$ within 20 moves. If
no bit is left at 0, every position of the coset is solved in 20 moves
or fewer.

We call the bits of a coset its _map_. The bits are stored in machine words.
An array in Rocq may hold 4 194 303 entries, so a map larger than that is an
array of chunks, each chunk an array of words.

== Choosing $H$ <choosingH>

To derive an effective marking algorithm, the choice 
of the subgroup $H$ is crucial. The one we chose is 
the one that is associated with the phase 1 summary.
It is easy to check that applying 
10 of the 18 moves (`U`, `U2`,
`U'`, `D`, `D2`, `D'`, `R2`, `L2`, `F2` and `B2`)
to a position does not change its summary.
In fact, if we take $H$ as the subgroup generated
by these 10 moves, the elements of $x H$ are exactly
the positions that have the same summary as $x$.
$H$ has other useful properties.
$H$ contains exactly 19 508 428 800 positions. So a coset is 19 508 428 800 bits,
about 2.4 GB. This fits in the memory of a desktop machine. There are
2 217 093 120 cosets. So up to 2 217 093 120 problems can be run in
parallel. 
#tbl(([], [count]),
  ([positions of the cube], [43 252 003 274 489 856 000]),
  ([cosets], [2 217 093 120]),
  ([positions in a coset], [19 508 428 800]),
)
Note that because of symmetries the number of cosets
to check can be reduced to 138 639 780. With a further reduction, to
55 882 296 cosets, the whole computation took about 35 CPU years.

Checking membership for $x H$ is quick. A position $p$ is in $x H$ exactly
when $x^(-1) p$ is in $H$, that is, when the summary of $x^(-1) p$ is
the solved one. The bit of a position $x h$ of the coset is indexed by
$h$. So we start our enumeration of the words of length $d$ from
$x^(-1)$. We apply the $d$ moves of a word. If the position $h$ we
reach is in $H$, that is, if its summary is the solved one,
we set the bit of $h$.

The phase 1 table gives us the distance to the solved summary. For a position, this is the number of moves needed to bring it into $H$. We use it to cut the enumeration, as in the search of @lowerbound. 
Remember that we start from $x^(-1)$. We
build the words of length $d$ one move at a time. Say $k$ moves have been applied to produce $x^(-1) w$, and the table gives $t$ for $x^(-1) w$. If $k + t > d$, no word that continues from there can end in $H$ after $d$ moves: its distance is too high. So we can drop this branch. 

== Structuring the map

An element of $H$ has the solved summary: no corner is twisted, no edge is
flipped and the 4 middle edges are in the middle layer. So the element $h$
that indexes a bit is named by 3 numbers: how the 8 corners of the
top and bottom layers sit, how the 8 edges of those layers sit and how the
4 middle edges sit. That is 40 320 by 40 320 by 24 arrangements, but half of
those triples cannot occur: on the cube the corners and the edges are always
permuted with the same sign.

The bits are laid out the way Rokicki's own program lays them out, and the
layout is what makes the next subsection cheap. A page is one arrangement of the
corners. Inside a page, a group is a pair of arrangements of the outer edges,
the 2 that differ by exchanging 2 edges, and the group's
24 bits are the 24 arrangements of the middle edges, the
12 even ones low and the 12 odd ones high. The parity determines which
arrangement of the pair a bit stands for, which is how the impossible half
disappears with nothing left to store.

A machine word holds 48 bits, so one word holds the same group on 2
pages, the corner arrangements of even and odd rank, the odd one in the top
half. The map is then 20 160 times 20 160 such words: 406 425 600 words, 3.25
GB, in 194 chunks of 2 million words. The map and its indexing are #src("Row.v") and
#src("RowMap.v").

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let tn = 7.5pt

    // ---- the deck of pages ------------------------------------------------
    for i in range(4) {
      let o = (3 - i) * 0.13
      rect((o, o), (1.7 + o, 1.4 + o), fill: white, stroke: 0.4pt)
    }
    content((0.85, 0.7), text(size: 8.5pt)[a page])
    content((0.85, -0.45), text(size: tn)[40 320 pages, one for])
    content((0.85, -0.78), text(size: tn)[each corner arrangement])

    // ---- one page, opened into its groups ---------------------------------
    line((2.3, 1.4), (3.5, 1.4), stroke: (dash: "dotted", thickness: 0.4pt))
    line((2.0, 0.0), (3.5, 0.0), stroke: (dash: "dotted", thickness: 0.4pt))
    for i in range(7) {
      rect((3.5, i * 0.2), (5.3, i * 0.2 + 0.2),
           fill: if i == 4 { luma(205) } else { white }, stroke: 0.4pt)
    }
    content((7.7, 1.95), text(size: tn)[20 160 groups in a page, one for])
    content((7.7, 1.62), text(size: tn)[each pair of outer-edge arrangements,])
    content((7.7, 1.29), text(size: tn)[and a group is one machine word])

    // ---- that group, as the forty-eight bits of one word ------------------
    let x0 = 2.6
    let w = 0.23
    let xe = x0 + 48 * w
    line((3.5, 0.8), (x0, -1.2), stroke: (dash: "dotted", thickness: 0.4pt))
    line((5.3, 0.8), (xe, -1.2), stroke: (dash: "dotted", thickness: 0.4pt))
    for i in range(48) {
      rect((x0 + i * w, -1.6), (x0 + (i + 1) * w, -1.2),
           fill: if i == 19 { luma(205) } else { white }, stroke: 0.3pt)
    }
    line((x0 + 24 * w, -1.67), (x0 + 24 * w, -1.13), stroke: 0.9pt)
    for (k, lb) in ((0, [12 even]), (12, [12 odd]),
                    (24, [12 even]), (36, [12 odd])) {
      content((x0 + (k + 6) * w, -1.9), text(size: tn, lb))
    }
    content((x0 + 12 * w, -2.25),
            text(size: tn)[corner arrangement of even rank])
    content((x0 + 36 * w, -2.25),
            text(size: tn)[corner arrangement of odd rank])
  }),
  caption: [The map, from the outside in. A page for each arrangement of the
  corners, a group in the page for each pair of outer-edge arrangements and a
  bit in the group for each arrangement of the 4 middle edges, the 12
  even ones low and the 12 odd ones high. One word holds the same group on
  the 2 pages of a pair.],
) <maplayout>

== A level and the prepass

A map is *sound at $d$* when every bit set to 1 is a position within $d$
moves of solved. The run starts from the empty map, with no bit set. It
is sound at 0. Level $d$ turns a map sound at $d-1$ into a map sound at
$d$. A level does 2 things, and they divide the words of length $d$
between them.

- The *prepass* applies each of the 10 moves of $H$ to the whole map at
  once. It covers every word whose last move is in $H$, and that is nearly
  all of them.
- The *search* then looks for the words of length $d$ whose last move is
  not in $H$.

The prepass is what makes a whole coset affordable. It is the one part of
the computation that has no counterpart in the lower bounds.

Applying a move of $H$ to a position of the coset does 3 separate things to
the 3 numbers that name it. The corner arrangement goes to another corner
arrangement, so a page goes to a page. The outer-edge pair goes to another
pair, so a group goes to a group. The middle arrangement goes to another
middle arrangement, so the 24 bits of the group are rearranged among
themselves. This rearrangement depends only on the move and the group. It
is a table lookup and a shuffle of one machine word.

So the prepass never takes a position apart. It never builds a cube, never
ranks one, never looks a position up. For each of the 10 moves it reads
the whole map and writes the whole map. The 10 passes over 3.25 GB cover
every word of this length that ends in a move of $H$, and there are
billions of those.

#src("RowMap.v") has the prepass and the proof that it keeps the map sound.
#src("RowLvl.v") has it again, written so that a page's chunk is fetched
once and put back once instead of once a word. It proves the two are the
same function, so nothing about the cube is proved twice.

== Refining the search

The search is the enumeration of @choosingH. It is a depth-first walk from
$x^(-1)$. At each node the table gives the distance to $H$. A branch
where the moves left are fewer than this distance is dropped. When a word
has its full length and its position is in $H$, the bit of this position
is set. This is the leaf, 2 lines of #src("RowSrch.v"):

```coq
else if csolved c
     then let: (pg, gr, bt) := plc (tomemb x) in mmark m pg gr bt
     else m
```

The membership test is made on the position, not on the table. The table
is only checked to be never too large. A table of zeros passes this
check. With it, every position would look like a member. So the theorem
must not depend on the table for membership.

The table entry also records which moves lower the distance and which
keep it (#src("RowMask.v")). So a node tries 3 or 4 moves instead of 18.

The search is refined in 3 ways, depending on the level.

- *Levels 1 to 13.* The search is the one above. It finds every word of
  length $d$, so the prepass is not needed and not run.
- *Levels 14 to 16.* The prepass covers the words whose last move is in
  $H$. So the search only needs the others. Near the end of a word, it
  only tries moves that strictly lower the distance. Near the end means
  that the moves left and the distance add up to less than 5. The last
  move is the extreme case: it must go from distance 1 to 0, so it is
  never a move of $H$. Level 16 also stops early, once the map holds
  167 million bits plus a third of what its prepass left.
- *Levels 17 to 20.* There is no search, only the prepass.

The cuts of levels 14 to 16 start when the map holds more than
6 million bits. On this coset this is level 14. All these numbers are
Rokicki's.

These cuts can lose words. A word can waste a move early and still end
in $H$. This is allowed. In the earlier sections, a cut that lost a word
would have lost the proof. Here nothing is proved about what the search
covers. What is proved is that every bit set is correct. A lost word
only leaves a bit at 0, and then the final check fails. So the cuts
need no argument.

== The members left over

Stopping the search at level 16, and stopping level 16 early, leaves
members the run never reaches. When the 2 runs ended, 32 bits of the
406 425 600 words were still clear. They are simply the members that no
word the cut search kept, followed by moves of $H$, happened to reach.
Searching deeper would leave fewer and cost hours; each one left over costs a
line.

So we give each of the 32 a word of 20 moves by hand, in
#src("RowWits.v"). Our prototype gave 28 of them, and the last
4 were found one at a time. None of that is believed. #src("RowWitsChk.v")
applies each of the 32 words to its member
and asks for the solved cube. If the producer had made a mistake, or given a
word of 21 moves, or named the wrong member, the check would fail;
it cannot make the theorem false. The replay is also the only thing in the
development that tests the 2 ideas of which facelet is which -- the
prototype's, which found the words, and Rocq's, which builds the member --
against each other.

The 32 are marked into the map at the very end, by #src("RowMark.v"),
and not at the start. In a map sound at $d$, every bit set is within
$d$. A witness is within 20, so seeding one before the run would make level
one mark its neighbours as within one, and they are not. Marking at the end is
sound because the map is already sound at 20 when the marks go in.

== The run, and its one boolean

In #src("RowSrchN.v") the run is 10 lines. It carries the map, the map it
reads while it writes and the number of bits set so far. This number decides
whether the cuts of levels 14 to 16 are on.

```coq
Fixpoint runskn (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m1 := prep m dst in
      let mn := slvlskn true d.+1 m1 (mcount m1) in
      runskn n1 d.+1 mn.2 mn.1 m
    else
      let mn := slvlskn false d.+1 m n0 in
      runskn n1 d.+1 mn.2 mn.1 dst
  else m.
```

With the cuts on, a level is the prepass `prep`, then the search
`slvlskn`. With the cuts off, it is the search alone. The search adds one
to the count for each bit it sets. Counting the bits of the whole map,
`mcount`, is done only after a prepass, which reads the whole map anyway.

Everything above is one boolean. #src("RowFoldCubDef.v") builds the map, runs
the 20 levels, marks the 32 and asks whether every bit is set:

```coq
Definition rowfulliO : bool := mfullf ffuli ycwitsoiO.

Lemma rowfulliOT : rowfulliO = true.
Proof. Time native_cast_no_check (erefl true). Time Qed.
```

That `Qed` is the 50 minutes. The file that holds it, #src("RowFoldCubBool.v"),
is one `Require` and one `Lemma`: a file that runs loads no proof, and a file
that proves runs nothing. Everything else -- that the prepass keeps the map
sound, that the search marks only members, that a full map is the theorem -- is
proved beside it, of a map and a run the proof never evaluates.

== Folding the map

The map can be made smaller, and we made it smaller to see what its size does
to the run. Both maps were searched, the folded one and the unfolded one, and
the 2 runs are compared at the end of the section.

The map is 40 320 pages, one for each arrangement of the corners.

The fold works because of the position we chose. Of the 48 symmetries of
the cube, 16 keep the top and bottom faces in place. Each of them sends the 10
moves to the 10 moves, so it maps $H$ to itself, and each leaves the superflip
unchanged, so it maps the superflip's coset to itself. A member and its image
under such a symmetry need the same number of moves, so 2 pages related by a
symmetry hold the same answer. One page of each family is then enough: 2 768 of
the 40 320, a factor of 14.6. A level of the run is one pass over the map, so
there is 14.6 times less of it to walk. The price is undoing a symmetry whenever
a kept page is read.

The kept pages go in pairs of their own, and a pair shares one word as it does
on the unfolded side: 1 496 words in place of 2 768. There are 224
pages that are their own partner and use half a word.

The fold has to be proved as well as written. A symmetry sends a member of the
coset to a member of the coset. Undoing it gives back the position the page
stood for. A map sound after one level is sound after the next. That is the
largest single part of the coset's proof.

== The reused and the new

We reuse nearly everything. The abstract search and its contract come over
unchanged, and so do the cube, the permutations, the machine-integer tools, the
phase one table and its generator. Each of the new tables has a check of its
own, in a file of its own, so that a failure names the table that failed.

There are 5 new things, and only one of them is a search.

- The rank and the sign of a permutation. Rocq's library has both, but for
  permutations that do not compute, so we need their effective version on
  machine integers.
- The link between a position and its 3 ranks. The map's bits are triples
  of numbers, so what the run proves is a statement about triples. To read it
  as a statement about the cube we have to turn a triple back into the position
  it stands for. The other way we already had.
- The pass that steps a whole map one move at a time.
- The fold by the 16 symmetries.
- Words given by hand for the members the run does not reach.

== The files and the cost

The coset adds 86 hand-written files and 23 800 lines, besides the
generated tables. The coset and its members are #src("Row.v"),
#src("RowMemb.v") and #src("RowInst.v"); the ranking and the moves
#src("Lehmer.v") with the `RowPart`, `RowMove` and `RowTab` groups; the map and
the search #src("RowMap.v"), #src("RowRun.v"), #src("RowSrch.v") and
#src("RowFinal.v"); the fold the `RowFold` group; and the 2 runs the `RowCub`
and `RowFoldCub` groups, ending in #src("RowCubDone.v") and
#src("RowFoldCubDone.v"). #src("README.md") lists every one of them with what
it does.

The search ran twice, over the folded map and over the unfolded one, with the
same search in both, and both times it filled the map.

#tbl(([the run], [wall clock], [processor time]),
  ([over the folded map], [50 min], [50 min]),
  ([over the unfolded map], [2 h 32], [2 h 31]),
)

The fold is worth 3 times on the wall clock and 3 times on processor time.
The map is 13 times smaller, so the run does not follow the size of the map.
The map sets the memory. The unfolded map is 3.25 GB against 248 MB, and a
level reads one map while it writes the other.

The phase one table is 2.9 GB of Rocq source and 4.5 GB once checked, 8 h 48 of
processor time. It is generated once and shared with the lower-bound work.

The statement has no hypothesis left.

```coq
Theorem real_superflip_row_fold_runO h :
  h \in H -> superflip^-1 * h \in ball Sset 20.
```

`H` is the subgroup above, and the superflip is its own inverse, so every
position of the superflip's coset is within 20 moves.

= Conclusion

We prove 2 lower bounds. No position of the cube is solved in 19 face turns,
and none in 25 quarter turns. In each case one position is the witness, the
superflip for the first and the four-spot with the superflip on it for the
second. In each case the proof is a search that comes back empty over a table of
estimated distances.

We do not prove that 20 and 26 always suffice. The upper half is a different
computation. It is not one search that finds nothing, but 2 billion searches
that must each find everything. We did one of the 2 billion, and the section
above gives its cost.

The three share a trunk. The cube itself, as permutations of the 48
facelets, with the 18 moves and the group they generate. Balls, the
positions within $d$ moves. The abstract search, whose
contract is that a false answer is a proof. The rule that any summary of a
position, together with any table that passes one check, gives an estimate that
is never too big. And the tables themselves, held as machine integers in arrays
rather than as lists of unary numbers.

What each of the three needed of its own:

- *The 20 face turns.* The phase one summary, which is the edge flips and
  the slice, its table and the certificate that checks the table. The same
  search seen from 3 angles, and 30 pieces run side by side.
- *The 26 quarter turns.* The cut to 6 prefixes, which is the one
  piece of the development argued by hand rather than computed, and the parity
  argument that turns 25 into 24. A second and much larger summary, 29 billion
  values, with a table of its own and a check of its own.
- *One coset.* A coset held as a map of bits rather than as a tree of
  positions. That needs 5 new pieces. The rank and the sign of a
  permutation on machine integers. The link between a position and its 3
  ranks. A pass that steps a whole map one move at a time. The fold by the
  16 symmetries. And words given by hand for the members the run does
  not reach.

The same search written in OCaml is about 4.5 times faster than the
one Rocq runs. We ran both at radius 19 on the reference machine. The
OCaml program visits 137 607 893 106 positions in 19.2 processor-hours, which is
0.50 microseconds a position. Rocq takes 89.5 processor-hours over the same
tree, which is 2.34. A factor of *4.7*.

We do not assume that the two walk the same tree. We divide each of the
30 Rocq pieces by the positions its OCaml counterpart visited. The result
is between 1.85 and 2.86 microseconds, over pieces that differ in size by a
factor of 2.8. So the run takes a night because the tree holds 138
billion nodes, not because the prover is slow: in OCaml the same tree still
costs 19 processor-hours.

The whole development, counted in hand-written Rocq and leaving out the
generated tables, is 36 300 lines. Each line of the table counts what that piece
adds to the ones above it.

#tbl(([], [files], [lines]),
  ([the superflip, for the 20 face turns], [44], [12 600]),
  ([the four-spot, for the 26 quarter turns], [19], [6 100]),
  ([one coset of the upper bound], [70], [17 600]),
  ([*in all*], [*133*], [*36 300*]),
)

This development was written with the help of Claude, Anthropic's coding
assistant.

The sources are at
#link("https://github.com/thery/DoubleCover/tree/main/code/Rubik")[`github.com/thery/DoubleCover/code/Rubik`],
with the note, its figures and Reid's transcribed post beside them.


#pagebreak(weak: true)

#bibliography("rubik20-note.bib", title: [References], style: "springer-mathphys")
