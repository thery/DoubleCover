# Proving the folded row

What is proved, and what is left, for the row on the folded map.

## Why the map can be folded

Sixteen renamings of the faces keep the U/D axis. `Sym16.v` certifies that
each of them turns a move into a move, and that the sixteen are a group.
`Sym16Row.v` adds what the row needs:

- `sym16_sf` — each of the sixteen fixes the superflip.
- `sym16_ball` — each maps the ball of radius n to itself.
- `sym16_row` — so if a position is within twenty of the superflip, so is
  its image, by the same number of moves.

One member of each orbit is therefore enough to keep, which is the fold.

## What is proved of the folded map

In `RowFoldOk.v`:

- `mfullf_ftest` — a full folded map answers every member.
- `fget_fset` — one write is seen at one place.
- `ftest_fmark` — a bit a folded mark sets is its own or was there
  already, and "its own" means the two members fold to the same page,
  group and bit.
- `soundatf_fmark` — a folded mark keeps a sound map sound, as long as
  members that fold together stand or fall together. That is `sym16_row`.
- `set_setA`, `fset_setp` — the folded level fills a page array and puts
  the chunk back; these turn that into the map write it stands for.
- `foldf_all` — full and sound puts every member within the depth.

## What is left

**The folded level's shape is proved**, in `RowFoldLvl.v`, on nothing but the
int63 and PArray primitives:

    flevel_sound : sdf P src -> sdf Q dst -> sdf Q (flevel ... src dst)

The two differences from `RowRun.prepass_sound` are both discharged.

1. The level writes into a page array, not into the map. `ffor_setp` is the
   bridge, and the induction runs over `RowMap.ifold_indi` with the
   invariant "the map with this chunk put back is sound". `set_getA` is what
   says a chunk put back unchanged leaves the map alone, which is how the
   carry starts; and the level's own length invariant is carried beside
   soundness so that every kept page's chunk stays in range.
2. Each group is written twice, once for each half of its word, and each
   write is under a test -- a half that is all noughts is not written at
   all. `lvstep_if` is that write with its test.

**And so is the run**, `frunx_sound`: the levels one after another at growing
depths, `soundatf (Pd d) m -> soundatf (Pd d) dst -> soundatf (Pd (d + n))`.
The search is not redone there -- a level is the gather and then, at the
depths it is asked for, a search that marks; all the run needs of it is that
whatever it does to the map it leaves it sound at the depth it was called at
and as long as it found it. That is one hypothesis, `extP`, and the mark
inside it is `RowFoldOk.soundatf_fmark`.

### THE TWO WRITE OBLIGATIONS ARE PROVED (2026-08-29)

`RowFoldWrite.QloC` and `RowFoldWrite.QhiC` discharge `Qlo_st` and `Qhi_st`
on the real tables, admit-free. So the folded level and the folded run stand
on nothing left over but `ext` -- the search leg -- and the instance.

THE GATHER IS THE PLAIN WRITE ON THE RENAMED SOURCE, and every leg of that
is now a fact:

- **the page leg**, `RowFoldSrc.gathC`: a sweep NOT over sixteen renamings by
  forty thousand pages but over the 27 680 pairs the level actually gathers,
  a kept page and one of the ten moves. At each pair: the renaming is one of
  the sixteen, the source is a kept page, the renamed page is a page, the
  renaming keeps its parity, the parity `fsrc` carries is the source page's,
  the move sends the renamed page to the page being filled, and the renaming
  conjugates the eight corner places. 17.7 s.
- **the group leg**: nothing. `mgr[fsgr[glo+g]*nhi+k]` IS
  `grmv mgr k (sgrmv fsgr u pty g)`, the same term, so it needs no lemma.
- **the bit leg**, `RowFoldGath.cbtC` and `caddXC`: the word the level ors in
  is `cloX`/`chiX` -- the half where `msw` puts it -- it is additive over the
  twelve bits, and one bit lands at `btmvt k (fsbt u i)`. So `cloX_bit` says
  a written bit came from a source bit AND names which. Under 2 s.
- **the member under the renaming**, `RowFoldSrc.gather_conj_pt`: word for
  word `fold_conj_pt` at the gather's renaming. `upart_conj` and
  `mpart_conj` were already stated at any of the sixteen and are reused;
  only the corner leg needed the new sweep.
- **the member under the move**: `RowMembChk.memb2tab_moveC`, unchanged.
- **the source bit is a member**, `RowFoldGath.keep_ftest`: the gather reads
  at a KEPT page, and a kept page is its own representative with a renaming
  that leaves groups and bits alone, so there is no renaming to undo.
- **the slot**, `RowFoldMem.fslot_inj`, and `fold_conjC` to undo the last
  renaming, at any depth (`Sym16Row` had it at twenty only).

**What is left of the fold:** `ext`/`extP`/`extlen` -- the search leg, whose
mark is `RowFoldOk.soundatf_fmark` -- and a folded `RowInst`/`RowFinal`, and
then the run.

### What the two write obligations needed

They are the last mathematics. A word gathered by move `k` into the page
being filled must be one move of H out from a member the source had, and the
source is read THROUGH A RENAMING -- so the step is a renaming AND a move,
where `fold_conj` was a renaming alone.

The plan is the same three-part cut, with one lemma added at each part:
`part_conj` for the renaming (proved) and `RowMemb.part_move` for the move
(proved), composed. And the page leg is ALREADY DONE: `RowFoldSym.fsrcC` is
exactly it -- rename the kept source page and the move sends the answer to
the page being filled.

What is left is the group leg and the bit leg, in the shape `uconjC` and
`mconjC` have but with the move table composed in, and then the assembly the
way `fold_conj_pt` assembles its three.

### THE GATHER IS THE PLAIN WRITE ON THE RENAMED SOURCE

Read off the level: the destination group is `mgr[fsgr[glo+g]*nhi+k]`, and
`fsgr[glo+g]` IS the renamed group while `mgr[..*nhi+k]` is the move on it.
The word is `mlo[k][fslo[u][lo]]` -- the renaming on the half, then the move.
And the page is `fsrcC`. So the folded write is LITERALLY the plain write
applied to the renamed source; the tables compose that way by construction.

That is worth a great deal, because it means `Qlo_st`/`Qhi_st` need no new
member-level gather. They reduce to three things that already exist:

- `clo_bit`/`chi_bit` (`RowFoldGath.v`) -- a bit of the moved half came from
  a bit of the half;
- `fold_conj_memb` -- the renaming costs nothing, via `sym16_ball`;
- `RowInst.prep_move` -- the move costs one step. It is usable concretely:
  `srcokC` and `halfokC` are proved on the real tables in `RowTab.v`.

What is left is the assembly of those three, and the ranges around it.

**AND `RowInst.grpmvP` CANNOT BE REUSED FOR THE BITS.** The plain level
sends the two halves of a word to ONE destination word, swapped or not, and
`grpmvP` is about that one word. The folded level sends them to TWO
DIFFERENT GROUPS -- the renaming carries the low half of a pair to one group
and the high half to another, which is the whole reason there are two group
tables. Measured:

    twoG = false

So the bits need their own lemma, one per half: a bit of `mlo[k][fslo[u][lo]]`
came from a bit of `lo`. That is a smaller statement than `grpmvP` -- one
half, not two -- but it is a new one, and it is the last piece of bit-level
work the fold needs.

**What is left is the two write obligations**, `Qlo_st` and `Qhi_st`, stated in
`RowFoldLvl.v` in the shape `RowRun.v` uses for `grpmvP` and `prep_move`: a
member that reads a bit of the word gathered for the low (resp. high) half
is one move of H out from a member the source had. The source is read
through a renaming, so the source member is not the one the plain level
would read but its image under one of the sixteen, and `Sym16Row.sym16_row`
is what says that costs nothing. All six tables those two statements speak
about are now checked.

**And `Porb` -- members that fold together stand or fall together -- which
`RowFoldOk` assumes and nobody had discharged.** It comes in two halves and
the first is done, in `RowFoldMem.v`:

- `fslot_inj`: a chunk and an offset name one kept page and one group. The
  offset a page starts at plus a group is exactly `RowMap`'s `grpof` of the
  page inside the chunk, so `grpof_inj` settles it, and `int_add_mod` puts
  the page number back together from its quotient and its remainder --
  going through `to_nat` there does not come back.
- `forb_same`: so `Porb`'s three premises name one kept page, one group and
  one bit.

- `sym16_ballV`: undoing one of the sixteen also stays inside the ball. Two
  members that fold together are each other's image under *two* of them, so
  one has to be undone -- and the sixteen are closed under inverse, so
  undoing one is applying one.
- `fold_Porb`: **`Porb` itself**, on nothing but the primitives.

**And `fold_conj` is proved too**, in `RowFoldConj.v` -- `fold_conj_memb`.
So `RowFoldOk`'s one assumption stands on nothing left over.
That is where the six sweeps of `RowFoldSym` are finally spent, and it is
exactly the shape `RowInst` leaves `memb2tab_move` in -- the algorithm
proved, what the tables mean left to the instance.

### And what `fold_conj` will cost: NOT `part`, and NOT `partt` either

`RowMemb.memb2tab_move` is the plain version of this, and it works by cutting
the member into three parts -- corners, outer edges, middle -- showing the
move acts on each, and putting them back together. The fold wants the same
cut with a renaming in place of the move, and there are two obstacles.

`RowMemb.part_move` asks `lslot`: the move leaves a facelet in the SAME slot
of its place. A renaming does not. `RowCub.partt` is `part` with that
relaxed to a TURN -- slot `s` goes to `(s + tw p) %% nsl`, round the place --
which is what a corner twist and an edge flip do.

**That is still not enough, and it is measured, not guessed.** Asking of all
sixteen renamings and all eight corner places whether the slot map is a turn:

    rot_ok = false

and at corner place 0 the sixteen split evenly -- eight give the slot map
`[0;1;2]` and eight give `[0;2;1]`. A transposition is not a rotation of
three, so eight of the sixteen REVERSE a corner's facelets and no `tw` can
say it.

**But the slot map does not depend on the place**, and that is measured too:

    same_across = true

Renaming 1 gives the slot map `[0;2;1]` at every one of the eight corner
places, and so it goes for all sixteen. So the variant `fold_conj` needs is
not an arbitrary slot permutation for each place -- it is ONE slot
permutation for the whole renaming, applied uniformly:

    parts lay nsl inL plc slt u sw :=
      mkseq (fun f => if inL f then lay[u (plc f) * nsl + sw (slt f)] else f) 48

which is `part` with a single extra argument, much closer to it than `partt`
is. And because that `sw` is global, in a conjugation the one from the
renaming and the one from its inverse cancel: the conjugate of a
slot-preserving part is slot-preserving again, which is what makes the three
parts reassemble the way `memb2tab_move` reassembles them.

**And that lemma is now proved**, in `RowFoldPart.v`:

    part_conj : ... -> comp_tab (part v) (restr inL t)
                     = comp_tab (restr inL t) (part u)

on `RowMemb`'s own `part`, twice -- no new kind of part was needed after
all, because the one slot map appears on both sides of the conjugation and
cancels. `lslots` is `lslot` with that one map added.

The condition it asks of the places is exactly what the fold tables are
checked to say: `nth (lperm t) (v p) = u (nth (lperm t) p)`, the renamed
rank names the conjugated permutation.

**And all three applications are now proved**, in `RowFoldConj.v`:
`cpart_conj`, `upart_conj`, `mpart_conj`. Each rests on a sweep of the fold's
own tables:

| | what is walked | |
|---|---|---|
| `pgconjC` | 40 320 pages | 5.5 s |
| `uconjC` | 16 x 2 x 20 160 groups | 81 s |
| `mconjC` | 16 x 24 bits | instant |

**THE SWEEPS ARE NOT OVER MEMBERS.** The outer part depends on a member only
through its group and its parity, and the middle only through its bit, so
each walk is the size of the table it is about and not of the row.

**And the parity does not move.** A renaming conjugates, so it keeps the
parity of a permutation, which is why the same `pty` indexes both sides of
`uconjC`. That is what the sweep says; it was not assumed. The parity the
fold computes -- `fpar w` xor the bit's half -- is `unplace`'s own parity,
because `fpgC` checks `fpar w = par8i pg` and the low half of a word is the
even middle permutations.

What is left is the reassembly of the three into `fold_conj`, which is what
`memb2tab_move` already does for its three.

And then a folded `RowInst`/`RowFinal`, so that `RowFoldCubRun.v` has a
theorem to print the assumptions of.

### The tables it needs

Two kinds, and the first is done.

**In range** — `RowFoldChkTab.v`, six sweeps, all passing: a page folds to
one of the 2768 kept pages, so does each move's source page, a group folds
to a group, a bit to one of the twenty four, each half of a word to a half.

**The members** — done, in `RowFoldSym.v`, all four sweeps passing (307 s,
1.1 GB): `fsgr` by unrank, rename, rank again and compare, 16 x 2 x 20160 of
them; `fsbt` the same on the middle four, 16 x 24; and `fslo`, `fshi` by
moving the twelve bits of a half one at a time, which is what `fsbt` already
says, 16 x 4096 each.

**EVERY INDEX IN THAT FILE IS AN int63.** `of_nat` walks its argument, so
naming a slot of the 645 120 entry group table in `nat` costs 645 120 steps
to build the number, once for every group of every renaming -- about 10^11
steps, which does not finish. Counted in int63 the same index is two
multiplications and an addition, and the sweep is five minutes.

**AND THE SIXTEEN ARE NUMBERED TWICE.** `Sym16.v` orders the renamings one
way and the fold tables, which come from the prototype, order them another.
`RowFoldSym.fren2sym` is the map between the two:

| fold `u` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `sym16ts` | 15 | 6 | 2 | 10 | 12 | 11 | 1 | 5 | 7 | 8 | 0 | 3 | 13 | 4 | 9 | 14 |

It is not assumed. The sweep asks that renaming `u` of the tables IS
`sym16ts (fren2sym u)` acting on the ranks, so a wrong entry makes the sweep
fail rather than pass. Read off the tables: the twenty four bits leave two
candidates for each `u` and cannot tell `u` from `u + 8`, because the two
differ only away from the middle four; the outer eight pin it, and they pin
it in one direction only -- the conjugation is `s` on the outside and `s`
inverse on the inside, and the other way round fails on four of the sixteen.

The member fact then follows the way `RowMemb.memb2tab_move` follows from
its own checks.

**The pages** — done too, in the same file. A page is a rank of the eight
corners, so the same conjugation says what a renaming does to it.

- `fpgC`: a page folds to a kept page through the renaming it names, and the
  word carries that page's own parity. 40320 of them.
- `fsrcC`: for a kept page and a move, rename the kept page the word names
  and the move sends the answer to the page being filled -- which is what
  gathering means. The parity carried here is the SOURCE page's, not the
  filled page's. 2768 x 10 of them.

So all six fold tables are checked. The whole file is 346 s.

## Why it is worth it

Measured on roquableu at depth thirteen, with the twenty cubies carried:
the search is 141.7 s against a floor of 68.9 s with no position at all,
and the folded map is fifteen times smaller than the plain one -- 0.45 GB
against 6.5.
