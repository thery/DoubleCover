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

**What is left is the two write obligations**, `Qlo` and `Qhi`, stated in
`RowFoldLvl.v` in the shape `RowRun.v` uses for `grpmvP` and `prep_move`: a
member that reads a bit of the word gathered for the low (resp. high) half
is one move of H out from a member the source had. The source is read
through a renaming, so the source member is not the one the plain level
would read but its image under one of the sixteen, and `Sym16Row.sym16_row`
is what says that costs nothing. All six tables those two statements speak
about are now checked.

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
