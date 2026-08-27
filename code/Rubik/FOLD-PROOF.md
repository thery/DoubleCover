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

One thing: the folded level. `flevpg` copies the source page and then ors
in what each of the ten moves gathers, and nothing yet says that a bit it
writes is a member one move of H away from a member the source had.

The shape is `RowRun.prepass_sound`, with two differences.

1. The level writes into a page array, not into the map. `fset_setp` is
   the bridge, so the induction runs over `RowMap.ifold_indi` with the
   invariant "the map with this chunk put back is sound".

2. The source is read through a renaming. So the source member is not the
   one the plain level would read but its image under one of the sixteen,
   and `sym16_row` is what says that costs nothing.

### The tables it needs

Two facts about the generated tables, checked and not proved, in the shape
`RowRun` already uses for `grpmvP` and `prep_move`:

- `fsrc` says, for a kept page and a move, which kept page the move gathers
  from and through which renaming. What has to hold is that the member at
  the destination is that move played on the renamed source member.
- `fsgr`, `fslo`, `fshi`, `fsbt` are the renaming acting on a group and on
  the bits. What has to hold is that a bit they set came from a bit of the
  word they were given, and that the member relation is the renaming.

`fkeepi` (in `RowFoldTab.v`, from `fkeep_data`) gives a page for each kept
number, which is what makes the source side of that statement sayable.

## Why it is worth it

Measured on roquableu at depth thirteen, with the twenty cubies carried:
the search is 141.7 s against a floor of 68.9 s with no position at all,
and the folded map is fifteen times smaller than the plain one -- 0.45 GB
against 6.5.
