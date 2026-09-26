# rubik_row_rocq.ml: the Rocq row run, written out in OCaml

A faithful translation of the two runs Rocq times at depth 13, so the time
can be taken apart in OCaml:

| run | Rocq | bench | Rocq's value at 13 |
|---|---|---|---|
| plain | `RowCubDefD.rowmappiD` then `mcount` | `RowBenchCountN.v` | 14 731 320, 110.3 s (roquableu) |
| folded | `RowFoldCubDefD.rowmapiD` then `fcount48 ffuli forbi fpopi` | `RowBenchCountF.v` | not yet measured |

## The rules of the translation

- A Rocq `int` (Uint63) is an OCaml `int`. Every value in the run is below
  2^62, so signed and unsigned compares agree, with one exception:
  `RowSrchN.nbig` is 2^62, which Rocq reads unsigned and OCaml would read as
  `min_int`, so it is `max_int` here.
- A `nat` is the unary type `nat = O | S of nat`. Every `ifold` counts one
  down, and `leq`, `eqn`, `subn` are mathcomp's, recursive.
- A `PArray` is Rocq's own `kernel/parray.ml` (9.1.1), copied in.
- A pair is a pair and a triple is a pair of a pair. `~~`, `||`, `&&` are
  functions, so both arguments are evaluated.
- A section's variables are arguments: the search calls `cstep`, `xstep`,
  `okmv`, `tomemb`, `csolved` through closures.
- The GC is set as `rocq` sets its own (`sysinit/coqinit.ml`): a 32 Mword
  minor heap, space overhead 120.

## Where each function comes from

| OCaml | Rocq |
|---|---|
| `Parray` | `kernel/parray.ml`, Rocq 9.1.1 |
| `ifold` | `RowMap.ifold` |
| `subn`, `eqn`, `leq` | mathcomp `subn` (`Nat.sub`), `eqn`, `leq` |
| `of_nat` | `Uint63.of_nat` |
| `gget`, `gor`, `mkempty`, `grpof`, `bitof` | `RowMap` |
| `pgmv`, `grmv`, `lomv`, `himv`, `grpmv24`, `grpmv` | `RowMap` |
| `pgbase`, `pgchk`, `pgoff`, `pgfits`, `prepmv0S`, `prepmvD`, `prepassD` | `RowLvl` |
| `p1getm` | `Phase1.p1getm` |
| `foldi`, `get20`, `get4` | `Fold` |
| `dfoldm`, `mdist`, `mmask` | `RowMask` |
| `sp1g` | `RowSrch.sp1g` (= `RowFoldSrch.fp1g`) |
| `place`, `place24`, `mcp`, `mud`, `mmp` | `Row` |
| `popof`, `popi`, `mcount`, `mmarkn`, `sslack`, `srchski` | `RowSrch` |
| `srchskiL` | `RowSrchC.srchskiL` |
| `slvlskni`, `runskni`, `nbig` | `RowSrchN` |
| `mkT`, `factA`, `nthfree`, `cunrank`, `ctab`, `einvT`, `etab`, `enc`, `tp0..3`, `all4`, `dist4`, `sub8`, `tup8`, `cstepx`, `eplace`, `cofy` | `RowCoord` |
| `l8`, `ecub`, `e8rT`, `l4`, `mcub`, `e4rT`, `cmemb` | `RowCoordLeaf` |
| `lbpop`, `lbcq`, `lbeq`, `lbstep`, `lbrank` | `RowLeafFast` |
| `acttwii` | `Phase1.acttwii` |
| `actfsri` | `Farp1.actfsri` |
| `cstep` | `RowInst.cstep` |
| `okmvv` | `RowReal.okmvv` (= `RowFoldCubDef.okmvvd`) |
| `fstep`, `mk_ishmi` | `RowCubDef.fstep`, `ishmi` (= `RowFoldCubDef`'s) |
| `mkemptyf`, `pchk`, `poff`, `ffor`, `fpar`, `fren`, `fhlf`, `fkpt`, `fbit` | `RowFold` |
| `sgrmv`, `sbtmv`, `fmark`, `fmarkn` | `RowFold` |
| `fofs`, `flevmvu`, `flevmv`, `flevpg`, `flevel` | `RowFold` |
| `fcount`, `fcount48` | `RowFold` |
| `frcutii`, `fsslack`, `fsrchki`, `fsrchski` | `RowFoldSrchI` |
| `isrchskL` | `RowFoldSrchIC` |
| `fmarknw` | `RowFoldN` |
| `wleaf`, `iwsrchL`, `wslv`, `wrun` | `RowFoldN` |
| `rowmappiD`, `rowmapiD` in `main` | `RowCubDefD`, `RowFoldCubDefD` |

## Where the data comes from

The same `.v` files Rocq loads, parsed. The tables Rocq builds by a
computation (`ctab`, `etab`, `e8rT`, `e4rT`, `sub8`, `tup8`, `popi`,
`lbpop`, `ishmi`, `cofy yrooti`) are built by the same computation.

| data | file |
|---|---|
| `e8num_data`, `e4bit_data` | `RowTabL.v` |
| `mgr_data`, `msw_data`, `mlo_data`, `mhi_data` | `RowTabP.v` |
| `cpg_data`, `cfl_data` | `RowTabC.v` |
| `twmove_data` | `P1Small.v` |
| `fsm_chunk_00..02` | `P1Fsm.v`, generated (`p1gen 9 small`) |
| `rep_data`, `sym_data`, `twsym_data` | `P1Fold.v`, generated (`p1gen 12 emitfold`) |
| `dnlo_data` .. `flhi_data` | `P1Fdec.v`, generated |
| `p1ftab` | `P1FTable.v` and `P1F_00..33.v`, generated |
| `fpg_data` .. `fpop_data` | `RowTabF48.v` |
| `ymvpi`, `yrooti`, `croot`, `csolvedci` | printed by `../RowTransConsts.v` |

`RowTransConsts.v` has to be compiled by the Rocq that built the `.vo`
files it loads (9.1 here):

    rocq compile -R . Rubik RowTransConsts.v > rowtrans_consts.txt

## Running it

    ocamlfind ocamlopt -package unix -linkpkg -O3 rubik_row_rocq.ml -o rubik_row_rocq
    ulimit -s unlimited
    taskset -c 0 ./rubik_row_rocq fold <code/Rubik> <generated dir> rowtrans_consts.txt 13

Building the tables is not timed. The run and the count are timed apart.
