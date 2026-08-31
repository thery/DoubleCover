# The folded row: run, proof, and the bridge between them

## The four files

| file | holds | loads |
|---|---|---|
| `RowFoldCubDef.v` | the map and `rowfull : bool` | tables only, no proof |
| `RowFoldCubBool.v` | `rowfullE : rowfull = true` | `RowFoldCubDef` |
| `RowFoldCubProof.v` | `row_of_run : rowfull = true -> the row` | the whole cube side |
| `RowFoldCubDone.v` | the two together | both |

The run answers one boolean and the theorem reads that boolean, so neither
process carries the other's weight.

## Why the bridge needs lemmas

`RowFoldCubDef` loads no proof file, so it cannot name `RowCubInst`'s and
`RowReal`'s constants.  It copies four bodies under its own names:

    ytomembd   ytomemb tomembi
    okmvvd     okmvv
    ycsolvedd  ycsolved1
    srchd      srch

Left to itself, unification does not *fail* when a name will not match --
it reduces.  Reducing this is the eight hour run again, in the kernel,
which is far slower than native.  So the four are equations, then
`ycwitsoE` says the two maps are equal, then the theorem is applied with
every argument named.  Nothing is left to search for.

## Two traps that cost a day

- **`csolvedi` against `csolvedci`.**  Same number: `csolvedci` is settled
  by `Eval vm_compute` at definition time, `csolvedi` is
  `fsidx (coordfs 1)` and `coordfs` takes a mathcomp permutation.  A search
  asking the node test with `csolvedi` walks the permutation type at every
  node.  Measured: 62 GB and killed, against 11.9 GB flat.
  `RowInst.csolvedciE` relates them.
- **`tomemb` against `tomembi`.**  `tomemb` builds a forty eight cell
  `seq nat` at every recorded answer; `tomembi` is the same member on int63.
  `RowMembi.tomembiE` relates them, given the `tabi_ok` that `pstok` carries.

## Measured

- depth 13, certificate's own map: 759 s, count 14 731 320.
- depth 20: 8 h 13, 11.9 GB flat.
- the certificate's whole Require list loads in 62 s under 5 GB.
- `Print Assumptions` on the corollary names only int63 and PArray primitives.
