# Slow lines in the development

Every sentence taking **>= 5 s**, from `coqc -time` on all hand written files,
scanned 2026-08-04. It skipped the generated families (`FsData.v`, `Fs_??.v`,
`Far_??.v`) whose cost IS the computation. `Far_??.v` and `Farmain.v` have
since been deleted with the old five view search, so their rows are gone from
the list below; everything else still exists.

Normal sentences are well under 1 s, so everything below is worth a look.

## 1. Real proof hotspots -- these are the actionable ones

| secs | file | sentence |
|---|---|---|
| **27.8** | `Rubik333.v` | `by repeat (apply/andP; spl...)` |
| **19.4** | `Diameter.v` | `by do ?[by apply: face...]` |
| **14.3** | `Far.v` | `by move=> _ ca; rewrite /Dtid ...`  (= `DtidE2`) |
| **8.0** | `Far.v` | `rewrite /prefixi !e //.`  (inside `prefixi_cub`) |
| **7.8** | `Phase1.v` | `by rewrite !permM (eqP (cm _)) (eqP (cg _)).`  (= `cubcPM`) |

Notes:

- `Rubik333.v` at 27.8 s is the single worst line in the development. `repeat
  (apply/andP; split)` on a large conjunction backtracks; an explicit
  `rewrite !andbA` / `do N!` with a fixed count is usually far cheaper.
- `Diameter.v` at 19.4 s has the same shape: `do ?[...]` with an open count.
- **`DtidE2` in `Far.v` at 14.3 s is mine and is embarrassing.** It is
  `by move=> _ ca; rewrite /Dtid /Dti ca` -- unfolding `Dtid` drags in `Dfsd`,
  hence `fstab`, hence the 2 097 152 word table. Making `fstab` or `Dfsd`
  opaque for that one proof should take it to milliseconds.
- `prefixi_cub`'s `rewrite /prefixi !e //` at 8 s is the same disease: `//`
  after unfolding `prefixi` lets `done` wander into the table.
- **`cubcPM` in `Phase1.v` at 7.8 s (2026-08-03) is a three-token proof** --
  `by rewrite !permM (eqP (cm _)) (eqP (cg _))` on `cubcP (g * m)`, where
  `cubcP g := [forall f, ccyc (g f) == g (ccyc f)]`. Nothing here touches a
  table, so the suspects are the two bang-rewrites and the `_` in `cm _` /
  `cg _`, i.e. the "exact counts, not bangs" and "arguments explicit" rules.
  `2!permM` and the point supplied explicitly is the first thing to try.
  NOT fixed -- flagged for an offline pass.

## 2. The import tax -- systematic, ~7-9 s PER FILE

Every remaining entry is the same sentence:

    From mathcomp Require Import all_ssreflect all_fingroup.

at **7-9 s in each of ~22 files**, so roughly **3 minutes of every full build**
is mathcomp loading, before any proof runs. coqc already warns:

    Warning: Library File mathcomp.ssreflect.all_ssreflect is deprecated
    since mathcomp 2.5.0. Use 'all_boot' and/or 'all_order' instead.

Importing only what each file needs (`all_boot`, `all_order`, or the specific
modules) is the obvious win, and it is mechanical.

## 3. Full list

- **8.046 s** `Far.v` -- Chars 18162 - 18185 [rewrite~/prefixi~!e~//.] 8.046 secs (7.967u,0.01s)
- **7.631 s** `Search.v` -- Chars 1945 - 2001 [From~mathcomp~Require~Import~a...] 7.631 secs (7.086u,0.464s)
- **7.605 s** `Sym.v` -- Chars 2269 - 2325 [From~mathcomp~Require~Import~a...] 7.605 secs (7.116u,0.421s)
- **7.57 s** `Root.v` -- Chars 1783 - 1839 [From~mathcomp~Require~Import~a...] 7.57 secs (7.053u,0.437s)
- **7.48 s** `Searchr.v` -- Chars 1217 - 1273 [From~mathcomp~Require~Import~a...] 7.48 secs (7.001u,0.407s)
- **7.423 s** `Fsmain.v` -- Chars 1243 - 1299 [From~mathcomp~Require~Import~a...] 7.423 secs (6.801u,0.538s)
- **7.141 s** `Tsearch.v` -- Chars 1135 - 1191 [From~mathcomp~Require~Import~a...] 7.141 secs (6.66u,0.417s)
- **7.078 s** `Rubik333.v` -- Chars 1783 - 1839 [From~mathcomp~Require~Import~a...] 7.078 secs (6.614u,0.392s)
- **6.964 s** `Table.v` -- Chars 1945 - 2001 [From~mathcomp~Require~Import~a...] 6.964 secs (6.521u,0.382s)
- **6.94 s** `Coord.v` -- Chars 2998 - 3054 [From~mathcomp~Require~Import~a...] 6.94 secs (6.482u,0.394s)
- **6.838 s** `Ball.v` -- Chars 1378 - 1434 [From~mathcomp~Require~Import~a...] 6.838 secs (6.39u,0.388s)
- **6.803 s** `Redun.v` -- Chars 979 - 1035 [From~mathcomp~Require~Import~a...] 6.803 secs (6.333u,0.4s)
- **6.632 s** `Diameter.v` -- Chars 1621 - 1677 [From~mathcomp~Require~Import~a...] 6.632 secs (6.176u,0.398s)
- **6.61 s** `Cyc.v` -- Chars 811 - 867 [From~mathcomp~Require~Import~a...] 6.61 secs (6.151u,0.407s)
