# `Alg2.v` — measurements, dead ends, and what each hole needs

`Alg2.v` keeps only short comments. Everything that would otherwise bloat it —
probe counts, refuted statements, retracted proofs, per-hole proof plans — is
here. Sections are referenced from the source as `see alg2-notes.md §N`.

Companion: `lefevre-these-notes.md` (what the algorithm's variables mean,
from Lefèvre's thesis ch. 2).

All probes are in `code/APaul/*.py`. Unless stated otherwise they run over
M ∈ {24,32,45,48,60,64}, all A, all B, every reachable loop state.

## 1. Refuted statements — do not retry

| statement | verdict |
|---|---|
| `inv_complete` | FALSE. `step_p_gt0`/`inv_step` went through it and were reproved. |
| `inv_d` (the old `d` field) | FALSE. Replaced by `invd`: bound + congruence + max. |
| `step_d_ge` | wrong direction |
| `step_pt` without its hypothesis | FALSE |
| `mod_le_dst` with `<= B+M` | needs `<= M` |
| `dstB` as an equation | only true mod `M`; needs no `Pt y <= Pt x` |
| "all distances ≡ `Inf` mod `p`" | FALSE, 4884/22864 |
| `d = Inf (u+v)` in general | FALSE, 314/17608 (all in the `p<q` branch) |
| `d %% p <= Dst y %% p` unguarded | FALSE, 2174/26560 — the `Dst y %/ p <= q %/ p` guard is essential |
| `Inf(new) = Inf(u+v) %% (p %% q)` (`ge` mirror of `inf_new_lt`) | FALSE, 34/1384 |
| `d' = Inf (u'+v')` (`ge` step exact) | FALSE, 314/5216 — the step can undershoot |
| `d' + p' < q` | FALSE, 8611/10669 |
| `W < q` always, in `le_ge_wrap` | FALSE, 2781/5701 — it quantifies over every `m`, not just the first to wrap |
| `ge_wrap_au` | FALSE, 1941/4690 — see §2 |

## 2. The `ge_wrap_au` retraction (PR #121 → #122)

`le_ge_wrap` was proved via `ge_wrap_au`, which is false. Cause: `invx_gap` is
an **existential** and the decomposition is not unique — e.g. M=24, A=13
(`p=2,q=1,u=11,v=2`) has `Dst y = 23` as both `Inf + 11p + 0q` and
`Inf + 10p + 2q`. The probe searched `a` upward and only ever saw the minimal
one, while the lemma accepted any.

**Rule this gives us: state a leaf so that a probe can quantify exactly as the
lemma does.** `ge_wrap_tight` (its replacement) names no decomposition.

## 3. Verified statements, with counts

| statement | count |
|---|---|
| `dstB` without the `Pt` hypothesis | 0 / 104326944 |
| `invx_gap` (decomposition exists) | 0 / 53120 |
| `invx_gap` with `a <= u`, `b <= v` | 0 / 226002 |
| `invx_inf` (`Inf (u+v) < maxn p q`) | 0 / 17608 |
| `invx_p1` | 0 / 2362 |
| `invx_p2` (needs the `%% M`; without it 672 failures, one per state) | 0 / 2362 |
| `invx` preserved by `step` | 0 / 376 |
| `Inf(new) = Inf(u+v) %% p` (`lt` branch) | 0 / 2576 |
| `inf_cong_ge` | 0 / 1384 |
| `d = Inf (u+v)` in the `ge` branch, initial state excluded | 0 / 5216 |
| `mod_le_restricted` (guarded) | 0 / 7532 |
| `ge_d_lt_q` | 0 / 28197 |
| `ge_wrap_tight` | 0 / 11335 (3124 left disjunct, 10701 right) |
| `pt_neq0 <-> N < M %/ gcdn A M` | 0 / 106962, all M<60, all A, N up to twice the bound |
| `le_ge_wrap` | 0 / 16705 |

## 4. `invx` — which fields are needed

Established by proof, not inspection (each leaf states its dependencies):

| field | downstream consumer | consumed by the step |
|---|---|---|
| `invx_inf` | `ge_d_eq_inf`, `inf_new_lt_le` | — |
| `invx_gap` | `mod_le_restricted` | — |
| `invx_min` | **none** | `lt/min`, `ge/min`, `ge/max` |
| `invx_max` | **none** | `lt/min`, `lt/max`, `ge/max`, `ge/p1` |
| `invx_qM` | only the unused `pt_gap_max`; free from `inv` | — |
| `invx_p1` | `invx_p1_iter` | — |
| `invx_p2` | **none** | **none** — it is a theorem about any `inv` state (`pt_subu`) |

So `invx_min`/`invx_max` are induction-only, and `invx_p2` and `invx_qM` can
leave the record.

## 5. The twelve `invx_step` leaves

`grep "@INVX_STEP" Alg2.v` lists them with status. Proved: `lt/min`, `lt/max`,
`lt/p2`, `ge/min`, `ge/max`, `ge/p1`, `ge/p2`.

Shared helpers, both admitted: `pt_new_lt` and `pt_new_ge` — a new index is an
old one walked by `j` copies of `v` (resp. `u`); the `lt` walk adds `j*p`, the
`ge` walk subtracts `j*q`. `pt_new_lt`'s proof is the middle of the proved
`lt/min`. `pt_new_ge` has a corner: `Pt 0 = 0` cannot carry the walk.

Remaining, with what each wants:

- **`lt/p1`** — by `pt_addv` this is `Pt z + p < M` for `z < u + k*v`. Old `z`
  are free (`Pt z <= M - q`, `p < q`). New ones need `(j+1)*p <= q`, i.e.
  `j < k`. *Helper wanted:* `new_index_decomp` sharpened to conclude `j < k`
  when `x < u + k*v`.
- **`lt/inf`** — `Inf` only decreases as the range grows, so the content is
  that it drops below the *new* `maxn p' q'`. **Not** via `inf_new_lt`:
  that goes `inf_new_lt` → `step_invd_le` → `step_invd_le_pt` →
  `step_invd_le_new` → `le_lt_nowrap` → `mod_le_restricted`, which needs
  `invx`. Circular. (An earlier note here suggested lifting `inf_new_lt`
  earlier; that is wrong.)
- **`ge/inf`** — no computed counterpart (the `ge` analogue of `inf_new_lt` is
  false, §1), so it needs the gap argument directly.
- **`lt/gap`, `ge/gap`** — the trade `q = q' + (q %/ p)*p` is **free**
  (`subnK` + `leq_divM`), so no helper is wanted there. The content is the
  count bookkeeping: from `a <= u`, `b <= v` and `a*p + b*q =
  (a + b*k)*p + b*q'` one gets `a' = a + b*k <= u + v*k = u'`, `b' = b <= v'`.
  But the new decomposition is relative to the **new** `Inf`, so
  **`lt/gap` depends on `lt/inf`** (and `ge/gap` on `ge/inf`). Do the `inf`
  pair first.

## 6. Other open holes

- **`pt_neq0`** — now a lemma, not an axiom (§3). Proof: `Pt n = 0` iff
  `M %| A*n` iff `(M %/ g) %| n` by Gauss after dividing by `g = gcdn A M`;
  `N_lt_Mg` puts the first such `n` beyond `N`.
- **`ge_wrap_tight`** — §1/§2. The `p`-interval half is the congruence
  argument of PR #121 and lifts verbatim.
- **`invx_p2_iter`** — mirror of the proved `invx_p1_iter`; same induction,
  one extra `modnDml` for the `%% M`.
- **`inf_cong_ge`** — the `ge`-branch congruence. Untouched; the mirror
  shortcut is false (§1).

## 7. Rocq gotchas hit in this file

- `rewrite -foo ?ltnW //` **diverges** when `ltnW` is an implication — pass
  arguments explicitly.
- `case: leqP` binds the *outer* comparison, not an inner `if` — use
  `case: (leqP lhs rhs)`.
- `ltn_mod` is an equation, `ltn_pmod` the proof.
- Long `rewrite a b ?side //` chains time out; split them.
- `Inf` unfolds under `/=`; `Arguments inf_dst : simpl never` plus
  `inf_dst0`/`inf_dstS`.
- Lemma **order** blocked two leaves (`step_p_gt0`, `new_index_decomp` were
  below the `invx` section); both are hoisted now.
