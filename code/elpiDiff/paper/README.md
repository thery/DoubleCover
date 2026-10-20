# The papers elpiDiff builds on

The references, with links ([references.bib](references.bib) for BibTeX). The
PDFs are not in the repository: the two POPL papers are on arXiv under the
arXiv license, which lets arXiv, not us, distribute them; the third is an
Elsevier article, whose technical report is on HAL. `paper/*.pdf` is ignored by git, so a local copy can sit
here (for the arXiv ones: `curl -o <name>.pdf https://arxiv.org/pdf/<id>`).

- **Abadi and Plotkin, *A Simple Differentiable Programming Language*.**
  Proc. ACM Program. Lang. 4, POPL (2020), 38:1–38:28.
  [doi:10.1145/3371106](https://doi.org/10.1145/3371106),
  [PDF](https://arxiv.org/pdf/1911.04523) (free, on
  [arXiv:1911.04523](https://arxiv.org/abs/1911.04523)).
  Its partial semantics, where a comparison of two equal reals is undefined,
  is the one of the Rocq proofs: `smooth_reals` and `defined` in
  [../rocq/Smooth.v](../rocq/Smooth.v), the hypothesis "f is defined at x" of
  the main theorems.

- **Radul, Paszke, Frostig, Johnson and Maclaurin, *You Only Linearize
  Once: Tangents Transpose to Gradients*.** Proc. ACM Program. Lang. 7, POPL
  (2023), 1246–1274.
  [doi:10.1145/3571236](https://doi.org/10.1145/3571236),
  [PDF](https://arxiv.org/pdf/2204.10923) (free, on
  [arXiv:2204.10923](https://arxiv.org/abs/2204.10923)).
  Reverse mode as forward mode, then partial evaluation with respect to the
  primal input (what remains is linear in the tangents), then transposition of
  that linear program: the compiler view of the adjoint, a possible structure
  for the adjoint pass and its proof (the tangent is correct, partial
  evaluation preserves the semantics, the to-be-recorded analysis keeps the
  coefficients the reverse sweep reads, transposition is adjoint for every
  linear program).

- **Hascoët, Naumann and Pascual, *"To be recorded" analysis in
  reverse-mode automatic differentiation*.** Future Generation Computer
  Systems 21(8) (2005), 1401–1417.
  [doi:10.1016/j.future.2004.11.009](https://doi.org/10.1016/j.future.2004.11.009).
  Free PDF of the earlier technical report: L. Hascoët, U. Naumann and V.
  Pascual, *TBR Analysis in Reverse-Mode Automatic Differentiation*, INRIA
  research report RR-4856 (2003), on HAL:
  [inria-00071727](https://inria.hal.science/inria-00071727v1),
  [PDF](https://inria.hal.science/inria-00071727v1/document). The to-be-recorded analysis (TBR) of Tapenade: which
  values the reverse sweep reads and must therefore be recorded; elpiDiff's
  `tbr.elpi` and its annotations (`computed`, `recorded`) follow it.
