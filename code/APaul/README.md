# APaul: the search for hard-to-round inputs of exp

The verified parts of this work have moved to a private repository
(postech-pl/libm-coremath-proofs, directory exp/htr-search):

- code/exptablekl (the check of the tables with k and l on each line),
- code/APaul/exp100 (the filter exp100 and its Rocq model),
- code/APaul/vst (the VST proofs of the search htr3.c, of exp100 and of the
  filter htr_filter.c),
- code/APaul/capla/exp100v2 and code/APaul/capla/htrfilter (the Capla
  proofs of exp100 and of the filter), and the older code/APaul/capla/exp100
  and code/APaul/capla/htr3 that they replace,
- the notes doc/exptablekl-note, doc/exp100-vst-plan,
  doc/exp100-capla-plan and doc/htr3-capla-plan.

They are still in the history of this repository: the last commit that has
them is e476da8 (`git checkout e476da8 -- code/APaul/vst`, for instance).

What stays here: rocq/ (the model of the search and the work on the search
algorithms), the C programs of the search (htr*.c, htrplan/), capla/ (the
other Capla experiments), and code/exptable, code/exptable9 (the checks of
the earlier tables).
