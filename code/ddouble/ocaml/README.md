# What is measured here

`f2scond.ml` -- the two Fast2Sum calls inside `plusDwDwErr` are exact only
under a condition, and this asks which condition is the true one.  It walks
well formed double words whose high words nearly cancel and whose low words
are as large as a double word allows, which is where the condition can fail;
a plain random walk never reaches that corner.  The first pair it tries is a
known failure of `|c| <= |sh|`, as a check on the harness itself.

    ocamlopt f2scond.ml -o f2scond && ./f2scond

`addup_ub.ml` -- can `add_UP` return minus infinity as its high word?  If it
can, the result is barred from being an upper bound and the signature's
obligation fails.  It mirrors `dwarith.v` and `dw_updn.v` step for step and
hunts at the top of the range, where the last Fast2Sum can overflow while
everything before it is finite.  It found nothing in 3.8 million well formed
pairs -- an overflow makes TwoSum compute infinity less infinity, which turns
everything after it into a NaN -- but not finding one is not a proof, which is
why `dw_ops.v` checks the result instead.

    ocamlopt addup_ub.ml -o addup_ub && ./addup_ub
