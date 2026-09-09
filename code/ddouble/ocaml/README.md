# What is measured here

`f2scond.ml` -- the two Fast2Sum calls inside `plusDwDwErr` are exact only
under a condition, and this asks which condition is the true one.  It walks
well formed double words whose high words nearly cancel and whose low words
are as large as a double word allows, which is where the condition can fail;
a plain random walk never reaches that corner.  The first pair it tries is a
known failure of `|c| <= |sh|`, as a check on the harness itself.

    ocamlopt f2scond.ml -o f2scond && ./f2scond
