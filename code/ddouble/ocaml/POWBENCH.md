# powbench.ml

The same `pi^100` as `../c/powbench.c`, written in OCaml, which is the
machine Rocq itself runs on.  Two things change, and both are forced:

  * the double word multiplies by Dekker's method, the definitions copied
    from `dwarith.v`, because a Rocq primitive float has no fused multiply
    add to build the exact product with;
  * the integer mantissa is two words of 60 bits, and the product of two
    words has to be put together out of four products of half words,
    because no integer here can hold the whole of it.

Run with

    ocamlopt -O3 -o powbench powbench.ml && ./powbench

Two lopsided costs had to be taken out before the two times could be
compared.  `splitC`, `dekker` and `fastTwoSum` are written out inside
`timesDwDw` rather than called, since a float returned from a function is
put in a box while one held in a local name stays in a register; and there
is one power function per arithmetic rather than one taking the
multiplication as an argument, which would call through a pointer on every
step.  With both removed each side puts one record in the heap per
multiplication, four words against three.

The single float line is not a fair yardstick: its power function passes
floats across a call and so boxes them.
