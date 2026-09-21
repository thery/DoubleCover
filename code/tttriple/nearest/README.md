# The round-to-nearest triple word

Nothing on the build path calls any of this. It is kept because it is what an
obvious implementation looks like, and the distance between it and what
`tw_ops.v` runs is the whole argument for using the paper's algorithms.

## What is here

| | |
|---|---|
| `twnearest.v` | the four operations rounded to nearest, and the sort the product used to do |
| `test_pi.v` | pi by Machin's formula over them, and the interface's brackets beside it |

`twnearest.v` holds `plusTwTw`, `subTwTw`, `timesTwTw`, `timesTwFp`,
`divTwTw`, `sqrtTw`, `dw2tw`, the insertion sort `sortMag`/`insMag`, and the
four lemmas in `twbound.v` that were about the sort.

## Why it is off the build path

These were the first implementation. Each is the direct thing to write and
each is far dearer than what replaced it:

| | µs | what runs instead | µs |
|---|---|---|---|
| `divTwTw`, three rounds of long division | 25 | `threeDiv`, the paper's Algorithm 14 | 10.6 |
| `sqrtTw`, two Newton steps | 49 | `threeSqRt`, Algorithm 15 | — |
| `timesTwTw`, thirteen terms sorted then swept | — | `mulTwUp`, written in size order | 6.15 |

`divTwTw` is three rounds of long division and each round does a **full**
triple-word multiplication; `sqrtTw` is two Newton steps and each one contains
a `divTwTw`. The sort was three microseconds of a product's eleven, and the
sweeps never used the order — only that the sum was unchanged — so it went.

There is a second reason, and it is the one that matters for a bound. These
round **to nearest**, so they are not bounds at all: an interval end has to
fall on a known side of the exact answer, and `RN` gives neither side. Every
operation on the build path rounds in a direction. Nothing here could be used
for an enclosure without being redone.

## Why it was worth keeping rather than deleting

Two of the numbers in the parent README come from running these, and a table
that says the paper's quotient is 10.6 microseconds means little without the
25 beside it. `test_pi.v` also runs Machin's formula far enough to show how
many digits three words really hold, which no goal on the build path does.

## Building it

Build `code/ddouble` and then `code/tttriple` first, then:

```
coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith nearest/twnearest.v
coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith nearest/test_pi.v
```

Both compile. Neither proves anything the interface rests on: `twnearest.v`
carries the four sort lemmas and no more, and `test_pi.v` is a smoke test.
