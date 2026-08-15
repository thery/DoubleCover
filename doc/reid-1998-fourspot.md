# Superflip composed with four spot

Michael Reid, posted to Cube-Lovers, Sunday 2 August 1998.

> From: michael reid `<reid@math.brown.edu>`
> To: cube-lovers@ai.mit.edu
> Subject: superflip composed with four spot

Reference [16] of Rokicki, Kociemba, Davidson and Dethridge, *The diameter of
the Rubik's cube group is twenty*, SIAM J. Discrete Math. 27 (2013) 1082–1105,
where it is cited as the source of the quarter-turn lower bound of 26. The URL
given there, `math.ucf.edu/~reid/Rubik/Cubelovers/`, no longer resolves.

Transcribed verbatim; only the formatting is added.

---

With my new optimal solver, I can show that the position

    superflip composed with four spot

is exactly 26 quarter turns from start. This gives a new lower bound for the
diameter of the cube group. The previous lower bound, 24q, was from the
position superflip, and was first established by Jerry Bryan.

Let `F2 B2 U D' R2 L2 U D'` be our choice of orientation of four spot.
Although four spot is not central, the position

    F2 B2 U D' R2 L2 U D'  C_U2

moves only face center cubies: `(F, B) (R, L)`. (Here `C_U2` denotes whole
cube rotation by 180 degrees about the U-D axis.) Since quarter turns do not
move face center cubies, we see that the sequence above commutes with any
sequence of quarter turns. The same is also true for

    superflip . four spot . C_U2

In terms of Singmaster's fixed face model, this means that we can cyclically
shift a maneuver for superflip composed with four spot, but the part that is
cyclically shifted gets conjugated by the cube rotation `C_U2`. For example:

    (B  U2 L) (U' D  L2 F2 R2 B  U2 R' L' D  R2 D  F2 U  R2 D  B)

creates this position. If we cyclically shift the first three twists to the
end, we get another maneuver for this position:

    (U' D  L2 F2 R2 B  U2 R' L' D  R2 D  F2 U  R2 D  B) (F  U2 R)

This observation about cyclic shifting enables us to prove

**Proposition 1.** Superflip composed with four spot is a local maximum in the
quarter turn metric.

*Proof.* We need to show that any quarter turn takes us closer to start. The
12 different twists split up into two different types under the symmetry of
this position: `{U, U', D, D'}` and `{R, R', F, F', L, L', B, B'}`. We claim
that any maneuver for superflip composed with four spot must contain twists of
both types. A maneuver consisting only of twists in `{U, U', D, D'}` clearly
cannot produce this position. Also, a maneuver consisting only of twists in
`{R, R', F, F', L, L', B, B'}` cannot flip any edges. Thus both twist types
must occur. Now consider a minimal maneuver for superflip composed with four
spot. We may cyclically shift (and apply symmetry) so that the last twist is
`U'`. Thus, applying `U` cancels this last twist and brings us closer to
start. Similarly, we can cyclically shift to get a minimal maneuver ending
with `R'`, so applying `R` also brings us closer to start. Since any twist is
equivalent to `U` or `R`, we have proved local maximality. ∎

The significance of this proposition is that this is the first case beyond the
Hoey-Saxe local maxima in which we can prove local maximality without computer
searching. (Please correct me if I'm wrong about this.)

Dan Hoey noted (a long time ago) that the position four spot is a local
maximum. However, I don't see that this can be proved without computer search.
The sticking point is that four spot can be achieved using only
`{R, R', F, F', L, L', B, B'}`. However, no minimal maneuver consists only of
these twists, a fact determined by computer search.

Similar to the transformations for superflip, we have three transformations to
apply to maneuvers for superflip composed with four spot.

* we may conjugate by any of the 16 cube symmetries that fix the U-D axis;
* we may cyclically shift the maneuver, as described above;
* we may invert the maneuver.

**Proposition 2.** By using the three transformations above, any maneuver for
superflip composed with four spot can be transformed into one that begins with
one of the six sequences

    R  U          R' U  D        R' U  F'
    R' U  R'      R' U  B'       R' U  L'

*Proof.* As shown in prop. 1, any sequence for superflip composed with four
spot contains both types of twists. Thus, the two types occur as consecutive
twists. By cyclic shifting, and applying symmetry, we may suppose that the
first two quarter turns are either `R U` or `R' U`. (This would already be
enough reduction for my program.) We can cut down the case `R' U` further.
There are eleven possibilities for the third quarter turn; only `U'` is not
allowed. The case `R' U U = R' U2` is equivalent under symmetry to `R U2`,
which is part of the case beginning with `R U`. The case `R' U D'` is
equivalent under symmetry to `R D' U = R U D'`, again part of the case
beginning with `R U`. The case `R' U B` inverts to `B' U' R`, and this is
equivalent to `R U B'`, which is part of the case beginning with `R U`.
Similarly, the cases beginning with `R' U R`, `R' U F` and `R' U L` invert to
`R U R'`, `R U F'` and `R U L'`, respectively. This leaves only the sequences
listed above. ∎

My program exhaustively searched the positions

    superflip . four spot . R  U        through 22q  and

    superflip . four spot . R' U  D   \
    superflip . four spot . R' U  F'   \
    superflip . four spot . R' U  R'    >  all through 21q
    superflip . four spot . R' U  B'   /
    superflip . four spot . R' U  L'  /

and found no maneuvers. Thus superflip composed with four spot requires more
than 24 quarter turns. **The total search time was about 153 hours.** To see
that superflip composed with four spot can be achieved in 26 quarter turns,
use

    U2 D2 L  F2 U' D  R2 B  U' D' R  L  F2 R  U  D' R' L  U  F' B'   (26q*, 21f)

It might be reasonable to ask for all 26q maneuvers. This is probably out of
reach for now. However, I suspect that there will be so many different 26q
maneuvers that it would not be of much use to see a long list of maneuvers.
(I have a bunch already.)

Superflip composed with four spot also requires 20f.

**Proposition 3.** Any maneuver for superflip composed with four spot of
length <= 20f can be transformed to one that begins with one of the sequences
`U2 R`, `R2 F` or `R2 U`.

The proof is very similar to the reductions for superflip in the face turn
metric.

Using this, a complete search for 20f maneuvers is straightforward. There are
two inequivalent 20f maneuvers for superflip composed with four spot:

    F  U2 R  L  D  F2 U  R2 D  F2 D  F' B' U2 L  F2 R2 B2 U' D    (20f*, 28q)
    F  U2 R  L  D  F2 U  R2 D  F2 D  F' B' U2 L  U' D  R2 B2 L2   (20f*, 28q)

This also shows that no maneuver is simultaneously minimal in both metrics.

mike

---

## What we checked of this, and where

`code/Rubik/ocaml/rubik_reid.ml`, `./rubik_reid <cap> check`:

* `p⁻¹ q p = σ q` for all twelve quarter turns, where `σ` is conjugation by
  `C_U2` — this is the commutation the whole proof turns on, stated without
  face centres, which our cubie model does not have;
* every one of the 26 cyclic shifts of his 26q maneuver still gives `p`;
* the 26q maneuver gives `p`;
* the corner permutation of `p` is even, so its distance is even — which is
  what takes "more than 24" to "exactly 26", a step he leaves implicit.

Propositions 1, 2 and 3 are **not** checked. Proposition 2 is what makes those
six the right six.

One trap for anyone porting Proposition 1. It needs that turns of R, L, F and
B cannot flip an edge, which is true in the orientation convention where U and
D are the flipping turns, and **false** in ours, where F and B are. Since the
orientation of four spot is a free choice — he says so — the fix is to turn
the position onto the front-back axis rather than to change the convention.
Then his four are `{F, F', B, B'}` and his eight are `{U, U', D, D', R, R',
L, L'}`, which carry no flip here. `./rubik_reid <cap> rephrase` checks that,
including that the eight really cannot reach `p` and that the four generate
only sixteen positions, none of them `p`.
