(* =========================================================================  *)
(*  Phase1.v -- SKELETON.  Every lemma is Admitted; this file fixes the        *)
(*  DESIGN and the SIZES of the phase 1 table, nothing else.                  *)
(*                                                                            *)
(*  The flip x slice table Far.v ships today is 2 ^ 24 entries and caps the    *)
(*  heuristic at 9.  Phase 1 -- twist x flip x slice -- caps at 12, which is   *)
(*  what a depth 19 search needs.  The raw space is                           *)
(*                                                                            *)
(*     2187 twist  x  2048 flip  x  495 slice  =  2 217 093 120 states        *)
(*                                                                            *)
(*  and the whole question is whether that fits.  It does, in ONE PArray,      *)
(*  because of two independent reductions:                                    *)
(*                                                                            *)
(*  SYMMETRY.  Only ONE representative per orbit need be stored.  Measured,    *)
(*  NOT quoted -- computed from Sym.v's own generators Sy, Sx, Sm:             *)
(*                                                                            *)
(*     symmetry group                     48   (closure of Sy, Sx, Sm)        *)
(*     act on the flip x slice coord      16   <-- see the warning below       *)
(*     reachable flip x slice      1 013 760   = 2048 x 495, all of them       *)
(*     orbits                         64 430   reduction 15.73x               *)
(*                                                                            *)
(*  which independently reproduces Kociemba's published 64 430.                *)
(*                                                                            *)
(*  WHY SIXTEEN AND NOT FORTY EIGHT.  An earlier version of this file claimed  *)
(*  all 48, on the grounds that Sym.Symg_stab makes every u in Symg permute    *)
(*  the move set and so preserve the distance.  That argument is about the     *)
(*  distance on the CUBE.  The fold is applied to the flip x slice COORDINATE, *)
(*  and a u that moves the UD slice does not act on that coordinate at all:    *)
(*  coordfs (g ^ u) is then not a function of coordfs g, so "the orbit of a    *)
(*  coordinate" is not even well defined.  Tested directly -- for each u, over *)
(*  540 000 pairs with coordfs a = coordfs b, is coordfs (a ^ u) =             *)
(*  coordfs (b ^ u)?  Exactly 16 of the 48 pass.  It is also what Far.v has    *)
(*  been telling us all along: its heuristic maxes over five views BECAUSE     *)
(*  they differ (7, 7, 6 at the root), which could not happen if conjugation   *)
(*  left the coordinate invariant.                                            *)
(*                                                                            *)
(*  CLAMP.  Two bits per entry, holding d - 8 clamped to [0, 3].  Entries      *)
(*  below 8 never prune at the depths we search, and clamping DOWN keeps the   *)
(*  heuristic admissible -- a smaller h is always safe.                        *)
(*                                                                            *)
(*  Together:                                                                  *)
(*                                                                            *)
(*     2187 x 64 430            = 140 908 410 entries                         *)
(*     at 31 entries per int63  =   4 545 433 words  =  36.4 MB               *)
(*     PArray.max_length        =   4 194 303 words                           *)
(*                                                                            *)
(*  which overshoots max_length by 8%, so it takes THREE chunks -- a PArray    *)
(*  of PArrays split on the word index, w >> 21, which stays definitional.     *)
(*                                                                            *)
(*  For scale, against the flip x slice table we ship today:                   *)
(*                                                                            *)
(*                      entries      per word   words       size              *)
(*     flip x slice   16 777 216      8         2 097 152   16.8 MB           *)
(*     phase 1       140 908 410     31         4 545 433   36.4 MB           *)
(*                                                                            *)
(*  8.4x the entries but only 2.2x the memory, the 2 bit packing absorbing     *)
(*  the rest.  Per worker that is +20 MB against the ~1 GB each already uses,  *)
(*  so -j18 is unaffected.  The real cost is not memory but FsData.v: 25 MB    *)
(*  of literals today, ~54 MB here, and it already compiles serially in 4-6    *)
(*  minutes.                                                                  *)
(*                                                                            *)
(*  WHAT IS STILL MISSING is only the proofs and the generated data.  See the  *)
(*  Admitted list at the bottom.                                              *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
(* Far.v's chain minus Fsmain, so this does not drag in the sixteen
   certificate files *)
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* =========================================================================  *)
(*  1.  The corner data                                                       *)
(*                                                                            *)
(*  DERIVED from the move tables, not read off a picture of a cube.  A facelet *)
(*  is a corner facelet iff f mod 8 is in {0,2,5,7} (each face is a row major  *)
(*  3x3 with the centre dropped, which is what Coordfs.eprim's {1,3,4,6}       *)
(*  confirms).  Two corner facelets sit on the same cubie iff exactly the same *)
(*  face turns fix them -- a corner lies on 3 of the 6 faces and distinct      *)
(*  corners have distinct face triples, so the eight triples fall out of the   *)
(*  fixed sets.                                                               *)
(*                                                                            *)
(*  THE U/D AXIS IS NOT A FREE CHOICE.  It must be the axis the flip x slice   *)
(*  coordinate already uses, namely the two faces whose quarter turn leaves    *)
(*  the slice alone.  An earlier version put it elsewhere; twist and           *)
(*  flip x slice were then quotients along different axes, their product was   *)
(*  not Kociemba's phase 1 coordinate, and every BFS level came out too large  *)
(*  (6, 71, 810, ... against the correct 4, 50, 592, ...).  Caught by the      *)
(*  generator, whose depth histogram must agree with ocaml/rubik_par.ml's.     *)
(*                                                                            *)
(*  NB two numberings that are easy to confuse: the MOVE GROUP k / 3 and the   *)
(*  FACELET BLOCK f / 8 do not agree.  Move group 3 spins block 5.  The U/D    *)
(*  groups are 0 and 3; the U/D blocks are 0 and 5, and it is the blocks that  *)
(*  carry the stickers below.                                                 *)
(* =========================================================================  *)

(* 3 ^ 7 -- the eighth orientation is forced, the sum being 0 mod 3 *)
Definition ntwist := 2187.

(* the U/D sticker of each corner, one per cubie *)
Definition cprim : seq nat := [:: 0; 2; 5; 7; 40; 42; 45; 47]%N.

(* the three stickers of each corner, U/D one first.  The cyclic order of the
   other two is a free choice: swapping them recodes one base 3 digit
   bijectively, so all 2 ^ 8 choices give the same 2187 value quotient.  The
   AXIS, however, is not free -- see the warning above. *)
Definition ctrip : seq (nat * nat * nat) :=
  [:: ( 0,  8, 34); ( 2, 26, 32); ( 5, 10, 16); ( 7, 18, 24);
      (40, 15, 21); (42, 23, 29); (45, 13, 39); (47, 31, 37)]%N.

(* NB: qualified Uint63 functions throughout rather than the << and >> and
   .[ ] notations -- fingroup owns << _ >> for the generated subgroup, so the
   shift notation does not survive an all_fingroup import. *)
Definition cmask : int := Eval vm_compute in
  foldr (fun f a => Uint63.lor a (Uint63.lsl 1%uint63 (of_nat f))) 0%uint63
        cprim.

(* is facelet x a U/D sticker?  the bitmask form, as Coordfs's bit pmask *)
Definition bitc (x : int) : bool :=
  negb (Uint63.eqb (Uint63.land cmask (Uint63.lsl 1%uint63 x)) 0%uint63).

(* Three levels, exactly as Coordfs / Coordfsi do it for flip x slice:
   arrays (what the search runs), lists (the intermediate), permutations (what
   the proofs talk about).  The bridges are ectwistiE and ctwisttE below,
   mirroring Coordfsi.ecoordiE and Coordfsi.coordtE.

   In all three, u is the INVERSE, so u at slot s is the facelet occupying s. *)

Definition corienti (u : arr) (t : nat * nat * nat) : nat :=
  let: (c0, c1, c2) := t in
  if bitc (PArray.get u (of_nat c0)) then 0%N
  else if bitc (PArray.get u (of_nat c1)) then 1%N else 2%N.

Definition corientt (u : seq nat) (t : nat * nat * nat) : nat :=
  let: (c0, c1, c2) := t in
  if nth 0%N u c0 \in cprim then 0%N
  else if nth 0%N u c1 \in cprim then 1%N else 2%N.

(* base 3 over the first seven corners; the eighth is forced *)
Definition ectwisti (u : arr) : int :=
  foldr (fun t x => Uint63.add (Uint63.mul x 3%uint63) (of_nat (corienti u t)))
        0%uint63 (take 7 ctrip).

Definition ectwistt (u : seq nat) : int :=
  foldr (fun t x => Uint63.add (Uint63.mul x 3%uint63) (of_nat (corientt u t)))
        0%uint63 (take 7 ctrip).

Definition ctwisti (a : arr) : int := ectwisti (inv_tabi 47 a).
Definition ctwistt (t : seq nat) : int := ectwistt (inv_tab 47 t).

(* the 2187 x 18 twist move table, alongside Coordfsi's actf.  GENERATED. *)
Definition twmove : arr := PArray.make (of_nat (ntwist * 18)) 0%uint63.

Definition acttw (x : int) (k : nat) : int :=
  PArray.get twmove (Uint63.add (Uint63.mul x 18%uint63) (of_nat k)).

(* the structured counterpart, for the proofs -- mirrors Coordfs.coordfs, which
   is likewise stated with g^-1 applied to the slot's primary facelet *)
Definition udcol (f : facelet) : bool := (f : nat) \in cprim.

Definition corientg (g : {perm facelet}) (p : nat) : nat :=
  let: (c0, c1, c2) := nth (0, 0, 0)%N ctrip p in
  if udcol (g^-1 (inord c0)) then 0%N
  else if udcol (g^-1 (inord c1)) then 1%N else 2%N.

Definition coordtw (g : {perm facelet}) : int :=
  foldr (fun p x => Uint63.add (Uint63.mul x 3%uint63) (of_nat (corientg g p)))
        0%uint63 (iota 0 7).

(* =========================================================================  *)
(*  2.  Re-indexing flip x slice into 1 013 760 consecutive slots             *)
(*                                                                            *)
(*  Coordfs packs flip into bits 0..11 and slice into bits 12..23, so the      *)
(*  packed coordinate ranges over 2 ^ 24 while only 2048 x 495 values occur.   *)
(*  Indexing the class table by the packed value would need 16.7 M words and   *)
(*  therefore chunking; ranking the slice mask instead gives 1 013 760 and one *)
(*  array.  srank is 4096 words, the rank of each 12 bit mask among those with *)
(*  four bits set, or 495 for the ones that cannot occur.                      *)
(* =========================================================================  *)

Definition nflip  := 2048.
Definition nslice := 495.
Definition nfs    := 1013760.   (* nflip * nslice *)

Definition srank : arr :=                                     (* GENERATED *)
  PArray.make 4096%uint63 (of_nat nslice).

(* NB 2047, not 4095.  The flip occupies twelve bits but edge flip parity is
   even, so bit 11 is determined by bits 0..10 and only 2048 of the 4096 occur.
   Masking with 4095 indexes past the end of fsclass -- caught by running the
   generator on the flip x slice table, where it failed at once. *)
Definition fsidx (x : int) : int :=
  Uint63.add
    (Uint63.mul (Uint63.land x 2047%uint63) (of_nat nslice))
    (PArray.get srank (Uint63.lsr x 12%uint63)).

(* =========================================================================  *)
(*  3.  The symmetry fold                                                     *)
(*                                                                            *)
(*  fsclass sends each of the 1 013 760 flip x slice indices to its orbit      *)
(*  representative together with the symmetry that gets there, packed as       *)
(*  class * 16 + sym (64 430 * 16 < 2 ^ 21, so one int63 is ample).  The twist *)
(*  must be conjugated by the SAME symmetry, which is what twconj is for:      *)
(*  2187 * 16 = 34 992 entries.                                               *)
(* =========================================================================  *)

(* the sixteen that ACT on the flip x slice coordinate, not all 48 of Symg *)
Definition nsym   := 16.
Definition nclass := 64430.

Definition fsclass : arr := PArray.make (of_nat nfs) 0%uint63.            (* GENERATED *)
Definition twconj  : arr := PArray.make (of_nat (ntwist * nsym)) 0%uint63. (* GENERATED *)

(* the folded phase 1 index: 0 .. 2187 * 64430 *)
Definition p1idx (tw x : int) : int :=
  let c  := PArray.get fsclass (fsidx x) in
  let s  := Uint63.land c 15%uint63 in
  let cl := Uint63.lsr c 4%uint63 in
  Uint63.add (Uint63.mul cl (of_nat ntwist))
    (PArray.get twconj (Uint63.add (Uint63.mul tw (of_nat nsym)) s)).

(* =========================================================================  *)
(*  4.  The table itself: two bits per entry, 31 per word                     *)
(* =========================================================================  *)

Definition p1base  := 8.        (* entries hold d - p1base, clamped to [0,3] *)
Definition p1words := 4545433.  (* ceil (2187 * 64430 / 31) *)

(* 4 545 433 > PArray.max_length = 4 194 303, so the table is a PArray of
   PArrays.  The split is on the WORD index at a power of two, w >> cwlog,
   which stays definitional -- the same trick Fspar.v's cbits uses.  Three
   chunks: two full at 2 ^ 21 words and a short tail of 351 129. *)
Definition cwlog  := 21.
Definition nchunk := 3.

Definition p1tabs : PArray.array arr :=                           (* GENERATED *)
  PArray.make (of_nat nchunk) (PArray.make 1%uint63 0%uint63).

Definition p1get (i : int) : int :=
  let w := Uint63.div i 31%uint63 in
  let r := Uint63.sub i (Uint63.mul w 31%uint63) in
  let c := Uint63.lsr w (of_nat cwlog) in
  let o := Uint63.land w (Uint63.sub (Uint63.lsl 1%uint63 (of_nat cwlog))
                                     1%uint63) in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get p1tabs c) o) (Uint63.mul r 2%uint63))
    3%uint63.

(* the heuristic.  Clamping DOWN is what keeps this admissible. *)
Definition Dp1 (tw x : int) : nat := p1base + to_nat (p1get (p1idx tw x)).

(* =========================================================================  *)
(*  5.  What has to be proved                                                 *)
(*                                                                            *)
(*  Exactly the shape Coordfs already uses: the table is never asked to be     *)
(*  CORRECT, only to be a local certificate.  Fsmain.v discharges the flip x   *)
(*  slice version in sixteen generated slices glued by all_pow_glue16, and     *)
(*  the same mkfs.sh machinery applies here -- the check is a forall over      *)
(*  independent entries, so it parallelises with no new proof technique.       *)
(*  Budget: about 70 CPU hours, roughly 4 hours wall at -j18, once.            *)
(* =========================================================================  *)

(* -- the twist is a genuine quotient coordinate -------------------------- *)

(* the identity leaves every corner's U/D sticker on its own slot, so every
   base 3 digit is 0.  perm1 kills the permutation and inordK the ordinal, and
   then each test is a membership in cprim that computes.  NB neither
   vm_compute nor native_compute can do this directly -- they time out on the
   48 element finfun behind (1 : {perm facelet}). *)
Lemma coordtw_id : coordtw 1 = 0%uint63.
Proof. by rewrite /coordtw /corientg invg1 /= !perm1 /udcol !inordK. Qed.

(* the bitmask really is membership in cprim -- 48 cases, so it computes *)
Lemma bit_cmask x : (x < 48)%N -> bitc (of_nat x) = (x \in cprim).
Proof.
move=> xL.
have H : all (fun k => bitc (of_nat k) == (k \in cprim)) (iota 0 48).
  by vm_compute.
by move/allP: H => /(_ x); rewrite mem_iota /= xL => /(_ isT)/eqP.
Qed.

Lemma of_pos_of_nat n : of_pos n = of_nat (BinPos.Pos.to_nat n).
  by rewrite Znat.positive_nat_Z.
  Qed.

(* array -> list, mirroring Coordfsi.ecoordiE.

   STUCK -- the proof below gets to one step from the end and then loops.
   After

     rewrite !bE.

   there are 15 goals: the first is literally X = X and closes with by [],
   and the other 14 are  to_nat (get u (of_pos k)) < 48  for the fourteen
   facelets of the seven triples.  blt discharges exactly those, but

     apply: blt

   diverges, and so does a trailing //.  The reason looks like the numerals:
   the /= that unfolds foldr over the concrete seven element take 7 ctrip
   also normalises of_nat 37 into of_pos 37%AC, so closing the side goal asks
   unification to solve  of_nat ?c == of_pos 37%AC,  i.e. to invert of_nat,
   and it unfolds forever.  Coordfsi.ecoordiE does not hit this because it
   goes through eq_packn and never simplifies a numeral.

   Two ways out I can see, both of which I would rather you picked between:
   lock of_nat across the /=, or restate ectwist* as a fold over iota 0 7
   with nth into ctrip so the side condition is c < 7 rather than a numeral.

Proof.
move=> uok.
have bE (y : int) : (to_nat y < 48)%N -> bitc y = (to_nat y \in cprim).
  by move=> yL; rewrite -bit_cmask ?to_natK.
have blt c : (c < 48)%N -> (to_nat (PArray.get u (of_nat c)) < 48)%N.
  by move=> cL; apply: tabi_lt.
rewrite /ectwisti /ectwistt /=.
rewrite !bE.                      (* 15 goals; goal 1 is X = X *)
(* ... and here apply: blt loops on every one of the fourteen *)
Qed. *)
Lemma ectwistiE u : tabi_ok 47 u -> ectwisti u = ectwistt (ti2t 47 u).
Proof.
move=> uok.
have bE y : (to_nat y < 48)%N -> bitc y = (to_nat y \in cprim).
  by move=> yL; rewrite -bit_cmask ?to_natK.
have blt c : (c < 48)%N -> (to_nat (PArray.get u (of_nat c)) < 48)%N.
  by move=> cL; apply: tabi_lt.
rewrite /ectwisti /ectwistt /=.
have of_posE n : of_pos n = of_nat (BinPos.Pos.to_nat n).
  by rewrite Znat.positive_nat_Z.
by rewrite !of_posE -[(get u 0)]/(get u (of_nat 0)) !bE //; apply: blt.
Qed.

Lemma ctwistiE a : tabi_ok 47 a -> ctwisti a = ctwistt (ti2t 47 a).
Proof. Admitted.

(* list -> permutation, mirroring Coordfsi.coordtE *)
Lemma ctwisttE t : tab_ok 47 t -> coordtw (pt 47 t) = ctwistt t.
Proof. Admitted.

(* twist (g * m) depends only on (twist g, m).  Checked by BFS in OCaml over
   all 2187 values and all 18 moves -- and over all 256 chirality choices,
   which is why ctrip's cyclic order needed no convention. *)
Lemma coordtw_step (g : {perm facelet}) (k : nat) : (k < 18)%N ->
  coordtw (g * pt 47 (nth [::] mtabs k)) = acttw (coordtw g) k.
Proof. Admitted.

(* -- the fold is sound: conjugate states land in the same slot ------------- *)

(* u must not only be a symmetry (Symg_stab, so it permutes the moves and
   preserves the distance) but must also ACT on the flip x slice coordinate,
   which is what fspres asks: it maps slice edges to slice edges and primary
   facelets to primary facelets.  Exactly 16 of the 48 do -- measured, and
   dropping fspres is precisely the error the header describes. *)
Definition fspres (u : {perm facelet}) : bool :=
  [forall f : facelet, (scol (u f) == scol f) && (pcol (u f) == pcol f)].

Lemma p1idx_sym (g u : {perm facelet}) : u \in Symg -> fspres u ->
  p1idx (coordtw (g ^ u)) (coordfs (g ^ u)) = p1idx (coordtw g) (coordfs g).
Proof. Admitted.

(* -- the local certificate ------------------------------------------------ *)

Lemma Dp1_0 : Dp1 (coordtw 1) (coordfs 1) = 0%N.
Proof. Admitted.

Lemma Dp1_step (g : {perm facelet}) (k : nat) : (k < 18)%N ->
  (Dp1 (coordtw g) (coordfs g) <=
   (Dp1 (coordtw (g * pt 47 (nth [::] mtabs k)))
        (coordfs (g * pt 47 (nth [::] mtabs k)))).+1)%N.
Proof. Admitted.

(* =========================================================================  *)
(*  6.  Still to build (code, not proof)                                      *)
(*                                                                            *)
(*  - acttw, the 2187 x 18 twist move table, alongside Coordfsi's actf         *)
(*  - the generator: BFS over the folded phase 1 space, emitting srank,        *)
(*    fsclass, twconj and p1tab as Rocq literals                               *)
(*  - Far.v's searchz5 carries five flip x slice coordinates; it must carry    *)
(*    five twists as well, and h5 becomes a max of five Dp1                    *)
(* =========================================================================  *)
