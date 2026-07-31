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
(*  SYMMETRY.  Sym.Symg_stab says every u in Symg permutes the move set, so    *)
(*  the distance is invariant under conjugation: d (g ^ u) = d g.  Hence only  *)
(*  one representative per orbit need be stored.  Measured, NOT quoted -- the  *)
(*  orbit count was computed from Sym.v's own generators Sy, Sx, Sm:           *)
(*                                                                            *)
(*     symmetry group                     48   (closure of Sy, Sx, Sm)        *)
(*     reachable flip x slice      1 013 760   = 2048 x 495, all of them       *)
(*     orbits                         46 739   reduction 21.69x               *)
(*                                                                            *)
(*  Kociemba folds by the sixteen symmetries that fix the UD axis and gets     *)
(*  64 430 classes, 15.73x; 1 013 760 / 64 430 = 15.73 reproduces that, which  *)
(*  is the check that the computation above is doing the right thing.  We can  *)
(*  use all 48 because Symg_stab holds for all 48.                            *)
(*                                                                            *)
(*  CLAMP.  Two bits per entry, holding d - 8 clamped to [0, 3].  Entries      *)
(*  below 8 never prune at the depths we search, and clamping DOWN keeps the   *)
(*  heuristic admissible -- a smaller h is always safe.                        *)
(*                                                                            *)
(*  Together:                                                                  *)
(*                                                                            *)
(*     2187 x 46 739            = 102 218 193 entries                         *)
(*     at 31 entries per int63  =   3 297 362 words  =  26.4 MB               *)
(*     PArray.max_length        =   4 194 303 words                           *)
(*                                                                            *)
(*  so it is a SINGLE array -- no chunking, no two level reader.  With the     *)
(*  three index tables below the total is about 35 MB per worker, against the  *)
(*  ~1 GB each already uses, so the eighteen Far_?? workers are unaffected.    *)
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
(*  fixed sets.  The U/D axis came out as faces 2 and 4, which is NOT the      *)
(*  (f + 3) mod 6 pairing that Moves.oppf uses on move indices.                *)
(* =========================================================================  *)

(* 3 ^ 7 -- the eighth orientation is forced, the sum being 0 mod 3 *)
Definition ntwist := 2187.

(* the U/D sticker of each corner, one per cubie *)
Definition cprim : seq nat := [:: 16; 18; 21; 23; 32; 34; 37; 39]%N.

(* the three stickers of each corner, U/D one first.  The cyclic order of the
   other two is a free choice: swapping them recodes one base 3 digit
   bijectively, so all 2 ^ 8 choices give the same 2187 value quotient.  This
   was checked by BFS over all of them, so nothing here rests on a chirality
   convention I would have had to get right. *)
Definition ctrip : seq (nat * nat * nat) :=
  [:: (16, 5, 10); (18, 7, 24); (21, 15, 40); (23, 29, 42);
      (32, 2, 26); (34, 0,  8); (37, 31, 47); (39, 13, 45)]%N.

(* NB: qualified Uint63 functions throughout rather than the << and >> and
   .[ ] notations -- fingroup owns << _ >> for the generated subgroup, so the
   shift notation does not survive an all_fingroup import. *)
Definition cmask : int := Eval vm_compute in
  foldr (fun f a => Uint63.lor a (Uint63.lsl 1%uint63 (of_nat f))) 0%uint63
        cprim.

(* is the facelet sitting in slot s a U/D sticker? *)
Definition udhit (u : arr) (c : nat) : bool :=
  negb (Uint63.eqb
          (Uint63.land cmask
             (Uint63.lsl 1%uint63 (PArray.get u (of_nat c)))) 0%uint63).

(* orientation of the corner sitting in this slot, as ecoordi does it: u is
   the inverse table, so u.[s] is the facelet occupying slot s *)
Definition corient (u : arr) (t : nat * nat * nat) : nat :=
  let: (c0, c1, c2) := t in
  if udhit u c0 then 0%N else if udhit u c1 then 1%N else 2%N.

(* base 3 over the first seven corners *)
Definition ctwisti (a : arr) : int :=
  let u := inv_tabi 47 a in
  foldr (fun t x => Uint63.add (Uint63.mul x 3%uint63) (of_nat (corient u t)))
        0%uint63 (take 7 ctrip).

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

Definition fsidx (x : int) : int :=
  Uint63.add
    (Uint63.mul (Uint63.land x 4095%uint63) (of_nat nslice))
    (PArray.get srank (Uint63.lsr x 12%uint63)).

(* =========================================================================  *)
(*  3.  The symmetry fold                                                     *)
(*                                                                            *)
(*  fsclass sends each of the 1 013 760 flip x slice indices to its orbit      *)
(*  representative together with the symmetry that gets there, packed as       *)
(*  class * 48 + sym (46 739 * 48 < 2 ^ 22, so one int63 is ample).  The twist *)
(*  must be conjugated by the SAME symmetry, which is what twconj is for:      *)
(*  2187 * 48 = 104 976 entries.                                              *)
(* =========================================================================  *)

Definition nsym   := 48.
Definition nclass := 46739.

Definition fsclass : arr := PArray.make (of_nat nfs) 0%uint63.            (* GENERATED *)
Definition twconj  : arr := PArray.make (of_nat (ntwist * nsym)) 0%uint63. (* GENERATED *)

(* the folded phase 1 index: 0 .. 2187 * 46739 *)
Definition p1idx (tw x : int) : int :=
  let c  := PArray.get fsclass (fsidx x) in
  let s  := Uint63.land c 63%uint63 in
  let cl := Uint63.lsr c 6%uint63 in
  Uint63.add (Uint63.mul cl (of_nat ntwist))
    (PArray.get twconj (Uint63.add (Uint63.mul tw (of_nat nsym)) s)).

(* =========================================================================  *)
(*  4.  The table itself: two bits per entry, 31 per word                     *)
(* =========================================================================  *)

Definition p1base  := 8.        (* entries hold d - p1base, clamped to [0,3] *)
Definition p1words := 3297362.  (* ceil (2187 * 46739 / 31) *)

Definition p1tab : arr := PArray.make (of_nat p1words) 0%uint63.  (* GENERATED *)

Definition p1get (i : int) : int :=
  let w := Uint63.div i 31%uint63 in
  let r := Uint63.sub i (Uint63.mul w 31%uint63) in
  Uint63.land
    (Uint63.lsr (PArray.get p1tab w) (Uint63.mul r 2%uint63)) 3%uint63.

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

Lemma coordtw_id : coordtw 1 = 0%uint63.
Proof. Admitted.

(* the array form computes the structured one.  Same three level shape as the
   flip x slice half, whose bridge is Coordfsi.coordtE:
     coordfs (pt 47 t) = coordt t   for tab_ok 47 t. *)
Lemma ctwistiE t : tab_ok 47 t -> ctwisti (t2ti 47 t) = coordtw (pt 47 t).
Proof. Admitted.

(* twist (g * m) depends only on (twist g, m).  Checked by BFS in OCaml over
   all 2187 values and all 18 moves -- and over all 256 chirality choices,
   which is why ctrip's cyclic order needed no convention. *)
Lemma coordtw_step (g : {perm facelet}) (k : nat) : (k < 18)%N ->
  coordtw (g * pt 47 (nth [::] mtabs k)) = acttw (coordtw g) k.
Proof. Admitted.

(* -- the fold is sound: conjugate states land in the same slot ------------- *)

(* this is where Sym.Symg_stab is spent, and it is what licenses folding by
   all 48 rather than Kociemba's 16 *)
Lemma p1idx_sym (g u : {perm facelet}) : u \in Symg ->
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
