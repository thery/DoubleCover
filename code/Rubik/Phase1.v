(* =========================================================================  *)
(*  Phase1.v -- the phase 1 heuristic, its table, and its certificate.        *)
(*                                                                            *)
(*  The flip x slice table Far.v ships today is 2 ^ 24 entries and caps the    *)
(*  heuristic at 9.  Phase 1 -- twist x flip x slice -- caps at 12, which is   *)
(*  what a depth 19 search needs.  The raw space is                           *)
(*                                                                            *)
(*     2187 twist  x  2048 flip  x  495 slice  =  2 217 093 120 states        *)
(*                                                                            *)
(*  UNFOLDED, one slot per state, exactly as ocaml/rubik_par.ml has it.  The  *)
(*  point of this file is to MIMIC that program, whose depth 19 run is the     *)
(*  computational content of Diameter.v's superflip_far: 104 561 988 516       *)
(*  nodes, 24.0 CPU-hours.                                                    *)
(*                                                                            *)
(*     2 217 093 120 entries                                                  *)
(*     4 bits each, 15 per int63  =  147 806 208 words  =  1.18 GB            *)
(*     PArray.max_length          =    4 194 303 words                        *)
(*                                                                            *)
(*  so the table is a PArray of 71 PArrays, split on the word index at a       *)
(*  power of two (w >> cwlog), which stays definitional -- the trick Fspar.v's *)
(*  cbits uses.                                                               *)
(*                                                                            *)
(*  WHY NOT FOLDED.  The 16 symmetries that act on the flip x slice           *)
(*  coordinate would collapse 1 013 760 values to 64 430 -- measured 15.73x,   *)
(*  independently reproducing Kociemba's published number -- taking the table  *)
(*  to 36.4 MB and the certificate with it.  It is not done here because the   *)
(*  fold needs a soundness lemma of its own (conjugate states must land in     *)
(*  the same slot) that the unfolded table simply does not have.  Mimic        *)
(*  first; fold later if the size bites.  Measured cost of not folding: about  *)
(*  8 GB per worker, capping roquableu at ~6 parallel workers rather than 18.  *)
(*  (If it is ever folded, note that only 16 of the 48 symmetries act on the   *)
(*  coordinate -- a u that moves the UD slice does not act on it at all, so    *)
(*  "the orbit of a coordinate" is not even well defined for the other 32.)    *)
(*                                                                            *)
(*  CLAMP.  Entries hold the true distance, capped ABOVE at p1cap + 1 by       *)
(*  stopping the BFS -- never an offset clamped from below.  Storing d - base  *)
(*  and clamping the underflow to 0 reports base for a state that is really    *)
(*  nearer, which OVERstates the distance and can prune a real solution.       *)
(*                                                                            *)
(*  THE TABLE IS GENERATED AND VALIDATED.  bench/p1gen.ml builds it in the     *)
(*  Rocq coordinate in ~2 min and agrees with rubik_par at every BFS level     *)
(*  (4, 50, 592, 7156, 87236, 1043817, 12070278, 124946368, 821605960) and     *)
(*  node for node in the search (2102, 25598, 340658 at depths 12, 13, 14).    *)
(*  Two programs on two different cube models.                                *)
(*                                                                            *)
(*  It is never asked to be CORRECT: p1check0 and p1checkStep make it a local  *)
(*  certificate, so the generator is not in the trusted base.                  *)
(*                                                                            *)
(*  WHAT IS STILL MISSING is the proofs and the generated data.  See the       *)
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

(* acttw is COMPUTED from the move, exactly as Coordfs.actfs is, and NOT a
   generated table.  That is the whole point: coordfs (g * m) = actfs (coordfs
   g) m needs no data, and the twist must be able to say the same.  A table
   would make coordtw_step a statement about emitted numbers.

   The corner analogue of Coordfs's epos / eprimf / src / xbit: a corner
   facelet belongs to a cubie (cpos) and sits in one of its three slots
   (cslot), the U/D slot being slot 0.  A move sends the U/D slot of corner p
   to some slot of some corner, and that pair IS the action on the digit. *)

(* the 24 corner facelets, grouped by cubie, U/D sticker first *)
Definition cflat : seq nat :=
  flatten [seq [:: t.1.1; t.1.2; t.2] | t <- ctrip].

Definition cpos  (f : facelet) : nat := (index (f : nat) cflat) %/ 3.
Definition cslot (f : facelet) : nat := (index (f : nat) cflat) %% 3.

(* the U/D slot of corner position p *)
Definition cprimf (p : nat) : facelet := inord (nth 0%N cprim p).

(* which corner arrives at p, and how far it is rotated when it gets there *)
Definition csrc   (m : {perm facelet}) (p : nat) : nat := cpos  (m^-1 (cprimf p)).
Definition cdelta (m : {perm facelet}) (p : nat) : nat := cslot (m^-1 (cprimf p)).

(* 3 ^ 0 .. 3 ^ 7 as int63 LITERALS: of_nat on a unary nat is O(n) *)
Definition pow3 : seq int := [:: 1; 3; 9; 27; 81; 243; 729; 2187]%uint63.

(* digit p of the base 3 coordinate; digit p has weight 3 ^ p *)
Definition dig3i (x : int) (p : nat) : int :=
  Uint63.mod (Uint63.div x (nth 1%uint63 pow3 p)) 3%uint63.

(* the eighth orientation is not stored: the eight sum to 0 mod 3 *)
Definition dig8i (x : int) : int :=
  Uint63.mod
    (Uint63.sub 3%uint63
       (Uint63.mod (foldr (fun p a => Uint63.add a (dig3i x p)) 0%uint63
                          (iota 0 7)) 3%uint63))
    3%uint63.

Definition digi (x : int) (p : nat) : int :=
  if p == 7 then dig8i x else dig3i x p.

(* =========================================================================  *)
(*  Base 3 digits -- the analogue of Coordfs's packn / nbit                    *)
(*                                                                            *)
(*  Everything here is on nat.  The values are below 3 ^ 7 = 2187, nowhere    *)
(*  near overflow, so the int63 side is reached once at the end rather than   *)
(*  carried through every lemma.                                             *)
(* =========================================================================  *)

Fixpoint pack3n (k : nat) (f : nat -> nat) : nat :=
  if k is k1.+1 then pack3n k1 f + (f k1 %% 3) * 3 ^ k1 else 0.

Definition dig3n (x j : nat) : nat := (x %/ 3 ^ j) %% 3.

Lemma pack3n_lt k f : (pack3n k f < 3 ^ k)%N.
Proof.
elim: k => [|k IH]; first by rewrite expn0.
have h3 : (f k %% 3 < 3)%N by rewrite ltn_mod.
apply: leq_ltn_trans (_ : pack3n k f + 2 * 3 ^ k < _)%N.
  by rewrite leq_add2l leq_mul2r -ltnS h3 orbT.
have h : (3 ^ k.+1 = 3 ^ k + 2 * 3 ^ k)%N.
  by rewrite expnS (_ : 3 = 1 + 2)%N // mulnDl mul1n.
by rewrite h ltn_add2r.
Qed.

Lemma dig3n_pack3n k f j : (j < k)%N -> dig3n (pack3n k f) j = f j %% 3.
Proof.
elim: k j => [//|k IH] j; rewrite ltnS leq_eqVlt => /orP[/eqP->|jL].
  rewrite /dig3n /= addnC divnMDl ?expn_gt0 //.
  by rewrite divn_small ?pack3n_lt // addn0 modn_mod.
have HH : (j <= k)%N := ltnW jL.
rewrite /dig3n /= divnDr; last by apply: dvdn_mull; apply: dvdn_exp2l.
(* the third k is the exponent; the first two are pack3n k f and f k *)
rewrite -{3}(subnK HH) expnD mulnA mulnK ?expn_gt0 //.
have h3 : (3 %| (f k %% 3) * 3 ^ (k - j))%N.
  by apply: dvdn_mull; rewrite -{1}(expn1 3) dvdn_exp2l // subn_gt0.
rewrite -modnDmr (eqP h3) addn0.
by move: (IH _ jL); rewrite /dig3n => ->.
Qed.

(* THE PROOF SIDE.  Computed from the move, so coordtwM is a theorem about the
   moves and not about emitted numbers. *)
Definition acttw (x : int) (m : {perm facelet}) : int :=
  foldr (fun p a =>
           Uint63.add (Uint63.mul a 3%uint63)
             (Uint63.mod (Uint63.add (digi x (csrc m p)) (of_nat (cdelta m p)))
                         3%uint63))
        0%uint63 (iota 0 7).

(* THE COMPUTATION SIDE.  {perm facelet} is a 48-element finfun that neither
   vm_compute nor native_compute can touch, so the check cannot run acttw.
   It runs this instead -- a 2187 x 18 table, tiny next to the phase 1 table --
   and acttwiE ties the two together by a finite check over 39 366 entries.
   Exactly Fstab's actd / actf / actfE split, one level up. *)
Definition twmove : arr := PArray.make (of_nat (ntwist * 18)) 0%uint63. (* GENERATED *)

Definition acttwi (x : int) (k : nat) : int :=
  PArray.get twmove (Uint63.add (Uint63.mul x 18%uint63) (of_nat k)).

Lemma acttwiE x k : (k < 18)%N ->
  acttwi x k = acttw x (pt 47 (nth [::] mtabs k)).
Proof. Admitted.

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
(* the number of 12 bit masks with four bits set.  NOT Coordfs.nslice,
   which is 4, the number of slice edges. *)
Definition nsrank := 495.
Definition nfs    := 1013760.   (* nflip * nsrank *)

Definition srank : arr :=                                     (* GENERATED *)
  PArray.make 4096%uint63 (of_nat nsrank).

(* NB 2047, not 4095.  The flip occupies twelve bits but edge flip parity is
   even, so bit 11 is determined by bits 0..10 and only 2048 of the 4096 occur.
   Masking with 4095 indexes past the end of fsclass -- caught by running the
   generator on the flip x slice table, where it failed at once. *)
Definition fsidx (x : int) : int :=
  Uint63.add
    (Uint63.mul (Uint63.land x 2047%uint63) (of_nat nsrank))
    (PArray.get srank (Uint63.lsr x 12%uint63)).

(* =========================================================================  *)
(*  3.  The index, unfolded                                                   *)
(*                                                                            *)
(*  UNFOLDED, deliberately: one slot per state, exactly as ocaml/rubik_par.ml  *)
(*  has it.  The 16-symmetry fold would shrink the table 15.73x and the        *)
(*  certificate with it, but it needs a soundness lemma of its own (conjugate  *)
(*  states land in the same slot) that the unfolded table does not.  Mimic     *)
(*  first, fold later if the size bites.  Measured cost of not folding: about  *)
(*  8 GB per worker, which caps roquableu at ~6 parallel workers rather than   *)
(*  18.  Nothing else about the development changes.                          *)
(* =========================================================================  *)

(* nfs and ntwist as int63 LITERALS, not as of_nat applied to the nat.
   of_nat is O(n) on a unary nat, so of_nat nfs is a million reduction steps --
   fine once, ruinous inside a loop the kernel runs 4 * 10 ^ 10 times, and it
   is also what makes `case: ifP` on the guard below diverge. *)
Definition nfsi    : int := 1013760%uint63.
Definition ntwisti : int := 2187%uint63.

(* NB no `to_nat nfsi = nfs` lemma: proving it materialises nfs as a unary nat
   and overflows the stack.  Everything below stays on the int63 side. *)

Definition p1idx (tw x : int) : int :=
  Uint63.add (Uint63.mul tw nfsi) (fsidx x).

(* =========================================================================  *)
(*  4.  The table itself: four bits per entry, fifteen per word               *)
(*                                                                            *)
(*  FOUR bits, holding the true distance capped at p1cap + 1 -- never an       *)
(*  offset clamped from below.  Storing d - base and clamping the underflow    *)
(*  to zero reports base for a state that is really nearer, which OVERstates   *)
(*  the distance and is not an admissible heuristic; it can prune away a real  *)
(*  solution.  Clamping from ABOVE is the safe direction, and that is exactly  *)
(*  what stopping the BFS at p1cap does.                                      *)
(* =========================================================================  *)

Definition p1cap     := 9.            (* the BFS stops here, as rubik_par does *)
Definition p1entries := 2217093120.   (* ntwist * nfs                          *)
Definition p1words   := 147806208.    (* ceil (p1entries / 15)                 *)

(* p1words > PArray.max_length = 4 194 303, so the table is a PArray of
   PArrays.  The split is on the WORD index at a power of two, w >> cwlog,
   which stays definitional -- the same trick Fspar.v's cbits uses. *)
Definition cwlog  := 21.
Definition nchunk := 71.

Definition p1tabs : PArray.array arr :=                           (* GENERATED *)
  PArray.make (of_nat nchunk) (PArray.make 1%uint63 0%uint63).

Definition p1get (i : int) : int :=
  let w := Uint63.div i 15%uint63 in
  let r := Uint63.sub i (Uint63.mul w 15%uint63) in
  let c := Uint63.lsr w (of_nat cwlog) in
  let o := Uint63.land w (Uint63.sub (Uint63.lsl 1%uint63 (of_nat cwlog))
                                     1%uint63) in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get p1tabs c) o) (Uint63.mul r 4%uint63))
    15%uint63.

(* the heuristic: the stored value, which IS the distance up to the cap *)
Definition Dp1i (tw x : int) : int := p1get (p1idx tw x).
Definition Dp1 (tw x : int) : nat := to_nat (Dp1i tw x).

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

(* Coordfsi.coordiE, one level up *)
Lemma ctwistiE a : tabi_ok 47 a -> ctwisti a = ctwistt (ti2t 47 a).
Proof.
move=> aok; rewrite /ctwisti /ctwistt ectwistiE.
  by rewrite (ti2t_inv n47_small n47_len aok).
by rewrite /tabi_ok (ti2t_inv n47_small n47_len aok); apply: tab_ok_inv.
Qed.

(* list -> permutation, mirroring Coordfsi.coordtE *)
(* Coordfsi.coordtE, one level up *)
Lemma ctwisttE t : tab_ok 47 t -> coordtw (pt 47 t) = ctwistt t.
Proof.
move=> tok; have iok := tab_ok_inv tok.
have ilt c : (c < 48)%N -> (nth 0%N (inv_tab 47 t) c < 48)%N.
  move=> cL; have /and3P[/eqP sz /allP hall _] := iok.
  by apply: hall; rewrite mem_nth // sz.
have hval c : (c < 48)%N ->
    udcol ((pt 47 t)^-1 (inord c)) = (nth 0%N (inv_tab 47 t) c \in cprim).
  move=> cL; rewrite (ptV tok) ptE; last exact: iok.
  by rewrite /udcol (inordK cL) (inordK (ilt _ cL)).
(* the entries of ctrip are facelets *)
have hb : all (fun tr => ((tr.1.1 < 48) && (tr.1.2 < 48) && (tr.2 < 48))%N) ctrip.
  by vm_compute.
have hfold (F G : nat -> int -> int) l :
    (forall p x, F p x = G p x) -> foldr F 0%uint63 l = foldr G 0%uint63 l.
  by move=> h; elim: l => //= p l ->; rewrite h.
have hlist : take 7 ctrip = [seq nth (0, 0, 0)%N ctrip p | p <- iota 0 7] by [].
rewrite /coordtw /ctwistt /ectwistt hlist foldr_map.
(* hfold quantifies over every p, including p >= 8 where nth gives the
   default -- whose entries are 0, so the bound holds there too *)
move/(all_nthP (0, 0, 0)%N): hb => hb'.
have hsz : seq.size ctrip = 8 by [].
have hbp q : (((nth (0, 0, 0)%N ctrip q).1.1 < 48) &&
              ((nth (0, 0, 0)%N ctrip q).1.2 < 48))%N.
  have [qL|qL] := ltnP q 8.
    have qs : (q < seq.size ctrip)%N by rewrite hsz.
    by have /andP[/andP[-> ->] _] := hb' q qs.
  by rewrite nth_default ?hsz.
apply: hfold => p x; congr (Uint63.add _ _); congr (of_nat _).
rewrite /corientg /corientt.
have /andP[h0 h1] := hbp p.
case: (nth (0, 0, 0)%N ctrip p) h0 h1 => [[c0 c1] c2] h0 h1.
by rewrite (hval _ h0) (hval _ h1).
Qed.

(* the corner analogue of Coordfs's epair: where an edge's two stickers are
   swapped by an involution, a corner's three are rotated by a 3-cycle.  A
   permutation "moves cubies rigidly" exactly when it commutes with it, and
   that is the guard coordtwM needs -- Coordfs.cubP one level up. *)
Definition Ccyc : seq (seq facelet) :=
  [seq [:: inord t.1.1; inord t.1.2; inord t.2] | t <- ctrip].

Definition ccyc : {perm facelet} := \prod_(l <- Ccyc) cyc l.

Definition cubcP (g : {perm facelet}) : bool :=
  [forall f : facelet, ccyc (g f) == g (ccyc f)].

(* Coordfs.coordfsM transposed.  With acttw computed rather than tabled this
   is a theorem about the moves, not about emitted numbers. *)
Lemma coordtwM g m :
  cubcP g -> cubcP m -> coordtw (g * m) = acttw (coordtw g) m.
Proof. Admitted.

(* the form the search uses *)
Lemma coordtw_step (g : {perm facelet}) (k : nat) : (k < 18)%N ->
  cubcP g ->
  coordtw (g * pt 47 (nth [::] mtabs k)) =
  acttw (coordtw g) (pt 47 (nth [::] mtabs k)).
Proof. Admitted.

(* =========================================================================  *)
(*  6.  THE CHECK                                                             *)
(*                                                                            *)
(*  The table is never asked to be CORRECT, only to be a local certificate:    *)
(*  zero at the identity, and never dropping by more than one across a move.   *)
(*  Those two facts alone make the heuristic admissible, and both are decided  *)
(*  by a closed boolean the kernel evaluates.  Exactly Fstab.v's check0 /      *)
(*  checkStep, one level up.                                                  *)
(*                                                                            *)
(*  WHY THE LOOP IS OVER RANKS.  Only 1 013 760 of the 2 ^ 24 packed flip x    *)
(*  slice values occur -- 6 % -- so iterating over packed values would do      *)
(*  sixteen times the work.  unranki turns a rank back into a packed value,    *)
(*  and p1checkUnrank is what makes that legitimate.                          *)
(*                                                                            *)
(*  WHY p1mdata IS HOISTED.  Fstab.v measured this: with the move data built   *)
(*  inside the lambda it is rebuilt per state, 26 ms against 79 us -- ninety   *)
(*  days against seven hours.  Here the loop is 132 times longer still.       *)
(* =========================================================================  *)

Definition p1mdata : seq (nat * mdatf) :=
  [seq (k, mdatf_of_tab (nth [::] mtabs k)) | k <- iota 0 18].

(* THE LOOP RUNS OVER PACKED VALUES, NOT OVER RANKS, and that is deliberate.
   Ranking first would be 16x fewer iterations, but then the checked instance
   is at unranki (fsidx x) rather than at x, and closing the gap needs fsidx
   to be injective on the summaries -- a real obligation, and one Coordfs does
   not currently provide.  Over packed values, all_powP hands back the
   instance at x itself and the proof is Fstab.DfsStep_of_check verbatim.
   Measured cost of the choice: the extra sweep is ~5 % on top of the move
   checks, which dominate either way.

   The fsidx guard is NOT cosmetic: without it every one of the 2 ^ 24 packed
   values would run the eighteen move checks instead of the 6 % that are
   summaries, which is sixteen times the work. *)
Definition p1stepF (tw : int) : int -> bool :=
  let md := p1mdata in
  fun x =>
    if (nfsi <=? fsidx x)%uint63 then true
    else all (fun km => (Dp1i tw x <=?
                incr (Dp1i (acttwi tw km.1) (actf x km.2)))%uint63) md.

Definition p1checkTw (tw : int) : bool := all_pow ncoord 0%uint63 (p1stepF tw).

Definition p1checkStep : bool :=
  all (fun t => p1checkTw (of_nat t)) (iota 0 ntwist).

(* An EQUATION, not a delta step.  Any conversion that has to see through
   p1checkTw lets the kernel unfold the all_pow fixpoint at ncoord = 24, i.e.
   2 ^ 24 conjuncts: applying all_powP to p1checkTw tw directly loops in the
   tactic, `rewrite /p1checkTw in htw` loops at Qed, and even a definitional
   coercion loops in elaboration.  Rewriting with this lemma is an eq_ind with
   a small motive and does not. *)
Lemma p1checkTwE tw : p1checkTw tw = all_pow ncoord 0%uint63 (p1stepF tw).
Proof. by rewrite /p1checkTw. Qed.

Definition p1check0 : bool :=
  (Dp1i (ctwistt (id_tab 47)) (coordt (id_tab 47)) =? 0)%uint63.

(* -- the split for parallel checking --------------------------------------- *)

(* The outer loop is an all over iota, not an all_pow, so splitting it is
   cat_take_drop and all_cat -- no all_pow_glue16 needed.  That is the one
   place this is EASIER than the flip x slice certificate: 2187 twists cut
   into as many slices as there are cores, each its own file. *)
Lemma p1checkStep_split n :
  all (fun t => p1checkTw (of_nat t)) (take n (iota 0 ntwist)) ->
  all (fun t => p1checkTw (of_nat t)) (drop n (iota 0 ntwist)) ->
  p1checkStep.
Proof.
by rewrite /p1checkStep -{3}(cat_take_drop n (iota 0 ntwist)) all_cat => -> ->.
Qed.

Lemma p1checkStep_of_slices (s : seq nat) :
  s = iota 0 ntwist ->
  all (fun t => p1checkTw (of_nat t)) s -> p1checkStep.
Proof. by move=> ->. Qed.

(* -- what the two checks buy ---------------------------------------------- *)

(* These are the point of the file.  A table passing them is a valid
   heuristic, whatever it actually contains. *)

(* coordtw 1 does not compute, being about a permutation; the identity table
   is its computable form, by pt1 and ctwisttE -- exactly Fstab's coordfs1E *)
Lemma coordtw1E : coordtw 1 = ctwistt (id_tab 47).
Proof. by rewrite -(ctwisttE (tab_ok_id 47)) pt1. Qed.

Lemma Dp1_0_of_check : p1check0 -> Dp1 (coordtw 1) (coordfs 1) = 0%N.
Proof.
rewrite /p1check0 /Dp1 /Dp1i coordtw1E coordfs1E.
by move=> /eqb_correct ->; rewrite to_nat_0.
Qed.

(* NO Dp1_oob ANALOGUE, and the reason matters.  Fstab gets Dfs_oob because a
   coordinate past 2 ^ ncoord indexes past the table.  Here p1idx tw x is
   tw * nfs + fsidx x, so fsidx x >= nfs does NOT leave the table -- it lands
   in the NEXT twist's block and reads a perfectly good entry for a different
   state.  So the fsidx guard in p1stepF is not free: it has to be discharged,
   not absorbed.

   That is what fsidx_lt is for.  It is a fact about the summaries, not about
   the table: the flip half is eleven bits and the slice half is a mask with
   exactly four bits set, so fsidx lands below 2048 * 495.  It belongs in
   Coordfs, which owns both halves; it is stated here until it moves. *)
Lemma fsidx_lt (g : {perm facelet}) : (fsidx (coordfs g) <? nfsi)%uint63.
Proof. Admitted.

(* the entries are four bits, so the successor on the int side is the
   successor on the nat side -- no wrap.  Fstab.Dfsi_small verbatim. *)
Lemma Dp1i_small tw x : (to_nat (Dp1i tw x) < nwB.-1)%N.
Proof.
rewrite /Dp1i /p1get.
set v := (X in (X land _)%uint63); rewrite landC.
apply: ltn_trans (_ : 2 ^ 4 < _); last first.
  rewrite -ltnS prednK; last by apply: ltn_trans ndigitsLwB.
  by apply: ltn_trans ndigitsLwB.
by apply: to_nat_land_bound.
Qed.

(* nfs < nwB, needed to move of_nat across the fsidx guard.  Proved the way
   ssrint63.ndigitsLwB is -- bound by a power of two, then nwB_pow -- because
   `by []` on a `_ < nwB` goal is the unary trap: 2 ^ 63 in successors. *)
Lemma nfsB : (nfs < nwB)%N.
Proof.
apply: leq_ltn_trans (_ : (2 ^ 20)%N < _); first by vm_compute.
by rewrite nwB_pow ltn_exp2l.
Qed.

(* STATED ON COORDINATES, not on g -- exactly Fstab.DfsStep_of_check.  The
   guard cubP that coordfs's coordM needs never appears here, and the step to
   g is taken later, where coordtw_step and coordM are applied together. *)
(* -- small facts about the move tables, hoisted so each gets its own Qed --- *)

Lemma mtabs_size : seq.size mtabs = 18.
Proof. by []. Qed.

Lemma nth_mtabs_ok k : (k < 18)%N -> tab_ok 47 (nth [::] mtabs k).
Proof.
by move=> kL; apply: (allP mtabs_ok); apply: mem_nth; rewrite mtabs_size.
Qed.

Lemma nth_moves_pt k : (k < 18)%N -> nth 1%g moves k = pt 47 (nth [::] mtabs k).
Proof. by move=> kL; rewrite mtabsE (nth_map [::]) ?mtabs_size. Qed.

(* the move as a permutation and the move as packed data agree *)
Lemma actfs_actfE x k : (k < 18)%N ->
  actfs x (nth 1%g moves k) = actf x (mdatf_of_tab (nth [::] mtabs k)).
Proof.
move=> kL; rewrite nth_moves_pt // actfE.
by apply: actdE; apply: nth_mtabs_ok.
Qed.

(* split in two so the Qeds are separate: getting the checked instance out of
   the loop, and then reading the k-th move out of it *)
Lemma p1stepF_of_check tw x :
  p1checkStep -> (to_nat tw < ntwist)%N -> (to_nat x < 2 ^ ncoord)%N ->
  p1stepF tw x.
Proof.
rewrite /p1checkStep => hcheck twL xL.
have htw : p1checkTw tw.
  move/allP: hcheck => /(_ (to_nat tw)).
  by rewrite mem_iota /= twL to_natK; apply.
rewrite p1checkTwE in htw.
exact: (all_powP ncoord_dig htw xL).
Qed.

Lemma p1checkStep_inst tw x k :
  p1stepF tw x -> (fsidx x <? nfsi)%uint63 -> (k < 18)%N ->
  (Dp1i tw x <=?
   incr (Dp1i (acttwi tw k) (actf x (mdatf_of_tab (nth [::] mtabs k)))))%uint63.
Proof.
move=> hall fsL kL.
(* the guard, settled on its own and entirely in int63 *)
have hcond : (nfsi <=? fsidx x)%uint63 = false.
  apply/idP => /nlebP h1; move/nltbP: fsL => h2.
  by rewrite leqNgt h2 in h1.
move: hall; rewrite /p1stepF hcond => hstep.
move: hstep => /(all_nthP (0%N, mdatf_of_tab [::])).
rewrite size_map size_iota => /(_ k kL).
(* nth_map_iota, not nth_map + nth_iota: with the length a literal the
   latter pair makes the iota compute and unfolds the whole list. *)
by rewrite (nth_map_iota _ _ kL).
Qed.

Lemma Dp1_step_of_check :
  p1checkStep ->
  forall tw x k, (to_nat tw < ntwist)%N -> (to_nat x < 2 ^ ncoord)%N ->
  (fsidx x <? nfsi)%uint63 -> (k < 18)%N ->
  (Dp1 tw x <=
   (Dp1 (acttwi tw k) (actfs x (nth 1%g moves k))).+1)%N.
Proof.
move=> hcheck tw x k twL xL fsL kL.
have F := p1checkStep_inst (p1stepF_of_check hcheck twL xL) fsL kL.
by rewrite (actfs_actfE _ kL) /Dp1; apply: leb_incr_le; last exact: Dp1i_small.
Qed.

(* Notes kept from the attempt: three causes found and fixed getting here,
   each worth a day if rediscovered.

     - htw must be UNFOLDED (rewrite /p1checkTw in htw) before all_powP, or
       unification expands all_pow ncoord into 2 ^ 24 conjuncts;
     - nfs must appear as the int63 literal nfsi, never as of_nat nfs.
       of_nat is O(n) on a unary nat, so of_nat nfs is a million reduction
       steps -- and the kernel would pay it inside a 4 * 10 ^ 10 loop;
     - to_nat nfsi = nfs cannot be proved at all: it materialises the unary
       nat and overflows the stack.  Hence the fsidx bound is stated in
       int63, as fsidx x <? nfsi.

   And the guard itself, which is what actually blocked: from
   fsL : (fsidx x <? nfsi) show (nfsi <=? fsidx x) = false.  case: ifP on the
   unfolded p1stepF and case E : on the bare condition both fail to return;
   apply/idP/negP to put both inequalities in the context, then nlebP/nltbP
   to move to nat and leqNgt to close, is thery's route and is instant.   *)

(* =========================================================================  *)
(*  6.  Still to build (code, not proof)                                      *)
(*                                                                            *)
(*  - acttw, the 2187 x 18 twist move table, alongside Coordfsi's actf         *)
(*  - the generator: BFS over the folded phase 1 space, emitting srank,        *)
(*    fsclass, twconj and p1tab as Rocq literals                               *)
(*  - Far.v's searchz5 carries five flip x slice coordinates; it must carry    *)
(*    five twists as well, and h5 becomes a max of five Dp1                    *)
(* =========================================================================  *)
