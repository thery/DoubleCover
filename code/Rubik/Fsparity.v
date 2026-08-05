(* =========================================================================  *)
(*  Fsparity.v                                                                   *)
(*                                                                            *)
(*  What makes a packed value a genuine flip x slice summary, and why a move  *)
(*  preserves it.  Split out of Farp1.v so it can be developed on its own:    *)
(*  Farp1.v takes over 290 s to elaborate interactively, which is longer than *)
(*  an rocq-mcp session will wait.                                            *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- 3bis.  What makes a packed value a genuine summary ------------------ *)

(* THE GUARD `fsidx x <? nfsi' IS NOT ENOUGH, AND THE THREE CERTIFICATES OF
   SECTION 5 WERE FALSE WITH IT.  Two packed values can share a rank without
   moving alike, for two separate reasons:

   - srank returns nsrank = 495 both for a twelve bit mask WITHOUT four bits
     set and as the array default, so for those fsidx x = (f + 1) * 495 --
     which is BELOW nfsi = 2048 * 495 for every f < 2047.  COUNTED: 495 of
     the 4096 masks are genuine and 3601 are not, so the old guard admits
     8 385 007 of the 2 ^ 24 rather than the 1 013 760 summaries.  The
     comment claiming it "leaves only the 6 %" was wrong by 8.3x.

   - fsidx masks the flip with 2047, not 4095, because bit 11 is the parity
     of the other eleven for a real cube -- Phase1.v says exactly that where
     fsidx is defined.  But actf moves all twelve bits.  MEASURED: at
     c0 = coordt (id_tab 47) and c1 = c0 lxor 2048, fsidx c0 = fsidx c1, yet
     after the fourth move the two ranks are 300 and 8220.

   fsok asks for both, and admits exactly nflip * nsrank = nfs values -- the
   count the emitted tables have a row for.  Fixing it is therefore a
   soundness fix AND the largest saving available on the certificate. *)

(* fpar, sok and fsok are DEFINED IN Phase1.v, next to fsidx: p1stepF there
   needs the guard, and this file requires Phase1, not the other way round.
   What is here is everything that has to be PROVED about them. *)

(* the old bound, where the old bound is what is wanted *)
Lemma fsok_lt x : fsok x -> (fsidx x <? nfsi)%uint63.
Proof.
move=> /andP[hs _]; apply: fsidx_ltB.
by have := nltbP _ _ hs; rewrite (_ : to_nat nsranki = nsrank) //; vm_compute.
Qed.

(* odd (count _) is a sum in F2, so a pointwise xor splits *)
Lemma odd_count_addb (T : Type) (f g : T -> bool) (s : seq T) :
  odd (count (fun k => f k (+) g k) s) = odd (count f s) (+) odd (count g s).
Proof.
elim: s => [|a s IH] //=; rewrite !oddD IH.
by case: (f a); case: (g a); case: (odd (count f s)); case: (odd (count g s)).
Qed.

(* THE TWO FACTS ABOUT THE MOVES the parity invariant rests on: each move
   permutes the twelve edges, and flips an EVEN number of them.  Both are
   finite, so both are checked rather than argued. *)
Definition mtabs_fpar : bool :=
  all (fun mt => perm_eq (msrc mt) (iota 0 nedge)
                 && ~~ odd (count id (mxbit mt))) mtabs.

Lemma mtabs_fparP : mtabs_fpar.
Proof. by vm_compute. Qed.

(* the flip half of actd is the flip half of x permuted, then xored with the
   move's own xbit vector, so the PARITY picks up only the second -- and that
   is a constant of the move, not of x *)
Lemma fpar_actd x d :
  perm_eq d.1 (iota 0 nedge) -> seq.size d.2 = nedge ->
  fpar (actd x d) = fpar x (+) odd (count id d.2).
Proof.
move=> hp hs; rewrite /fpar.
have hnb j : j \in iota 0 nedge ->
    nbit (actd x d) j = nbit x (nth 0%N d.1 j) (+) nth false d.2 j.
  rewrite mem_iota add0n => /andP[_ jL].
  rewrite /actd (nbit_packn _ (j := j)) //; first by rewrite jL.
  by apply: leq_trans jL (leq_addr _ _).
rewrite (eq_in_count hnb) odd_count_addb; congr (_ (+) _).
  rewrite -(seq.permP hp (nbit x)) -count_map.
  have hsz : seq.size d.1 = nedge by rewrite (perm_size hp) size_iota.
  by rewrite -hsz -/(mkseq _ _) mkseq_nth.
by rewrite -(count_map (nth false d.2) id) -hs -/(mkseq _ _) mkseq_nth.
Qed.

(* THE INVARIANT, at the int level: a move does not change the flip parity *)
Lemma fpar_actf x mt : mt \in mtabs ->
  fpar (actf x (mdatf_of_tab mt)) = fpar x.
Proof.
move=> hmt; rewrite actfE.
have /andP[hp hx] := allP mtabs_fparP _ hmt.
rewrite (fpar_actd x (mdat_of_tab mt) hp).
  by move: hx; rewrite mdat_snd; case: odd => //=; rewrite addbF.
by rewrite mdat_snd /mxbit size_map size_iota.
Qed.

(* the slice half of the guard, at a real cube.  REPLAYED from Phase1's
   fsidx_lt rather than factored out of it -- only because fsidx_lt runs the
   two facts together and this file wants the first alone.  It is NOT to
   avoid touching Phase1.v: P1_00.v .. P1_70.v require nothing but Uint63 and
   PArray, so they do not depend on Phase1 and editing it rebuilds proofs,
   not the five hours of data. *)
Lemma sok_coordfs g : cubP g -> sok (coordfs g).
Proof.
move=> cg; rewrite /sok; apply/nltbP.
rewrite (_ : to_nat nsranki = nsrank); last by vm_compute.
have hmem : to_nat (Uint63.lsr (coordfs g) 12%uint63) \in iota 0 nmask.
  by rewrite mem_iota add0n leq0n smask_lt.
have hcount : count (nbit (of_nat (to_nat (Uint63.lsr (coordfs g) 12%uint63))))
                    (iota 0 nedge) == nslice.
  rewrite to_natK; apply/eqP; rewrite -(count_sliceb cg).
  apply: eq_in_count => j.
  by rewrite mem_iota add0n => /andP[_ jL]; exact: nbit_smask jL.
have hall : all (fun m => (count (nbit (of_nat m)) (iota 0 nedge) == nslice)
                ==> (to_nat (PArray.get srank (of_nat m)) < nsrank)%N)
      (iota 0 nmask).
  by rewrite -srankCE; exact: srankCP.
by have := implyP (allP hall _ hmem) hcount; rewrite to_natK.
Qed.

(* and the parity at the array level: a move does not change it *)
Lemma fpar_step a k : tabi_ok 47 a -> cubti a -> (k < 18)%N ->
  fpar (coordi (comp_tabi 47 a (nth (id_tabi 47) mtis k))) = fpar (coordi a).
Proof.
move=> aok ca kL.
have kL' : (k < seq.size mtis)%N by rewrite size_mtis.
rewrite (actcdE kL' aok ca) /actcd.
have -> : nth (mdatf_of_tab [::]) mdatafd k = mdatf_of_tab (nth [::] mtabs k).
  by rewrite mdatafdE /mdataf (nth_map [::]) // size_mtabs18.
by apply: fpar_actf; rewrite mem_nth // size_mtabs18.
Qed.

