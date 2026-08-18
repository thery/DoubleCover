(* =========================================================================  *)
(*  HBound.v -- the block on top: what the run has to give, and what it gives.*)
(* =========================================================================  *)

(* THIS FILE PROVES NO BOUND.  It states the last step -- twenty five quarter *)
(* turns are not enough for the position -- as a consequence of three things, *)
(* and proves that implication.  Each of the three is written as an explicit  *)
(* hypothesis, so what is still owed is visible in the statement rather than  *)
(* buried:                                                                    *)
(*                                                                            *)
(*   Hrun    no rule-accepted word completes any of Reid's six prefixes       *)
(*           within the depth.  This is the 72 run files AND the soundness of *)
(*           the search, which rests on the table being a lower bound -- the  *)
(*           sweep, item 4, not started.                                      *)
(*   Hcanon  the search's rule loses no maneuver.  Item 3.  Searchr.v is this *)
(*           theorem for the eighteen moves; the quarter-turn version needs it*)
(*           generalised from `two of a face collapse' to `three collapse'.   *)
(*   the parity -- that a maneuver has even length -- is NOT a hypothesis any *)
(*           more: qparity below proves it.                                   *)
(*                                                                            *)
(* What IS proved here: that those give the bound, the two sides of the      *)
(* bridge between words and balls, the parity, and Reid's own 26 quarter      *)
(* turns.                                                                     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Table Tabi Tsearch Rubik333 Sym Ball Moves Coordfs Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- words and balls ----------------------------------------------------  *)

Definition Sqseq : seq {perm facelet} := [seq qmv m | m <- iota 0 nq].
Definition Sq : {set {perm facelet}} := [set g in Sqseq].

Lemma qmv_Sq m : (m < nq)%N -> qmv m \in Sq.
Proof.
move=> mL; rewrite inE /Sqseq; apply/mapP; exists m => //.
by apply: mem_iota0.
Qed.

Lemma Sq_qmv g : g \in Sq -> exists2 m, (m < nq)%N & g = qmv m.
Proof.
rewrite inE => /mapP[m mI ->]; exists m => //.
by move: mI; rewrite mem_iota add0n; case/andP.
Qed.

Lemma wp_ball (w : seq nat) : qw w -> wp w \in ball Sq (seq.size w).
Proof.
elim/last_ind: w => [_|w m ih]; first by rewrite wp_nil; apply: mem1_ball.
rewrite -cats1 /qw all_cat => /andP[wq]; rewrite /= andbT => mL.
rewrite wp_cat wp_one size_cat /= addn1 /=.
rewrite inE; apply/orP; right; apply: mem_mulg; first by apply: ih.
by apply: qmv_Sq.
Qed.

Lemma ball_wp (n : nat) (g : {perm facelet}) : g \in ball Sq n ->
  exists w, [/\ qw w, (seq.size w <= n)%N & wp w = g].
Proof.
elim: n g => [g|n ih g].
  rewrite /= inE => /eqP->; exists [::]; split => //; exact: wp_nil.
rewrite /= inE => /orP[/ih[w [wq ws wg]]|].
  by exists w; split => //; apply: leq_trans ws _.
case/mulsgP => b s bB /Sq_qmv[m mL ->] ->.
have [w [wq ws wg]] := ih _ bB.
exists (rcons w m); split.
- rewrite -cats1 /qw all_cat /= andbT mL andbT; exact: wq.
- by rewrite size_rcons ltnS.
by rewrite -cats1 wp_cat wp_one wg.
Qed.

(* ---- from the heads of prop2_search to one of Reid's six prefixes -------- *)

Lemma yrelK : all (fun m => yrel (xrel m) == m) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma xrel_inv a v : (a < nq)%N -> xrel a = v -> a = yrel v.
Proof.
move=> aL <-; apply/eqP; rewrite eq_sym.
by apply: (allP yrelK); apply: mem_iota0.
Qed.

Lemma take2E (w : seq nat) : (1 < seq.size w)%N ->
  take 2 w = [:: nth 0%N w 0; nth 0%N w 1].
Proof. by case: w => [|a [|b w]] //= _; rewrite take0. Qed.

Lemma take3E (w : seq nat) : (2 < seq.size w)%N ->
  take 3 w = [:: nth 0%N w 0; nth 0%N w 1; nth 0%N w 2].
Proof. by case: w => [|a [|b [|c w]]] //= _; rewrite take0. Qed.

(* the word begins with one of the six                                        *)
Definition hasp (w : seq nat) : bool :=
  has (fun p => take (seq.size p) w == p) rpfx.

Lemma sheads_hasp (w : seq nat) : qw w -> (2 < seq.size w)%N ->
  sheads [seq xrel m | m <- w] -> hasp w.
Proof.
move=> wq s3 hs.
have ha : (nth 0%N w 0 < nq)%N by apply: nth_qw => //; apply: leq_trans s3.
have hb : (nth 0%N w 1 < nq)%N by apply: nth_qw => //; apply: leq_trans s3.
have hc : (nth 0%N w 2 < nq)%N by apply: nth_qw.
move: hs; rewrite /sheads !(nth_map 0%N) //; last 2 first.
- by apply: leq_trans s3.
- by apply: leq_trans s3.
case/orP=> [/andP[/eqP e0 /eqP e1]|/and3P[/eqP e0 /eqP e1 e2]].
  rewrite /hasp /=; apply/orP; left.
  rewrite take2E; last by apply: leq_trans s3.
  by rewrite (xrel_inv ha e0) (xrel_inv hb e1).
rewrite /hasp /=; apply/orP; right.
rewrite (take3E s3) (xrel_inv ha e0) (xrel_inv hb e1).
move: e2; rewrite /ksearch !inE.
case/orP=> [e2|/orP[e2|/orP[e2|/orP[e2|e2]]]]; move/eqP: e2 => e2;
  by rewrite (xrel_inv hc e2) /= ?eqxx ?orbT.
Qed.

Lemma man_size3_targ (w : seq nat) : qw w -> wp w = targ -> (2 < seq.size w)%N.
Proof.
move=> wq hw.
have := man_size3 (xrel_qw wq) (man_x wq hw).
by rewrite size_map.
Qed.

(* ---- the rule, as a property of a word ----------------------------------  *)

(* what the search explores: from the start, every turn allowed by the rule   *)
(* in the class the ones before it left.                                      *)
Fixpoint okw (p : nat) (w : seq nat) : bool :=
  if w is m :: w' then allowedq p m && okw (hclass p m) w' else true.

(* ---- the parity: OBLIGATION A, PROVED ----------------------------------   *)

(* Every quarter turn is an ODD permutation of the forty eight facelets, so   *)
(* the sign of a word is the parity of its length; the position is even; so a *)
(* maneuver for it has even length.  That is what takes "nothing at 24" to    *)
(* "at least 26".                                                             *)
(*                                                                            *)
(* The sign comes from the cycles the moves are built from: Cyc.v defines a   *)
(* cycle as a product of transpositions, so its sign is odd of its length     *)
(* less one, and each face is five four-cycles -- fifteen transpositions.     *)

Lemma odd_cyc (A : finType) (l : seq A) : uniq l ->
  odd_perm (cyc l) = odd (seq.size l).-1.
Proof.
case: l => [_|a l]; first by rewrite /cyc odd_perm1.
rewrite cons_uniq => /andP[aNl lU].
rewrite /cyc (big_morph _ (@odd_permM _) (odd_perm1 _)).
have -> : \big[addb/false]_(i <- l) odd_perm (tperm a i)
        = \big[addb/false]_(i <- l) true.
  apply: eq_big_seq => i iL; rewrite odd_tperm.
  by case: eqP => // aE; move: aNl; rewrite aE iL.
have big_true : forall s : seq A,
    \big[addb/false]_(i <- s) true = odd (seq.size s).
  by elim=> [|b s ihs]; rewrite ?big_nil // big_cons ihs.
by rewrite big_true.
Qed.

Lemma uniq_map_inord (l : seq nat) :
  all (fun i => (i < flast.+1)%N) l -> uniq l ->
  uniq [seq (inord i : facelet) | i <- l].
Proof.
move=> lA lU; rewrite map_inj_in_uniq // => x y xL yL /(congr1 val) /=.
by rewrite !inordK //; [apply: (allP lA) | apply: (allP lA)].
Qed.

Lemma odd_cycs (ll : seq (seq nat)) :
  all (all (fun i => (i < flast.+1)%N)) ll -> all uniq ll ->
  odd_perm (pt flast (cycs_tab flast ll))
    = odd (sumn [seq (seq.size l).-1 | l <- ll]).
Proof.
move=> lA lU; rewrite -(cycs_pt lA lU).
rewrite (big_morph _ (@odd_permM _) (odd_perm1 _)) big_map.
elim: ll lA lU => [_ _|l ll ih] /=; first by rewrite big_nil.
case/andP => lA llA /andP[luq lluq].
rewrite big_cons ih // odd_cyc ?size_map ?oddD //.
by apply: uniq_map_inord.
Qed.

(* the six faces, as the cycles Sym.v builds them from                        *)
Definition ncycs : seq (seq (seq nat)) :=
  [:: Uncyc; Rncyc; Fncyc; Dncyc; Lncyc; Bncyc].

Lemma mvt_cycs' :
  all (fun f => nth (id_tab flast) mtabs (3 * f)
                  == cycs_tab flast (nth [::] ncycs f)) (iota 0 6).
Proof. by vm_compute. Qed.

Lemma ncycs_range :
  all (fun f => all (all (fun i => (i < flast.+1)%N)) (nth [::] ncycs f))
      (iota 0 6).
Proof. by vm_compute. Qed.

Lemma ncycs_uniq : all (fun f => all uniq (nth [::] ncycs f)) (iota 0 6).
Proof. by vm_compute. Qed.

(* five cycles of four is fifteen transpositions, so every face turn is odd   *)
Lemma ncycs_sum :
  all (fun f => sumn [seq (seq.size l).-1 | l <- nth [::] ncycs f] == 15)
      (iota 0 6).
Proof. by vm_compute. Qed.

Lemma odd_qmv_ev f : (f < 6)%N -> odd_perm (qmv (2 * f)%N) = true.
Proof.
move=> fL.
have mL : (2 * f < nq)%N by rewrite /nq -[12%N]/(2 * 6)%N ltn_mul2l.
have qE : qt18 (2 * f)%N = (3 * f)%N.
  by rewrite /qt18 oddM /= addn0 mulKn.
have /eqP mE := allP mvt_cycs' _ (mem_iota0 fL).
rewrite qmvE // /mvt qE mE odd_cycs.
- by have /eqP -> := allP ncycs_sum _ (mem_iota0 fL).
- by apply: (allP ncycs_range); apply: mem_iota0.
by apply: (allP ncycs_uniq); apply: mem_iota0.
Qed.

Lemma odd_qmv m : (m < nq)%N -> odd_perm (qmv m) = true.
Proof.
move=> mL.
have hev : forall k, (k < nq)%N -> ~~ odd k -> odd_perm (qmv k) = true.
  move=> k kL ke.
  have kE : k = (2 * (k %/ 2))%N.
    have kd : (2 %| k)%N by rewrite dvdn2.
    by rewrite mulnC divnK.
  rewrite kE; apply: odd_qmv_ev.
  by rewrite ltn_divLR // (leq_trans kL).
have [mo|me] := boolP (odd m); last by apply: hev.
have qE : qinv m = m.-1 by rewrite /qinv mo subn1.
have pL : (m.-1 < nq)%N by apply: leq_trans mL; apply: leq_pred.
have := qmvV mL; rewrite qE => hV.
have -> : qmv m = (qmv m.-1)^-1 by rewrite -hV invgK.
rewrite odd_permV; apply: hev => //.
by case: m mo {mL qE pL hV} => // k /=; rewrite negbK.
Qed.

Lemma odd_wp (w : seq nat) : qw w -> odd_perm (wp w) = odd (seq.size w).
Proof.
elim: w => [_|m w ih]; first by rewrite wp_nil odd_perm1.
rewrite /qw /= => /andP[mL wq].
by rewrite wp_cons odd_permM odd_qmv // ih.
Qed.

(* ---- the position, as a word of quarter turns ---------------------------  *)

(* one of the eighteen moves, spelled in quarter turns: a face turn is one, a *)
(* half turn is two, an inverse is one the other way.                         *)
Definition qexp1 (k : nat) : seq nat :=
  let f := (k %/ 3)%N in
  if (k %% 3 == 0)%N then [:: (2 * f)%N]
  else if (k %% 3 == 1)%N then [:: (2 * f)%N; (2 * f)%N]
  else [:: (2 * f + 1)%N].

Definition qexp (w : seq nat) : seq nat := flatten [seq qexp1 k | k <- w].

Definition targw : seq nat := Eval vm_compute in qexp (sfw ++ fsw).

Lemma targw_qw : qw targw.
Proof. by vm_compute. Qed.

Lemma targw_size : seq.size targw = 40.
Proof. by vm_compute. Qed.

Lemma targw_tab : wtr targw = ti2t flast targeti.
Proof. by apply/eqP; vm_compute. Qed.

Lemma wp_targw : wp targw = targ.
Proof. by rewrite wp_wtr ?targw_qw // targw_tab. Qed.

Lemma targ_even : odd_perm targ = false.
Proof. by rewrite -wp_targw odd_wp ?targw_qw // targw_size. Qed.

Theorem qparity (w : seq nat) : qw w -> wp w = targ -> ~~ odd (seq.size w).
Proof. by move=> wq hw; rewrite -odd_wp // hw targ_even. Qed.

(* ---- and Reid's own 26 quarter turns -----------------------------------   *)

(* U2 D2 L F2 U' D R2 B U' D' R L F2 R U D' R' L U F' B', which he gives as   *)
(* 26q and 21f.  Spelled out it is twenty six quarter turns and it does give  *)
(* the position -- q26_tab is that check.                                     *)
Definition r26w : seq nat :=
  [:: 1; 10; 12; 7; 2; 9; 4; 15; 2; 11; 3; 12; 7; 3; 0; 11; 5; 12; 0; 8; 17]%N.

Definition q26 : seq nat := Eval vm_compute in qexp r26w.

Lemma q26_size : seq.size q26 = 26.
Proof. by vm_compute. Qed.

Lemma q26_qw : qw q26.
Proof. by vm_compute. Qed.

Lemma q26_tab : wtr q26 = ti2t flast targeti.
Proof. by apply/eqP; vm_compute. Qed.

Theorem targ_near : targ \in ball Sq 26.
Proof.
have <- : wp q26 = targ by rewrite wp_wtr ?q26_qw // q26_tab.
by have h := wp_ball q26_qw; rewrite q26_size in h.
Qed.

(* ---- the block ----------------------------------------------------------  *)

(* The induction is on the length, and it is what replaces `take a shortest   *)
(* maneuver': at each step the shorter ones are already known not to exist, so*)
(* the one in hand is a shortest, which is what prop2 asks for.               *)
Lemma no_man
  (Hrun : forall k v, (k < seq.size rpfx)%N -> qw v -> okw 0 v ->
     (seq.size (nth [::] rpfx k) + seq.size v <= 24)%N ->
     wp (nth [::] rpfx k ++ v) != targ)
  (Hcanon : forall v, qw v -> exists v', [/\ qw v', wp v' = wp v,
                                   (seq.size v' <= seq.size v)%N & okw 0 v'])
  n : (n <= 25)%N ->
  forall w, qw w -> wp w = targ -> (seq.size w <= n)%N -> False.
Proof.
elim: n => [_ w wq hw|n ih nL w wq hw ws].
  rewrite leqn0 => /eqP /size0nil wE.
  by have := man_size3_targ wq hw; rewrite wE.
have [wsn|wsn] := boolP (seq.size w <= n)%N.
  by apply: (ih _ w) => //; apply: ltnW.
have hmin : forall u, qw u -> wp u = targ -> (seq.size w <= seq.size u)%N.
  move=> u uq hu; rewrite leqNgt; apply/negP => hlt.
  apply: (ih _ u uq hu) => //; first by apply: ltnW.
  by rewrite -ltnS; apply: leq_trans hlt _.
have [w' [q' s' p' h']] := prop2_search wq hw hmin.
have s3 := man_size3_targ q' p'.
have hp := sheads_hasp q' s3 h'.
move: hp; rewrite /hasp => /hasP[pk pkR /eqP pkE].
have kL : (index pk rpfx < seq.size rpfx)%N by rewrite index_mem.
set k := index pk rpfx.
have pkN : nth [::] rpfx k = pk by apply: nth_index.
set v := drop (seq.size pk) w'.
have wE : pk ++ v = w' by rewrite /v -{1}pkE cat_take_drop.
have vq : qw v by apply: qw_drop.
have [v' [q2 p2 s2 o2]] := Hcanon _ vq.
have hsz : (seq.size pk + seq.size v' <= 24)%N.
  apply: leq_trans (_ : (seq.size pk + seq.size v <= 24)%N).
    by rewrite leq_add2l.
  rewrite -size_cat wE s'.
  have hle : (seq.size w <= 25)%N by apply: leq_trans ws nL.
  have hev := qparity wq hw.
  move: hle; rewrite leq_eqVlt => /orP[/eqP hE|]; last by rewrite ltnS.
  by move: hev; rewrite hE.
have := Hrun k v' kL q2 o2; rewrite pkN hsz => /(_ isT)/eqP; apply.
by rewrite wp_cat p2 -wp_cat wE.
Qed.

Theorem targ_far
  (Hrun : forall k v, (k < seq.size rpfx)%N -> qw v -> okw 0 v ->
     (seq.size (nth [::] rpfx k) + seq.size v <= 24)%N ->
     wp (nth [::] rpfx k ++ v) != targ)
  (Hcanon : forall v, qw v -> exists v', [/\ qw v', wp v' = wp v,
                                   (seq.size v' <= seq.size v)%N & okw 0 v'])
  :
  targ \notin ball Sq 25.
Proof.
apply/negP => /ball_wp[w [wq ws wt]].
by apply: (no_man Hrun Hcanon (leqnn 25) wq wt ws).
Qed.

(* ---- what each hypothesis still needs -----------------------------------  *)

(* Hpar.  Every quarter turn is an ODD permutation of the forty eight         *)
(* facelets -- five four-cycles -- so the sign of a word is the parity of its *)
(* length, and the position is even.  What is missing is the sign itself:     *)
(* mathcomp's odd_perm is not computable on pt of a table, so it needs either *)
(* a cycle count on the table with a lemma tying it to odd_perm, or the moves *)
(* read back through the cycles Sym.v builds them from.                       *)
(*                                                                            *)
(* Hcanon.  Searchr.v proved for the eighteen moves.  Generalise fc_close.    *)
(*                                                                            *)
(* Hrun.  Two halves.  The run files give `the search returned false'.  Making*)
(* that mean `no rule-accepted word completes the prefix' needs the search to *)
(* be sound, and the search prunes with the table, so it needs                *)
(*                                                                            *)
(*   h of the solved coset is 0                    -- one lookup;             *)
(*   h x <= h (x . m) + 1 for every coset and turn -- THE SWEEP, 2.9e10 x 12; *)
(*   the coordinates commute with the moves        -- a sweep too, and it also*)
(*     needs unranking in Rocq: mtabsok checks a spread of positions, not all;*)
(*   the fold reads back what the flat table holds -- the symmetry argument.  *)
(*                                                                            *)
(* The first two are what `item 4' means.  The third is the one I would have  *)
(* missed: HChk passes on 950 positions, which is a check, not a theorem.     *)
