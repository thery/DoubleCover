(** * search: the candidates of one line *)

From APaulRocq Require Import HtrDefs.
From compcert Require Import CaplaProof.
Require Import HtrFilterCapla.htr_filter HtrFilterCapla.HtrWords.
Require Import HtrFilterCapla.WordLemmas HtrFilterCapla.Specs.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** Lists: mathcomp and Stdlib *)

Lemma mapE {A B : Type} (f : A -> B) (s : list A) :
  [seq f x | x <- s] = List.map f s.
Proof. by elim: s => //= x s ->. Qed.

Lemma sizeE {A : Type} (s : list A) : size s = List.length s.
Proof. by elim: s => //= x s ->. Qed.

Lemma iotaE s n : iota s n = List.seq s n.
Proof. by elim: n s => //= n IH s; rewrite IH. Qed.

Lemma app1E {A : Type} (s : list A) x : List.app s (x :: nil) = rcons s x.
Proof. by elim: s => //= y s ->. Qed.

(** ** The table, on integers *)

(* Reducing modulo b before a step of the table changes nothing modulo b. *)
Lemma tstepZ_mod (b : Z) ds :
  List.map (fun z => z mod b)%Z (tstepZ (List.map (fun z => z mod b)%Z ds)) =
  List.map (fun z => z mod b)%Z (tstepZ ds).
Proof.
  set g := fun z => (z mod b)%Z.
  have Ec : forall x s, List.map g (x :: s) = g x :: List.map g s by [].
  elim: ds => [|a ds IH] //; case: ds IH => [|c r] IH.
    by rewrite /= /g Zmod_mod.
  have E1 : tstepZ (List.map g [:: a, c & r]) =
    (g a + g c)%Z :: tstepZ (List.map g (c :: r)) by [].
  have E2 : tstepZ [:: a, c & r] = (a + c)%Z :: tstepZ (c :: r) by [].
  rewrite E1 E2 Ec IH Ec; congr (_ :: _).
  by rewrite /g -Zplus_mod.
Qed.

Lemma table_S l e ds j : table l e ds j.+1 = tstepZ (table l e ds j).
Proof. by []. Qed.

(* One more j: j is added when it is a candidate. *)
Lemma cands_S l e ds j :
  cands l e ds j.+1 =
  if cand l e ds j then rcons (cands l e ds j) j else cands l e ds j.
Proof.
  rewrite /cands List.seq_S List.filter_app /=.
  by case: cand; rewrite ?app1E ?List.app_nil_r.
Qed.

(* There are at most j candidates below j. *)
Lemma size_cands l e ds j : (size (cands l e ds j) <= j)%nat.
Proof.
  rewrite sizeE /cands; apply/leP.
  by have := List.filter_length_le (cand l e ds) (List.seq 0 j);
    rewrite List.length_seq.
Qed.

(* Adding e to the top digit of a number written in base M. *)
Lemma add_top_digit (X B M u e : Z) : (0 <= X < B)%Z -> (0 < M)%Z ->
  (X + B * ((u + e) mod M) = (X + B * u + e * B) mod (B * M))%Z.
Proof.
  move=> HX HM.
  have Hd := Z.div_mod (u + e) M ltac:(lia).
  have Hr := Z.mod_pos_bound (u + e) M HM.
  apply: (Z.mod_unique_pos _ _ ((u + e) / M)); first nia.
  have -> : (X + B * u + e * B = X + B * (u + e))%Z by ring.
  rewrite {1}Hd; ring.
Qed.

(* The weight of the top word of a coefficient of L + 1 words. *)
Lemma top_weight (L : nat) :
  (2 ^ (wbits * (Z.of_nat L.+1 - 1)))%Z = baseZ (Z.of_nat L).
Proof. by rewrite /baseZ; f_equal; lia. Qed.

(** ** The words of the array *)

Section Arr.

Context {n : nat}.
Implicit Types b : {ffun 'I_n -> int64}.

(* The top word of coefficient 0 is word l - 1. *)
Lemma top_coef0 b L : (0 < L)%nat ->
  top (Z.of_nat L) (coefA b L 0) = wd b L.-1.
Proof.
  case: L => [//|L] _ /=.
  rewrite /coefA mul0n segvS add0n /top top_weight.
  have Hs := segv_bound b 0 L; have Hw := wd_bound b L.
  have Bp := baseZ_pos L.
  rewrite Zmod_small; first by rewrite baseZS; nia.
  rewrite Z.mul_comm Z.div_add; first lia.
  rewrite Z.div_small; first lia.
  lia.
Qed.

(* The window: err added to word l - 1 adds err beta^(l-1) to
   coefficient 0 and leaves the others. *)
Lemma window_coef b1 b2 L e : (0 < L)%nat ->
  (forall q : 'I_n, (q : nat) <> L.-1 -> b2 q = b1 q) ->
  wd b2 L.-1 = ((wd b1 L.-1 + e) mod 2 ^ wbits)%Z ->
  coefA b2 L 0 =
    ((coefA b1 L 0 + e * 2 ^ (wbits * (Z.of_nat L - 1))) mod baseZ (Z.of_nat L))%Z
  /\ forall p, (0 < p)%nat -> coefA b2 L p = coefA b1 L p.
Proof.
  move=> HL Hf Hw; split; last first.
  { move=> p Hp; apply: coefA_ext => q Hq; apply: Hf => Eq.
    have : (L <= p * L)%nat by rewrite leq_pmull.
    lia. }
  case: L HL Hf Hw => [//|L] _ Hf Hw /=.
  rewrite /coefA mul0n; rewrite !segvS; rewrite add0n top_weight Hw baseZS.
  have -> : segv b2 0 L = segv b1 0 L.
  { apply: segv_ext => q Hq; apply: wd_eq => Hq'; apply: Hf => /=; lia. }
  apply: add_top_digit; last by rewrite /wbits; lia.
  have := segv_bound b1 0 L; lia.
Qed.

(* After difftab and the window, the array holds table 0. *)
Lemma window_coefs b1 L K (kk : nat) (Hk : (kk < n)%nat) v e ds :
  (0 < L)%nat -> (0 < K)%nat -> kk = L.-1 -> size ds = K ->
  Int64.unsigned v = ((wd b1 L.-1 + e) mod 2 ^ wbits)%Z ->
  coefsA b1 L K = [seq fdiff ds j mod baseZ (Z.of_nat L) | j <- iota 0 K]%Z ->
  coefsA (b1 ↑[kk ← v]) L K =
    List.map (fun z => z mod baseZ (Z.of_nat L))%Z (table (Z.of_nat L) e ds 0).
Proof.
  move=> HL HK Ekk Hs Hv Hd.
  set g := fun z => (z mod baseZ (Z.of_nat L))%Z.
  have Hf : forall q : 'I_n, (q : nat) <> L.-1 -> (b1 ↑[kk ← v]) q = b1 q.
  { move=> q Hq; rewrite (setfE _ _ _ Hk) ffunE; case: eqP => // Eq.
    by case: Hq; rewrite Eq /= Ekk. }
  have Hw : wd (b1 ↑[kk ← v]) L.-1 = ((wd b1 L.-1 + e) mod 2 ^ wbits)%Z.
    by rewrite (wd_set _ _ _ _ Hk); case: eqP => [_|]; [exact: Hv | rewrite Ekk].
  have [W0 Wp] := window_coef b1 (b1 ↑[kk ← v]) L e HL Hf Hw.
  have E0 : table (Z.of_nat L) e ds 0 =
    window (Z.of_nat L) e (List.map (fdiff ds) (List.seq 0 (List.length ds))) by [].
  rewrite E0 -sizeE Hs.
  case: K HK Hs Hd => [//|K'] _ _ Hd.
  have I0 : iota 0 K'.+1 = 0%nat :: iota 1 K' by [].
  have S0 : List.seq 0 K'.+1 = 0%nat :: List.seq 1 K' by [].
  move: Hd; rewrite /coefsA I0 S0 => -[H0 Ht].
  have Ec : forall (f : nat -> Z) s x, [seq f p | p <- x :: s] = f x :: [seq f p | p <- s] by [].
  rewrite Ec.
  have -> : List.map (fdiff ds) (0%nat :: List.seq 1 K') =
            fdiff ds 0 :: List.map (fdiff ds) (List.seq 1 K') by [].
  have -> : forall a s, window (Z.of_nat L) e (a :: s) =
            (a + e * 2 ^ (wbits * (Z.of_nat L - 1)))%Z :: s by [].
  have -> : forall a s, List.map g (a :: s) = g a :: List.map g s by [].
  congr (_ :: _).
  - by rewrite W0 H0 /g Zplus_mod_idemp_l.
  - rewrite List.map_map -iotaE -mapE -Ht.
    apply/eq_in_map => p; rewrite mem_iota => /andP [Hp _].
    exact: Wp.
Qed.

(* The test of the loop is cand: word l - 1 against 2 err. *)
Lemma cand_word b L K e ds j : (0 < L)%nat -> (0 < K)%nat ->
  coefsA b L K =
    List.map (fun z => z mod baseZ (Z.of_nat L))%Z (table (Z.of_nat L) e ds j) ->
  cand (Z.of_nat L) e ds j = (wd b L.-1 <=? 2 * e)%Z.
Proof.
  move=> HL HK Hc; rewrite /cand.
  set g := fun z => (z mod baseZ (Z.of_nat L))%Z.
  have T : forall T, top (Z.of_nat L) (List.nth 0 T 0%Z) =
                     top (Z.of_nat L) (List.nth 0 (List.map g T) 0%Z).
    by case=> [|x T] //=; rewrite /top /g Zmod_mod.
  rewrite T -Hc.
  case: K HK Hc => [//|K'] _ _.
  have -> : List.nth 0 (coefsA b L K'.+1) 0%Z = coefA b L 0 by [].
  by rewrite top_coef0.
Qed.

(* One call of tstep: the array goes from table j to table (j+1). *)
Lemma table_step b b' L K e ds j :
  coefsA b L K =
    List.map (fun z => z mod baseZ (Z.of_nat L))%Z (table (Z.of_nat L) e ds j) ->
  coefsA b' L K =
    [seq z mod baseZ (Z.of_nat L) | z <- tstepZ (coefsA b L K)]%Z ->
  coefsA b' L K =
    List.map (fun z => z mod baseZ (Z.of_nat L))%Z (table (Z.of_nat L) e ds j.+1).
Proof. by move=> H1 ->; rewrite mapE H1 tstepZ_mod. Qed.

End Arr.


(** ** The words of the loop *)

(* The test of the loop: word l - 1 at most 2 err. *)
Section Mul.
Transparent Int64.mul.
Lemma le_word (w e : int64) : (2 * Int64.unsigned e <= Int64.max_unsigned)%Z ->
  ~~ Int64.ltu (Int64.mul (Int64.repr 2) e) w =
  (Int64.unsigned w <=? 2 * Int64.unsigned e)%Z.
Proof.
  move=> He; have Re := Int64.unsigned_range e.
  rewrite /Int64.ltu /Int64.mul.
  change (Int64.unsigned (Int64.repr 2)) with 2%Z.
  rewrite Int64.unsigned_repr; first lia.
  by case: Z.leb_spec => H1; case: Coqlib.zlt => H2 //=; exfalso; lia.
Qed.
End Mul.

(* A word as the natural number it stands for. *)
Lemma repr_nat (j : int64) : Int64.repr (Z.of_nat (Z.to_nat (Int64.unsigned j))) = j.
Proof.
  rewrite Z2Nat.id; first by have := Int64.unsigned_range j; lia.
  exact: Int64.repr_unsigned.
Qed.

(* A candidate j is written at index count, while count < cap. *)
Lemma out_write (c : nat) (o : {ffun 'I_c -> int64}) (cs : list nat) (cnt j : int64)
    (Hc : (Z.to_nat (Int64.unsigned cnt) < c)%nat) :
  Z.to_nat (Int64.unsigned cnt) = size cs ->
  (forall i : 'I_c, (i < size cs)%nat -> o i = Int64.repr (Z.of_nat (nth 0%nat cs i))) ->
  forall i : 'I_c, (i < size (rcons cs (Z.to_nat (Int64.unsigned j))))%nat ->
    [ffun x => if x == Ordinal Hc then j else o x] i =
    Int64.repr (Z.of_nat (nth 0%nat (rcons cs (Z.to_nat (Int64.unsigned j))) i)).
Proof.
  move=> Hcnt Ho i; rewrite size_rcons ffunE nth_rcons => Hi.
  case: eqP => [Ei|Ni].
  - have -> : (i : nat) = size cs by rewrite Ei /= Hcnt.
    by rewrite ltnn eqxx repr_nat.
  - have Hi' : (i < size cs)%nat.
      move: Hi; rewrite ltnS leq_eqVlt => /orP [/eqP Ei|//].
      by case: Ni; apply: val_inj; rewrite /= Ei Hcnt.
    by rewrite Hi' Ho.
Qed.

(* Once count >= cap, out is left as it is. *)
Lemma out_full (c : nat) (o : {ffun 'I_c -> int64}) (cs : list nat) x :
  (c <= size cs)%nat ->
  (forall i : 'I_c, (i < size cs)%nat -> o i = Int64.repr (Z.of_nat (nth 0%nat cs i))) ->
  forall i : 'I_c, (i < size (rcons cs x))%nat ->
    o i = Int64.repr (Z.of_nat (nth 0%nat (rcons cs x) i)).
Proof.
  move=> Hc Ho i _; have Hi : (i < size cs)%nat by apply: leq_trans Hc.
  by rewrite nth_rcons Hi Ho.
Qed.

Theorem search_ok : difftab_spec -> tstep_spec -> search_spec.
Proof.
  move=> DS TS μ mm m Hm cc cap Hcc B0 out0 k l n err r rl K L N HK HL HKL Herr.
  subst mm cc.
  enter_func. csteps.
  call DS => /(_ erefl HKL) [B1 [-> [Hd Hdf]]].
  csteps; evalf; csteps.
  set ds := coefsA B0 L K.
  set g := fun z => (z mod baseZ (Z.of_nat L))%Z.
  set E := Int64.unsigned err.
  inv I := { [:: B; out; count; j; _j_hi] }
    (fun (b : {ffun 'I_(m:N) -> int64}) (o : {ffun 'I_(cap:N) -> int64})
         (c jj hi : int64) =>
    hi = n /\ (jj:N <= N)%nat /\
    coefsA b L K = List.map g (table (Z.of_nat L) E ds jj:N) /\
    c:N = size (cands (Z.of_nat L) E ds jj:N) /\
    (forall i : 'I_(cap:N), (i < size (cands (Z.of_nat L) E ds jj:N))%nat ->
       o i = Int64.repr (Z.of_nat (nth 0%nat (cands (Z.of_nat L) E ds jj:N) i)))).
  enter_loop I.
  { have HL1 : (L.-1 < m:N)%nat.
      by apply: leq_trans HKL; rewrite prednK // leq_pmull.
    have Esl : (Int64.sub l (Int64.repr 1)):N = L.-1 by apply: sub1_nat.
    prove_inv; exsp.
    apply: window_coefs => //; first by rewrite /ds size_coefsA.
    by rewrite Int64.add_unsigned Int64.unsigned_repr_eq -Esl (wdE _ _ H). }
  unfold_inv => - [hv [Ehv [Ehn [Hj [Hc [Hcnt Hout]]]]]].
  csteps.
  have HL1 : (L.-1 < m:N)%nat.
    by apply: leq_trans HKL; rewrite prednK // leq_pmull.
  have Esl : (Int64.sub l (Int64.repr 1)):N = L.-1 by apply: sub1_nat.
  have HNm : (Z.of_nat N <= Int64.max_unsigned)%Z.
    by have := Int64.unsigned_range_2 n; rewrite /N; lia.
  case END: Int64.ltu => /=; move: (END); rewrite ltu_nat => END'.
  - (* one step *)
    have Ej1 : (Int64.add j0 (Int64.repr 1)):N = (j0:N).+1.
      by apply: (add1_nat _ N).
    have Hcand := cand_word B2 L K E ds j0:N HL HK Hc.
    have Hsz := size_cands (Z.of_nat L) E ds j0:N.
    have Ecand : ~~ Int64.ltu (Int64.mul (Int64.repr 2) err)
                   (B2 (Ordinal H)) = cand (Z.of_nat L) E ds j0:N.
      by rewrite Hcand le_word // -(wdE _ _ H) Esl.
    have Hc0 : (count0:N < N)%nat by rewrite Hcnt; apply: leq_ltn_trans Hsz END'.
    have Ec1 : (Int64.add count0 (Int64.repr 1)):N = (count0:N).+1.
      by apply: (add1_nat _ N).
    have Ecs := cands_S (Z.of_nat L) E ds j0:N.
    csteps; evalf; csteps.
    rewrite Ecand; case C: cand => /=.
    + csteps.
      case C2: (Int64.ltu count0 cap) => /=; move: (C2); rewrite ltu_nat => C2'.
      * csteps; evalf; csteps.
        call TS => /(_ erefl HK HL HKL) [B3 [-> [Ht _]]].
        csteps; cret; split=> // _; split.
        { solve_loop_conditions. }
        prove_inv; exsp; rewrite ?Ej1 ?Ec1.
        -- exact: END'.
        -- exact: (table_step B2 B3 L K E ds j0:N Hc Ht).
        -- by rewrite Ecs C size_rcons Hcnt.
        -- rewrite Ecs C.
           exact: (out_write _ out1 _ count0 j0 _ Hcnt Hout).
      * csteps.
        call TS => /(_ erefl HK HL HKL) [B3 [-> [Ht _]]].
        csteps; cret; split=> // _; split.
        { solve_loop_conditions. }
        prove_inv; exsp; rewrite ?Ej1 ?Ec1.
        -- exact: END'.
        -- exact: (table_step B2 B3 L K E ds j0:N Hc Ht).
        -- by rewrite Ecs C size_rcons Hcnt.
        -- rewrite Ecs C; apply: out_full Hout.
           by rewrite -Hcnt leqNgt C2'.
    + csteps.
      call TS => /(_ erefl HK HL HKL) [B3 [-> [Ht _]]].
      csteps; cret; split=> // _; split.
      { solve_loop_conditions. }
      prove_inv; exsp; rewrite ?Ej1.
      -- exact: END'.
      -- exact: (table_step B2 B3 L K E ds j0:N Hc Ht).
      -- by rewrite Ecs C.
      -- by rewrite Ecs C.
  - (* the loop ends with j = n *)
    csteps; cret; split=> //= _; csteps; cret.
    have Ej : j0:N = N by apply/eqP; rewrite eqn_leq Hj leqNgt END'.
    exists B2, out1; split; first by rewrite/envC/=.
    rewrite -Ej; split; last exact: Hout.
    by rewrite /envC /= -Hcnt repr_nat.
Qed.
