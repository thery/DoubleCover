(** * search_filter: the candidates of search that maybe_hard_bits keeps

    [search_filter] of ../htr_filter.b calls [search], then walks the
    first [min(count, cap)] candidates [j] written in [out], and keeps
    (compacted at the start of [out], in order) those for which
    [maybe_hard_bits] of the bits [xb0 + j] ([neg = 0]) or [xb0 - j]
    ([neg <> 0]), taken mod [2^64], answers [1].  It returns the number
    kept.  The statement mirrors [search_filter_spec] of the VST proof
    (../../../vst/htrfilter/Spec_filter.v).

    [search_filter_ok] proves it from the statement [search_spec] of
    search (Specs.v); the external maybe_hard_bits is used through
    [maybe_hard_bits_ok], from the axiom of ExtAxiom.v. *)

From compcert Require Import CaplaProof.
From APaulRocq Require Import HtrDefs.
From Exp100 Require ExpModel.
Require Import HtrFilterCapla.htr_filter HtrFilterCapla.HtrWords
  HtrFilterCapla.Specs HtrFilterCapla.ExtAxiom.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(* the model of the filter is never computed by the execution *)
Arguments ExpModel.maybe_hard_Z : simpl never.

(** ** The filter maybe_hard_bits *)

(* What a call of maybe_hard_bits returns: maybe_hard_Z of the model. *)
Definition maybe_hard_bits_spec : Prop :=
  forall μ xb r rl,
    eval_func ge μ f_maybe_hard_bits [:: xb <:: u64] = Some (r, rl) ->
    r = Vint64 (Int64.repr (ExpModel.maybe_hard_Z (Int64.unsigned xb))) /\
    rl = [::].

(* It holds by the axiom of ExtAxiom.v. *)
Lemma maybe_hard_bits_ok : maybe_hard_bits_spec.
Proof.
have [ef Hef] : exists ef, f_maybe_hard_bits = External ef.
  by eexists; reflexivity.
move=> μ xb r rl.
case: μ => [|μ]; rewrite Hef /= (maybe_hard_bits_ext ef xb Hef) => -[<- <-];
  by split.
Qed.

(** ** What is kept *)

(* The bits of the input j of the line: xb0 + j or xb0 - j, as a word of
   64 bits (what the program computes). *)
Definition xbj (neg xb0 j : Z) : Z :=
  (if Z.eqb neg 0 then xb0 + j else xb0 - j) mod 2 ^ 64.

(* j is kept: maybe_hard_bits answers 1 on the bits of the input j. *)
Definition keep (neg xb0 : Z) (j : nat) : bool :=
  Z.eqb (ExpModel.maybe_hard_Z (xbj neg xb0 (Z.of_nat j))) 1.

(* The candidates written by search in out (the first cap), then those
   kept. *)
Definition kept_list (L : nat) (err : Z) (cs : list Z) (N cc : nat)
    (neg xb0 : Z) : list nat :=
  seq.filter (keep neg xb0) (seq.take cc (cands (Z.of_nat L) err cs N)).

(** ** The statement *)

Definition search_filter_spec : Prop :=
  forall μ (mm : nat) (m : int64), mm = Z.to_nat (Int64.unsigned m) ->
  forall (cc : nat) (cap : int64), cc = Z.to_nat (Int64.unsigned cap) ->
  forall (B : {ffun 'I_mm -> int64}) (out : {ffun 'I_cc -> int64})
      (k l n err xb0 neg : int64) r rl,
    let K := Z.to_nat (Int64.unsigned k) in
    let L := Z.to_nat (Int64.unsigned l) in
    let N := Z.to_nat (Int64.unsigned n) in
    (1 <= K)%nat -> (1 <= L)%nat -> (K * L <= mm)%nat ->
    2 * Int64.unsigned err <= Int64.max_unsigned ->
    eval_func ge μ f_search_filter
      [:: B <:: [u64; mm]; m <:: u64; k <:: u64; l <:: u64; n <:: u64;
          err <:: u64; out <:: [u64; cc]; cap <:: u64; xb0 <:: u64;
          neg <:: u64]
      = Some (r, rl) ->
    let ks := kept_list L (Int64.unsigned err) (coefsA B L K) N cc
                (Int64.unsigned neg) (Int64.unsigned xb0) in
    exists (B' : {ffun 'I_mm -> int64}) (out' : {ffun 'I_cc -> int64}),
      rl = [:: B' <:: [u64; mm]; out' <:: [u64; cc]] /\
      r = Vint64 (Int64.repr (Z.of_nat (size ks))) /\
      (forall i : 'I_cc, (i < size ks)%nat ->
         out' i = Int64.repr (Z.of_nat (nth 0%nat ks i))).

(** ** Facts on the candidates and on the words *)

(* Stdlib's filter and seq are mathcomp's filter and iota. *)
Lemma List_filterE {T : Type} (f : T -> bool) (s : seq.seq T) :
  List.filter f s = seq.filter f s.
Proof. by elim: s => //= x s ->. Qed.

Lemma List_seqE (a n : nat) : List.seq a n = iota a n.
Proof. by elim: n a => //= n IH a; rewrite IH. Qed.

(* There are at most n candidates, each below n. *)
Lemma cands_size l e ds n : (size (cands l e ds n) <= n)%nat.
Proof.
rewrite /cands List_filterE List_seqE size_filter.
by apply: leq_trans (count_size _ _) _; rewrite size_iota.
Qed.

Lemma cands_lt l e ds n x : x \in cands l e ds n -> (x < n)%nat.
Proof.
by rewrite /cands List_filterE List_seqE mem_filter mem_iota add0n
  => /andP [_ /andP [_ ->]].
Qed.

(* A word as a natural number. *)
Lemma wordN_lt (w : int64) : (Z.of_nat w:N < 2 ^ 64)%Z.
Proof.
rewrite Z2Nat.id; last by have := Int64.unsigned_range w; lia.
by have := Int64.unsigned_range w; change Int64.modulus with (2 ^ 64)%Z; lia.
Qed.

Lemma unsigned_reprN (x : nat) : (Z.of_nat x < 2 ^ 64)%Z ->
  Int64.unsigned (Int64.repr (Z.of_nat x)) = Z.of_nat x.
Proof.
by move=> hx; apply: Int64.unsigned_repr;
  change Int64.max_unsigned with (2 ^ 64 - 1)%Z; lia.
Qed.

Lemma reprN (x : nat) : (Z.of_nat x < 2 ^ 64)%Z ->
  (Int64.repr (Z.of_nat x)):N = x.
Proof. by move=> hx; rewrite unsigned_reprN // Nat2Z.id. Qed.

(* The bits of the input j, as the program computes them. *)
Lemma xb_add (neg xb0 : int64) (x : Z) : (0 <= x < 2 ^ 64)%Z ->
  Int64.eq neg (Int64.repr 0) = true ->
  Int64.unsigned (Int64.add xb0 (Int64.repr x)) =
  xbj (Int64.unsigned neg) (Int64.unsigned xb0) x.
Proof.
move=> hx; rewrite /Int64.eq; case: Coqlib.zeq => // h _.
rewrite /xbj h /= /Int64.add Int64.unsigned_repr_eq.
rewrite (Int64.unsigned_repr x) //.
by change Int64.max_unsigned with (2 ^ 64 - 1)%Z; lia.
Qed.

Lemma xb_sub (neg xb0 : int64) (x : Z) : (0 <= x < 2 ^ 64)%Z ->
  Int64.eq neg (Int64.repr 0) = false ->
  Int64.unsigned (Int64.sub xb0 (Int64.repr x)) =
  xbj (Int64.unsigned neg) (Int64.unsigned xb0) x.
Proof.
move=> hx; rewrite /Int64.eq; case: Coqlib.zeq => // h _.
have h' : Int64.unsigned neg <> 0%Z by move: h; rewrite Int64.unsigned_zero.
rewrite /xbj (proj2 (Z.eqb_neq _ _) h') /Int64.sub Int64.unsigned_repr_eq.
rewrite (Int64.unsigned_repr x) //.
by change Int64.max_unsigned with (2 ^ 64 - 1)%Z; lia.
Qed.

(* The test r == 1 on the answer of maybe_hard_bits. *)
Lemma eq_mh (z : Z) : (0 <= z <= 1)%Z ->
  Int64.eq (Int64.repr z) (Int64.repr 1) = Z.eqb z 1.
Proof.
move=> hz; have [->|->] : z = 0%Z \/ z = 1%Z by lia.
  by vm_compute.
by vm_compute.
Qed.

Lemma maybe_hard_Z_range xb : (0 <= ExpModel.maybe_hard_Z xb <= 1)%Z.
Proof.
rewrite /ExpModel.maybe_hard_Z.
case: (ExpModel.core_Z xb) => [rc|[y hN]]; first lia.
rewrite /ExpModel.decide_Z; cbv zeta.
by repeat match goal with |- context [if ?b then _ else _] => case: b end;
  lia.
Qed.

(* The kept candidates among the first t, one more. *)
Lemma filter_take_S (p : pred nat) (s : seq.seq nat) (t : nat) :
  (t < size s)%nat ->
  seq.filter p (seq.take t.+1 s) =
  seq.filter p (seq.take t s) ++
    (if p (nth 0%nat s t) then [:: nth 0%nat s t] else [::]).
Proof.
move=> ht; rewrite (take_nth 0%nat ht) filter_rcons -cats1.
by case: (p _); rewrite ?cats0.
Qed.

Lemma ltuN (a b : int64) : Int64.ltu a b = true -> (a:N < b:N)%nat.
Proof.
rewrite /Int64.ltu; case: Coqlib.zlt => // h _.
have := Int64.unsigned_range a; lia.
Qed.

Lemma ltuNF (a b : int64) : Int64.ltu a b = false -> (b:N <= a:N)%nat.
Proof.
rewrite /Int64.ltu; case: Coqlib.zlt => // h _.
have := Int64.unsigned_range b; lia.
Qed.

Lemma take_minn (s : seq.seq nat) (n : nat) :
  seq.take (minn (size s) n) s = seq.take n s.
Proof.
rewrite /minn; case: ltnP => h //.
by rewrite take_size take_oversize // ltnW.
Qed.

(** ** Tactics of the symbolic execution

    [start] enters the function with the postcondition hidden, [envr]
    computes the lookups of the environment, [fin] gives the
    postcondition back at the return. *)

(* enter a function; the postcondition is hidden in a local definition
   POST, so that the simplifications of the execution leave it alone *)
Ltac start := lazymatch goal with |- _ = Some (?r, ?rl) -> _ =>
  let E := fresh "E" in move=> E; pattern r, rl;
  lazymatch goal with |- ?F _ _ => let Q := fresh "POST" in set Q := F end;
  move: E; enter_func end.

(* the return: the postcondition back *)
Ltac fin := cret; lazymatch goal with Q := _ |- ?F _ _ =>
  rewrite /F; cbv beta; clear F end.

(* astep does not compute the lookups of the environment: each assignment
   then copies the previous environment into the new one (nested envC),
   and the steps slow down; [envr] computes them *)
Ltac envr := rewrite /envC /=.

(* run the program as far as possible: the steps, the array reads *)
Ltac run := repeat progress (csteps; evalf).

(* the writes of the program into an array of words *)
Lemma setfV n (f : {ffun 'I_n -> int64}) k v :
  setf [ffun x => Vint64 (f x)] k (Vint64 v) =
  [ffun x => Vint64 (setf f k v x)].
Proof.
rewrite /setf; case: insubP => [k' _ _|_] /=; apply/ffunP => i;
  rewrite !ffunE //; by case: eqP.
Qed.

Lemma shrink_ffun n (f : {ffun 'I_n -> int64}) i : (i < n)%nat ->
  shrink (Tint64 Unsigned) (` [ffun x => Vint64 (f x)] i) = Vint64 (` f i).
Proof. by move=> H; rewrite (fffE' _ _ H) (fffE _ _ H). Qed.

(* A write into an array of words, read back. *)
Lemma setfE n (f : {ffun 'I_n -> int64}) k v (q : 'I_n) :
  setf f k v q = if (q : nat) == k then v else f q.
Proof.
rewrite /setf; case: insubP => [k' _ Ek|Hk] /=; rewrite ?ffunE.
  by rewrite -Ek.
by case: eqP => // Eq; move: Hk; rewrite -Eq ltn_ord.
Qed.

(* a + 1 does not wrap when a is below a word b. *)
Lemma add1N (a b : int64) : (a:N < b:N)%nat ->
  (Int64.add a (Int64.repr 1)):N = (a:N).+1.
Proof.
move=> h; have Ra := Int64.unsigned_range a.
have Rb := Int64.unsigned_range_2 b.
move/ltP: h => h.
rewrite Int64.add_unsigned Int64.unsigned_repr; rewrite Int64.unsigned_repr;
  try lia.
all: rewrite /Int64.max_unsigned /= in Rb *; lia.
Qed.

(** ** The invariant of the loop of the filter

    After [i] rounds, [kept] is the number of candidates kept among the
    first [i], they are at the start of [out], and [out] is unchanged
    from position [i] on. *)

(* One round: candidate x = cs_i is kept (written at position kept) or
   not. *)
Lemma inv_step (cap : int64) (cs : seq.seq nat) (p : pred nat)
    (out1 out2 : {ffun 'I_(cap:N) -> int64}) (kept0 i0 hi : int64) :
  let fl t := seq.filter p (seq.take t cs) in
  hi:N = minn (size cs) cap:N -> (i0:N < hi:N)%nat ->
  kept0:N = size (fl i0:N) ->
  (forall q : 'I_(cap:N), (q < size (fl i0:N))%nat ->
     out2 q = Int64.repr (Z.of_nat (nth 0%nat (fl i0:N) q))) ->
  (forall q : 'I_(cap:N), (i0:N <= q)%nat -> out2 q = out1 q) ->
  let x := nth 0%nat cs i0:N in
  let out3 := if p x then setf out2 kept0:N (Int64.repr (Z.of_nat x))
              else out2 in
  let k1 := if p x then Int64.add kept0 (Int64.repr 1) else kept0 in
  let i1 := Int64.add i0 (Int64.repr 1) in
  hi:N = minn (size cs) cap:N /\ (i1:N <= hi:N)%nat /\
  k1:N = size (fl i1:N) /\
  (forall q : 'I_(cap:N), (q < size (fl i1:N))%nat ->
     out3 q = Int64.repr (Z.of_nat (nth 0%nat (fl i1:N) q))) /\
  (forall q : 'I_(cap:N), (i1:N <= q)%nat -> out3 q = out1 q).
Proof.
move=> fl Hmin Hi Hkk Hpre Hpost x out3 k1 i1.
have Hcap : (i0:N < cap:N)%nat by apply: leq_trans Hi _; rewrite Hmin geq_minr.
have Hics : (i0:N < size cs)%nat.
  by apply: leq_trans Hi _; rewrite Hmin geq_minl.
have Ei1 : i1:N = (i0:N).+1 by apply: (add1N _ cap).
have Hk : (kept0:N <= i0:N)%nat.
  rewrite Hkk /fl size_filter; apply: leq_trans (count_size _ _) _.
  by rewrite size_take; case: ltnP => // h; apply: ltnW.
have Efl : fl i1:N = fl i0:N ++ (if p x then [:: x] else [::]).
  by rewrite Ei1 /fl filter_take_S.
rewrite /k1 /out3 Efl; split; first done; split; first by rewrite Ei1.
case Px: (p x); rewrite ?cats0.
- have Ek1 : (Int64.add kept0 (Int64.repr 1)):N = (kept0:N).+1.
    by apply: (add1N _ cap); apply: leq_ltn_trans Hcap.
  rewrite Ek1 Hkk size_cat /= addn1; split; first done; split.
  + move=> q; rewrite setfE ltnS leq_eqVlt; case: eqP => [->|Hq] /=.
      by rewrite nth_cat ltnn subnn.
    by move=> hq; rewrite Hpre // nth_cat hq.
  + move=> q; rewrite Ei1 setfE => hq; case: eqP => [Eq|_]; last first.
      by apply: Hpost; apply: ltnW.
    by move: hq; rewrite Eq -Hkk ltnNge Hk.
- split; first done; split; first done.
  by move=> q; rewrite Ei1 => hq; apply: Hpost; apply: ltnW.
Qed.

(* The end of the loop: i = min(size cs, cap). *)
Lemma inv_exit (cap : int64) (cs : seq.seq nat) (p : pred nat)
    (out2 : {ffun 'I_(cap:N) -> int64}) (kept0 i0 hi : int64) :
  let fl t := seq.filter p (seq.take t cs) in
  hi:N = minn (size cs) cap:N -> (i0:N <= hi:N)%nat -> (hi:N <= i0:N)%nat ->
  kept0:N = size (fl i0:N) ->
  (forall q : 'I_(cap:N), (q < size (fl i0:N))%nat ->
     out2 q = Int64.repr (Z.of_nat (nth 0%nat (fl i0:N) q))) ->
  kept0 = Int64.repr (Z.of_nat (size (fl cap:N))) /\
  (forall q : 'I_(cap:N), (q < size (fl cap:N))%nat ->
     out2 q = Int64.repr (Z.of_nat (nth 0%nat (fl cap:N) q))).
Proof.
move=> fl Hmin Hi1 Hi2 Hkk Hpre.
have Ei : fl i0:N = fl cap:N.
  have -> : i0:N = hi:N by apply/eqP; rewrite eqn_leq Hi1 Hi2.
  by rewrite /fl Hmin take_minn.
split; last by move=> q; rewrite -Ei; exact: Hpre.
rewrite -Ei -Hkk Z2Nat.id ?Int64.repr_unsigned //.
by have := Int64.unsigned_range kept0; lia.
Qed.

(** ** The proof *)

Theorem search_filter_ok : search_spec -> search_filter_spec.
Proof.
move=> SE μ mm m Em cc cap Ec B out k l n err xb0 neg r rl
  K L N HK HL HKL Herr Hev ks.
have MH := maybe_hard_bits_ok.
subst mm cc.
have Eks : ks = kept_list L (Int64.unsigned err) (coefsA B L K) N cap:N
  (Int64.unsigned neg) (Int64.unsigned xb0) by [].
clearbody ks; revert Hev.
start; do 20 astep; envr; do 20 astep; envr.
do 30 astep; envr; do 30 astep; envr; do 30 astep; envr.
call (SE μ.-1 _ m erefl _ cap erefl).
move=> /(_ HK HL HKL Herr) [B1 [out1 [-> [-> Hout1]]]].
do 30 astep; envr; do 30 astep; envr.
set cs := cands _ _ _ _ in Hout1 *.
set fl := fun t => seq.filter (keep (Int64.unsigned neg) (Int64.unsigned xb0))
  (seq.take t cs).
have Hsz : (size cs <= n:N)%nat := cands_size _ _ _ _.
have HszZ : (Z.of_nat (size cs) < 2 ^ 64)%Z.
  by have := wordN_lt n; lia.
case Hc: (Int64.ltu cap _).
all: do 30 astep; envr; do 30 astep; envr; do 30 astep; envr.
all: inv I := { [:: out0; kept; i; _i_hi] }
  (fun (o : {ffun 'I_(cap:N) -> int64}) (kk ii hi : int64) =>
   hi:N = minn (size cs) cap:N /\ (ii:N <= hi:N)%nat /\
   kk:N = size (fl ii:N) /\
   (forall q : 'I_(cap:N), (q < size (fl ii:N))%nat ->
      o q = Int64.repr (Z.of_nat (nth 0%nat (fl ii:N) q))) /\
   (forall q : 'I_(cap:N), (ii:N <= q)%nat -> o q = out1 q)).
all: enter_loop I.
(* the invariant on entry *)
1,3: prove_inv.
1,2: exists out1; split; first reflexivity;
  do 3 (eexists; split; first reflexivity); split;
  [first [(rewrite /minn; case: ltnP => h //; move: (ltuN _ _ Hc);
             rewrite reprN //; lia)
         |(rewrite reprN //; move: (ltuNF _ _ Hc); rewrite reprN // => h;
             rewrite /minn; case: ltnP => //; lia)]
  |change ((Int64.repr 0):N) with 0%nat; rewrite /fl take0;
   split; first done; split; first done; split; [by move=> q | by []]].
(* one round of the loop *)
all: unfold_inv; move=> -[Hmin [Hi [Hkk [Hpre Hpost]]]].
all: do 10 astep; envr.
all: case END: Int64.ltu => /=.
all: first [move: (ltuN _ _ END) => END' | move: (ltuNF _ _ END) => END'].
1,3: have Hlt := END'; rewrite Hmin leq_min in Hlt;
  case/andP: Hlt => Hics Hicap; do 30 astep; envr;
  rewrite (shrink_ffun _ _ _ Hicap) (fffE _ _ Hicap).
1,2: have Ejv : out2 (Ordinal Hicap) = Int64.repr (Z.of_nat (nth 0%nat cs i0:N))
    by rewrite Hpost //= (Hout1 (Ordinal Hicap) Hics).
1,2: have hx : (nth 0%nat cs i0:N < n:N)%coq_nat
    by apply/ltP; exact: (cands_lt _ _ _ _ _ (mem_nth 0%nat Hics)).
1,2: have Hx : (0 <= Z.of_nat (nth 0%nat cs i0:N) < 2 ^ 64)%Z
    by have := wordN_lt n; lia.
1,2: rewrite Ejv; do 30 astep; envr;
  case EN: (Int64.eq neg (Int64.repr 0)) => /=; do 30 astep; envr.
(* the call of maybe_hard_bits *)
1,2,3,4: do 5 astep; envr; rewrite/call/= /envC/=; try evalf;
  case x: eval_func => [[v rlv]|]; last by [];
  move/MH: x => -[-> ->];
  first [rewrite (xb_add _ _ _ Hx EN) | rewrite (xb_sub _ _ _ Hx EN)];
  do 30 astep; envr.
1,2,3,4: rewrite (eq_mh _ (maybe_hard_Z_range _)).
1,2,3,4: case ER: (Z.eqb _ 1).
all: do 30 astep; envr.
(* the write into out, then the end of the round *)
all: try rewrite setfV.
all: do 30 astep; envr.
all: try (lazymatch goal with |- ⟦ ret Onormal ⟧ => _ -> _ => idtac end;
  cret; split=> // _; split; [solve_loop_conditions|prove_inv]).
(* the invariant after one round *)
all: try (lazymatch goal with |- ∃ _ : {ffun _}, _ => idtac end;
  have ER' : keep (Int64.unsigned neg) (Int64.unsigned xb0)
               (nth 0%nat cs i0:N) = _ := ER;
  have := inv_step cap cs (keep (Int64.unsigned neg) (Int64.unsigned xb0))
            out1 out2 kept0 i0 _ Hmin END' Hkk Hpre Hpost;
  cbv zeta; rewrite ER' => -[A1 [A2 [A3 [A4 A5]]]];
  do 4 (eexists; split; first reflexivity); by repeat split).
(* the end of the loop and the return *)
all: cret; split=> //= _; do 10 astep; envr; fin.
all: have [Ek Hk] := inv_exit cap cs
  (keep (Int64.unsigned neg) (Int64.unsigned xb0)) out2 kept0 i0 _
  Hmin Hi END' Hkk Hpre.
all: exists B1, out2; split; first reflexivity.
all: rewrite Eks Ek; split; [reflexivity | exact: Hk].
Qed.
