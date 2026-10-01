(** * The lines of the table cover a whole range of doubles

    A line [(x0, n, B)], [x0 = S0 2^(ex - 52)], covers the doubles
    [(S0 + j) 2^(ex - 52)], [j = 0 .. n - drop] (see [closed] in
    [ExpCheck]); the last one is [SL = S0 + n - drop].  [contig] checks
    on the text that each line stays in one binade and starts at the
    double right after the last one of the previous line; then the lines
    hold every double from the first [x0] to the last [SL].  The next
    double is not always [x0 + n u]: going up from a negative [x] that
    crosses a binade, [u] halves.  Only [parse] is
    evaluated, never [exp].  [joins] lets the table be checked one file
    at a time. *)

From Stdlib Require Import ZArith Reals Lia Lra List Bool PrimString.
From Flocq Require Import Core.
From ExpTable9 Require Import ExpCheck ExpParse.
Import ListNotations.

Open Scope Z_scope.

(** ** Doubles *)

(** [S] is the signed significand of a normal double. *)
Definition normal (S : Z) : Prop := 2 ^ 52 <= Z.abs S < 2 ^ 53.

(** The value [S 2^(ex - 52)] of the double [(S, ex)]. *)
Definition val (S ex : Z) : R := (IZR S * bp (uexp ex))%R.

(** The next double upwards, for [S] normal; towards 0 when [S < 0]. *)
Definition next (S ex : Z) : Z * Z :=
  if Z.eqb S (- 2 ^ 52) then (- (2 ^ 53 - 1), ex - 1)
  else if Z.eqb (S + 1) (2 ^ 53) then (2 ^ 52, ex + 1)
  else (S + 1, ex).

(** ** The check *)

(** The doubles [S0 .. S0 + n] are normal, with the same sign. *)
Definition inbin (S0 n : Z) : bool :=
  Z.leb 0 n && Z.leb (2 ^ 52) (Z.abs S0) && Z.ltb (Z.abs S0) (2 ^ 53) &&
  Z.leb (2 ^ 52) (Z.abs (S0 + n)) && Z.ltb (Z.abs (S0 + n)) (2 ^ 53) &&
  (Z.ltb 0 S0 || Z.ltb (S0 + n) 0).

(** Every line parses and stays in a binade, the first one starts at
    [p], each next one at the double after the end of the previous. *)
Fixpoint chain (p : Z * Z) (ls : list string) : bool :=
  match ls with
  | [] => true
  | s :: ls' =>
    match parse s with
    | Some (S0, ex, n, _) =>
      Z.eqb S0 (fst p) && Z.eqb ex (snd p) && inbin S0 (n - drop) &&
      chain (next (S0 + (n - drop)) ex) ls'
    | None => false
    end
  end.

(** The first double [x0] of the first line. *)
Definition firstX (ls : list string) : Z * Z :=
  match ls with
  | s :: _ =>
    match parse s with Some (S0, ex, _, _) => (S0, ex) | None => (0, 0) end
  | [] => (0, 0)
  end.

(** The last double [SL] of the last line. *)
Fixpoint lastX (ls : list string) : Z * Z :=
  match ls with
  | [] => (0, 0)
  | s :: ls' =>
    match ls' with
    | [] =>
      match parse s with
      | Some (S0, ex, n, _) => (S0 + (n - drop), ex)
      | None => (0, 0)
      end
    | _ => lastX ls'
    end
  end.

(** The lines are not empty and follow each other. *)
Definition contig (ls : list string) : bool :=
  match ls with [] => false | _ => chain (firstX ls) ls end.

(** Equality of two doubles. *)
Definition eqX (p q : Z * Z) : bool :=
  Z.eqb (fst p) (fst q) && Z.eqb (snd p) (snd q).

(** Each list starts at the double after the end of the previous one. *)
Fixpoint joins (Ls : list (list string)) : bool :=
  match Ls with
  | [] => true
  | l1 :: Ls' =>
    match Ls' with
    | [] => true
    | l2 :: _ =>
      eqX (next (fst (lastX l1)) (snd (lastX l1))) (firstX l2) && joins Ls'
    end
  end.

(** Every line of [ls] reads as a line that satisfies the six
    conditions. *)
Definition lines_good (ls : list string) : Prop :=
  forall s, In s ls -> exists S0 ex n B,
    parse s = Some (S0, ex, n, B) /\ line_ok S0 ex n B.

(** ** The rank of a double *)

(** The doubles of one sign, in increasing order, have consecutive
    ranks. *)
Definition rank (S ex : Z) : Z :=
  if Z.ltb 0 S then ex * 2 ^ 52 + S else S - ex * 2 ^ 52.

Lemma p52 : 2 ^ 52 = 4503599627370496.
Proof. reflexivity. Qed.

Lemma p53 : 2 ^ 53 = 2 * 4503599627370496.
Proof. reflexivity. Qed.

(** The next double is normal, has the same sign and the next rank. *)
Lemma next_ok S ex : normal S ->
  normal (fst (next S ex)) /\ (0 < S <-> 0 < fst (next S ex)) /\
  rank (fst (next S ex)) (snd (next S ex)) = rank S ex + 1.
Proof.
intros hS; unfold next.
destruct (Z.eqb_spec S (- 2 ^ 52)) as [h1|h1];
  [|destruct (Z.eqb_spec (S + 1) (2 ^ 53)) as [h2|h2]];
  cbn [fst snd]; unfold normal, rank in *; rewrite ?p53, ?p52 in *;
  repeat match goal with |- context [Z.ltb ?a ?b] =>
    destruct (Z.ltb_spec a b) end; lia.
Qed.

Lemma bp_pos e : (0 < bp e)%R.
Proof. apply bpow_gt_0. Qed.

(** A positive normal double is in [[2^ex, 2^(ex+1))]. *)
Lemma val_bnd S ex : 2 ^ 52 <= S < 2 ^ 53 ->
  (bp ex <= val S ex < bp (ex + 1))%R.
Proof.
intros hS; unfold val, uexp, prec.
assert (h52 : bp ex = (IZR (2 ^ 52) * bp (ex - (53 - 1)))%R).
{ change (2 ^ 52) with (Zpower radix2 52); rewrite IZR_Zpower by lia.
  unfold bp; rewrite <- bpow_plus; f_equal; lia. }
assert (h53 : bp (ex + 1) = (IZR (2 ^ 53) * bp (ex - (53 - 1)))%R).
{ change (2 ^ 53) with (Zpower radix2 53); rewrite IZR_Zpower by lia.
  unfold bp; rewrite <- bpow_plus; f_equal; lia. }
rewrite h52, h53.
assert (hu := bp_pos (ex - (53 - 1))).
split; [apply Rmult_le_compat_r; [lra|apply IZR_le; lia]|].
apply Rmult_lt_compat_r; [lra|apply IZR_lt; lia].
Qed.

(** On positive normal doubles, the rank orders the values. *)
Lemma val_lt_pos Sa ea Sb eb :
  2 ^ 52 <= Sa < 2 ^ 53 -> 2 ^ 52 <= Sb < 2 ^ 53 ->
  ea * 2 ^ 52 + Sa < eb * 2 ^ 52 + Sb -> (val Sa ea < val Sb eb)%R.
Proof.
intros ha hb hr.
destruct (Z.lt_trichotomy ea eb) as [he|[he|he]].
- destruct (val_bnd _ ea ha) as [_ h1].
  destruct (val_bnd _ eb hb) as [h2 _].
  assert (bp (ea + 1) <= bp eb)%R by (apply bpow_le; lia).
  lra.
- subst eb; unfold val; apply Rmult_lt_compat_r; [apply bp_pos|].
  apply IZR_lt; lia.
- rewrite p53, p52 in *; lia.
Qed.

(** On normal doubles of one sign, the rank orders the values. *)
Lemma val_lt Sa ea Sb eb : normal Sa -> normal Sb -> (0 < Sa <-> 0 < Sb) ->
  rank Sa ea < rank Sb eb -> (val Sa ea < val Sb eb)%R.
Proof.
unfold normal, rank; intros ha hb hs hr.
destruct (Z.ltb_spec 0 Sa); destruct (Z.ltb_spec 0 Sb); [|lia|lia|].
- apply val_lt_pos; lia.
- assert (h : (val (- Sb) eb < val (- Sa) ea)%R) by (apply val_lt_pos; lia).
  unfold val in *; rewrite !opp_IZR in h; lra.
Qed.

(** On normal doubles of one sign, the rank tells them apart. *)
Lemma rank_inj Sa ea Sb eb : normal Sa -> normal Sb ->
  (0 < Sa <-> 0 < Sb) -> rank Sa ea = rank Sb eb -> Sa = Sb /\ ea = eb.
Proof.
unfold normal, rank; rewrite p53, p52; intros ha hb hs hr.
destruct (Z.ltb_spec 0 Sa); destruct (Z.ltb_spec 0 Sb); lia.
Qed.

(** A rank between those of [S0] and [S0 + n], normal and of one sign,
    is that of a double [(S, ex)] with [S0 <= S <= S0 + n]. *)
Lemma rank_line S0 ex0 n S ex : 0 <= n -> normal S0 -> normal (S0 + n) ->
  normal S -> (0 < S0 <-> 0 < S0 + n) -> (0 < S0 <-> 0 < S) ->
  rank S0 ex0 <= rank S ex <= rank S0 ex0 + n ->
  ex = ex0 /\ S0 <= S <= S0 + n.
Proof.
unfold normal, rank; rewrite p53, p52; intros hn h0 h1 hS hs1 hs hr.
destruct (Z.ltb_spec 0 S0); destruct (Z.ltb_spec 0 S); lia.
Qed.

(** ** Coverage of one list *)

Lemma inbinP S0 n : inbin S0 n = true ->
  0 <= n /\ normal S0 /\ normal (S0 + n) /\ (0 < S0 <-> 0 < S0 + n).
Proof.
unfold inbin, normal; intros h.
destruct (Z.leb_spec 0 n), (Z.leb_spec (2 ^ 52) (Z.abs S0)),
  (Z.ltb_spec (Z.abs S0) (2 ^ 53)), (Z.leb_spec (2 ^ 52) (Z.abs (S0 + n))),
  (Z.ltb_spec (Z.abs (S0 + n)) (2 ^ 53)), (Z.ltb_spec 0 S0),
  (Z.ltb_spec (S0 + n) 0); cbn [andb orb] in h; try discriminate; lia.
Qed.

(** The rank of the end of a line. *)
Lemma rank_end S0 ex n : 0 <= n -> normal S0 -> normal (S0 + n) ->
  (0 < S0 <-> 0 < S0 + n) -> rank (S0 + n) ex = rank S0 ex + n.
Proof.
unfold normal, rank; intros hn h0 h1 hs.
destruct (Z.ltb_spec 0 S0); destruct (Z.ltb_spec 0 (S0 + n)); lia.
Qed.

(** The last double of a chain is normal, with the sign of the first. *)
Lemma chain_last p ls : chain p ls = true -> ls <> [] -> normal (fst p) ->
  normal (fst (lastX ls)) /\ (0 < fst p <-> 0 < fst (lastX ls)).
Proof.
revert p; induction ls as [|s ls IH]; intros p h hne hp; [congruence|].
cbn [chain] in h.
destruct (parse s) as [[[[S0 ex] n] B]|] eqn:hs; [|discriminate].
apply andb_prop in h as [h hc]; apply andb_prop in h as [h hb].
apply andb_prop in h as [h1 h2]; apply Z.eqb_eq in h1, h2.
destruct (inbinP _ _ hb) as [hn [h0 [hl hsg]]].
destruct ls as [|s' ls'].
- cbn [lastX]; rewrite hs; cbn [fst]; rewrite <- h1; tauto.
- change (lastX (s :: s' :: ls')) with (lastX (s' :: ls')).
  destruct (next_ok (S0 + (n - drop)) ex hl) as [hn1 [hs1 _]].
  destruct (IH _ hc ltac:(discriminate) hn1) as [hl2 hs2].
  split; [exact hl2|rewrite <- h1; tauto].
Qed.

(** Every double [(S, ex)] of the sign of [p], ranked from [p] to the
    last double of the chain, is in a line. *)
Lemma chain_cover p ls S ex : chain p ls = true -> ls <> [] ->
  normal (fst p) -> normal S -> (0 < fst p <-> 0 < S) ->
  rank (fst p) (snd p) <= rank S ex <=
    rank (fst (lastX ls)) (snd (lastX ls)) ->
  exists s S0 n B, In s ls /\ parse s = Some (S0, ex, n, B) /\
    S0 <= S <= S0 + (n - drop).
Proof.
revert p; induction ls as [|s ls IH]; intros p h hne hp hS hsg hr;
  [congruence|].
cbn [chain] in h.
destruct (parse s) as [[[[S0 ex0] n] B]|] eqn:hs; [|discriminate].
apply andb_prop in h as [h hc]; apply andb_prop in h as [h hb].
apply andb_prop in h as [h1 h2]; apply Z.eqb_eq in h1, h2.
destruct p as [Sp ep]; cbn [fst snd] in *; subst Sp ep.
destruct (inbinP _ _ hb) as [hn [h0 [hl hsl]]].
assert (he := rank_end S0 ex0 (n - drop) hn h0 hl hsl).
destruct (Z_le_gt_dec (rank S ex) (rank S0 ex0 + (n - drop))) as [hle|hgt].
- destruct (rank_line S0 ex0 (n - drop) S ex hn h0 hl hS hsl hsg ltac:(lia))
    as [-> hr2].
  exists s, S0, n, B; split; [left; reflexivity|split; [exact hs|exact hr2]].
- destruct ls as [|s' ls'].
  + cbn [lastX] in hr; rewrite hs in hr; cbn [fst snd] in hr; lia.
  + change (lastX (s :: s' :: ls')) with (lastX (s' :: ls')) in hr.
    destruct (next_ok (S0 + (n - drop)) ex0 hl) as [hn1 [hs1 hr1]].
    destruct (IH _ hc ltac:(discriminate) hn1 hS ltac:(tauto)
      ltac:(lia)) as [t [S1 [n1 [B1 [ht [hp1 hr3]]]]]].
    exists t, S1, n1, B1; split; [right; exact ht|split; assumption].
Qed.

(** ** Joining lists *)

Lemma chain_app p l1 l2 : chain p l1 = true -> l1 <> [] ->
  chain (next (fst (lastX l1)) (snd (lastX l1))) l2 = true ->
  chain p (l1 ++ l2) = true.
Proof.
revert p; induction l1 as [|s l1 IH]; intros p h hne h2; [congruence|].
cbn [chain app] in h |- *.
destruct (parse s) as [[[[S0 ex] n] B]|] eqn:hs; [|discriminate].
apply andb_prop in h as [h hc]; rewrite h; cbn [andb].
destruct l1 as [|s' l1].
- cbn [lastX] in h2; rewrite hs in h2; exact h2.
- apply IH; [exact hc|discriminate|exact h2].
Qed.

Lemma lastX_app l1 l2 : l2 <> [] -> lastX (l1 ++ l2) = lastX l2.
Proof.
intros hne; induction l1 as [|s l1 IH]; [reflexivity|].
destruct l1 as [|s' l1]; [|exact IH].
destruct l2; [congruence|reflexivity].
Qed.

Lemma contig_nil ls : contig ls = true -> ls <> [].
Proof. destruct ls; [discriminate|intros _; discriminate]. Qed.

Lemma eqXP p q : eqX p q = true -> p = q.
Proof.
destruct p, q; unfold eqX; cbn [fst snd]; intros h.
apply andb_prop in h as [h1 h2]; apply Z.eqb_eq in h1, h2; congruence.
Qed.

Theorem contig_app l1 l2 : contig l1 = true -> contig l2 = true ->
  next (fst (lastX l1)) (snd (lastX l1)) = firstX l2 ->
  contig (l1 ++ l2) = true /\ firstX (l1 ++ l2) = firstX l1 /\
  lastX (l1 ++ l2) = lastX l2.
Proof.
intros h1 h2 hj.
assert (hf : firstX (l1 ++ l2) = firstX l1)
  by (destruct l1; [discriminate|reflexivity]).
split; [|split; [exact hf|apply lastX_app, contig_nil, h2]].
destruct l1 as [|s l1]; [discriminate|].
change (chain (firstX ((s :: l1) ++ l2)) ((s :: l1) ++ l2) = true).
rewrite hf.
apply chain_app; [exact h1|discriminate|].
destruct l2 as [|s' l2]; [discriminate|].
rewrite hj; exact h2.
Qed.

Lemma last_indep (l1 : list string) Ls d d' :
  last (l1 :: Ls) d = last (l1 :: Ls) d'.
Proof.
revert l1; induction Ls as [|l2 Ls IH]; intros l1; [reflexivity|].
exact (IH l2).
Qed.

Lemma last_cons (l0 l1 : list string) Ls :
  last (l1 :: Ls) l0 = last Ls l1.
Proof.
destruct Ls as [|l2 Ls]; [reflexivity|]; cbn [last]; apply last_indep.
Qed.

Theorem contig_concat l0 Ls :
  Forall (fun l => contig l = true) (l0 :: Ls) ->
  joins (l0 :: Ls) = true ->
  contig (concat (l0 :: Ls)) = true /\
  firstX (concat (l0 :: Ls)) = firstX l0 /\
  lastX (concat (l0 :: Ls)) = lastX (last Ls l0).
Proof.
revert l0; induction Ls as [|l1 Ls IH]; intros l0 hc hj.
- cbn [concat]; rewrite app_nil_r.
  inversion hc; subst; split; [assumption|split; reflexivity].
- inversion hc as [|x y h0 hc1]; subst.
  cbn [joins] in hj; apply andb_prop in hj as [hb hj].
  apply eqXP in hb.
  destruct (IH l1 hc1 hj) as [hc2 [hf2 hl2]].
  change (concat (l0 :: l1 :: Ls)) with (l0 ++ concat (l1 :: Ls)).
  rewrite <- hf2 in hb.
  destruct (contig_app l0 (concat (l1 :: Ls)) h0 hc2 hb) as [hc3 [hf3 hl3]].
  rewrite last_cons, <- hl2; split; [exact hc3|split; assumption].
Qed.

(** ** Coverage of the table *)

(** If the lists [l0 :: Ls] are each contiguous, join, and hold good
    lines, every normal double [y] between the first [x0] and the last
    double [SL u] is a double [x0 + j u], [0 <= j <= n - drop], of a line
    that satisfies the six conditions. *)
Theorem cover_ok l0 Ls :
  Forall (fun l => contig l = true) (l0 :: Ls) ->
  Forall lines_good (l0 :: Ls) ->
  joins (l0 :: Ls) = true ->
  forall S ex, normal S ->
  (val (fst (firstX l0)) (snd (firstX l0)) <= val S ex <=
   val (fst (lastX (last Ls l0))) (snd (lastX (last Ls l0))))%R ->
  exists s S0 n B, In s (concat (l0 :: Ls)) /\
    parse s = Some (S0, ex, n, B) /\ line_ok S0 ex n B /\
    S0 <= S <= S0 + n - drop /\
    (IZR S0 * bp (uexp ex) <= IZR S * bp (uexp ex) <=
     IZR (S0 + n - drop) * bp (uexp ex))%R.
Proof.
intros hc hg hj S ex hS hy.
destruct (contig_concat l0 Ls hc hj) as [hc1 [hf hl]].
rewrite <- hf, <- hl in hy.
set (L := concat (l0 :: Ls)) in *.
assert (hne : L <> []) by exact (contig_nil _ hc1).
assert (hc2 : chain (firstX L) L = true)
  by (destruct L; [congruence|exact hc1]).
(* The first double is normal. *)
assert (hp : normal (fst (firstX L))).
{ destruct L as [|s L']; [congruence|].
  cbn [chain] in hc2; cbn [firstX] in hc2 |- *.
  destruct (parse s) as [[[[S0 ex0] n] B]|]; [|discriminate].
  apply andb_prop in hc2 as [h _]; apply andb_prop in h as [_ hb].
  apply inbinP in hb; cbn [fst]; tauto. }
destruct (chain_last _ _ hc2 hne hp) as [hl1 hsl].
destruct (firstX L) as [Sa ea] eqn:ha0.
destruct (lastX L) as [Sb eb] eqn:hb0; cbn [fst snd] in *.
(* y has the sign of the ends. *)
assert (hsg : 0 < Sa <-> 0 < S).
{ unfold val in hy; assert (hu := bp_pos (uexp ex)).
  assert (hua := bp_pos (uexp ea)); assert (hub := bp_pos (uexp eb)).
  unfold normal in *.
  destruct (Z.ltb_spec 0 Sa) as [ha|ha]; destruct (Z.ltb_spec 0 S) as [h|h];
    try (split; intros; lia).
  - assert (0 < IZR Sa)%R by (apply IZR_lt; lia).
    assert (IZR S <= 0)%R by (apply IZR_le; lia).
    nra.
  - assert (Sb < 0) by (destruct hsl; lia).
    assert (IZR Sb < 0)%R by (apply IZR_lt; lia).
    assert (0 < IZR S)%R by (apply IZR_lt; lia).
    nra. }
assert (hr : rank Sa ea <= rank S ex <= rank Sb eb).
{ split; apply Z.nlt_ge; intros h.
  - assert (val S ex < val Sa ea)%R by (apply val_lt; tauto).
    lra.
  - assert (val Sb eb < val S ex)%R by (apply val_lt; tauto).
    lra. }
destruct (chain_cover (Sa, ea) L S ex hc2 hne hp hS hsg
  ltac:(rewrite hb0; exact hr))
  as [s [S0 [n [B [hs [hps hr2]]]]]].
exists s, S0, n, B; split; [exact hs|split; [exact hps|]].
split.
- apply in_concat in hs as [l [hl0 hsl0]].
  rewrite Forall_forall in hg.
  destruct (hg l hl0 s hsl0) as [S1 [ex1 [n1 [B1 [hp1 hok]]]]].
  rewrite hps in hp1; injection hp1 as -> -> -> ->; exact hok.
- split; [lia|].
  assert (hu := bp_pos (uexp ex)).
  split; apply Rmult_le_compat_r; try lra; apply IZR_le; lia.
Qed.
