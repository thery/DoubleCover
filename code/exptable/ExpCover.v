(** * The lines of the table cover a whole range of inputs

    A line [(M0, n, B)] covers the significands [M0 .. M0 + n], that is
    the inputs [x0 + j u] for [j = 0 .. n].  [contig] checks, on the
    text, that each line starts one [u] after the end of the previous
    one, so that the lines together cover every significand from the
    first [M0] to the last [M0 + n].  Only [parse] is evaluated, never
    [exp].  [joins] lets the table be checked in slices. *)

From Stdlib Require Import ZArith Lia List Bool PrimString.
From ExpTable Require Import ExpCheck ExpParse.
Import ListNotations.

Open Scope Z_scope.

(** ** The check *)

(** The first significand of the first line. *)
Definition firstM (ls : list string) : Z :=
  match ls with
  | s :: _ => match parse s with Some (M0, _, _) => M0 | None => 0 end
  | [] => 0
  end.

(** The last significand of the last line. *)
Fixpoint lastM (ls : list string) : Z :=
  match ls with
  | [] => 0
  | s :: ls' =>
    match ls' with
    | [] => match parse s with Some (M0, n, _) => M0 + n | None => 0 end
    | _ => lastM ls'
    end
  end.

(** Every line parses, the first starts at [nxt], each next one starts
    right after the end of the previous one. *)
Fixpoint chain (nxt : Z) (ls : list string) : bool :=
  match ls with
  | [] => true
  | s :: ls' =>
    match parse s with
    | Some (M0, n, _) => Z.eqb M0 nxt && chain (M0 + n + 1) ls'
    | None => false
    end
  end.

(** The lines are not empty and follow each other. *)
Definition contig (ls : list string) : bool :=
  match ls with [] => false | _ => chain (firstM ls) ls end.

(** Each list starts right after the end of the previous one. *)
Fixpoint joins (Ls : list (list string)) : bool :=
  match Ls with
  | [] => true
  | l1 :: Ls' =>
    match Ls' with
    | [] => true
    | l2 :: _ => Z.eqb (firstM l2) (lastM l1 + 1) && joins Ls'
    end
  end.

(** Every line of [ls] reads as a line that satisfies the six
    conditions. *)
Definition lines_good (ls : list string) : Prop :=
  forall s, In s ls -> exists M0 n B,
    parse s = Some (M0, n, B) /\ line_ok M0 n B.

(** ** Coverage of one list *)

Lemma chain_cover nxt ls M : chain nxt ls = true -> ls <> [] ->
  nxt <= M <= lastM ls ->
  exists s M0 n B, In s ls /\ parse s = Some (M0, n, B) /\
    M0 <= M <= M0 + n.
Proof.
revert nxt; induction ls as [|s ls IH]; intros nxt h hne hM;
  [congruence|].
cbn [chain] in h.
destruct (parse s) as [[[M0 n] B]|] eqn:hs; [|discriminate].
apply andb_prop in h as [h1 h2]; apply Z.eqb_eq in h1; subst nxt.
destruct (Z_le_gt_dec M (M0 + n)) as [hle|hgt].
- exists s, M0, n, B; split; [left; reflexivity|split; [exact hs|lia]].
- destruct ls as [|s' ls'].
  + cbn [lastM] in hM; rewrite hs in hM; lia.
  + change (lastM (s :: s' :: ls')) with (lastM (s' :: ls')) in hM.
    destruct (IH (M0 + n + 1) h2 ltac:(discriminate) ltac:(lia))
      as [t [M1 [n1 [B1 [ht [hp hr]]]]]].
    exists t, M1, n1, B1; split; [right; exact ht|split; [exact hp|exact hr]].
Qed.

Theorem contig_cover ls M : contig ls = true ->
  firstM ls <= M <= lastM ls ->
  exists s M0 n B, In s ls /\ parse s = Some (M0, n, B) /\
    M0 <= M <= M0 + n.
Proof.
destruct ls as [|s ls]; [discriminate|].
intros h hM.
apply (chain_cover (firstM (s :: ls))); [exact h|discriminate|exact hM].
Qed.

(** ** Joining two lists *)

Lemma chain_app nxt l1 l2 : chain nxt l1 = true -> l1 <> [] ->
  chain (lastM l1 + 1) l2 = true -> chain nxt (l1 ++ l2) = true.
Proof.
revert nxt; induction l1 as [|s l1 IH]; intros nxt h hne h2;
  [congruence|].
cbn [chain app] in h |- *.
destruct (parse s) as [[[M0 n] B]|] eqn:hs; [|discriminate].
apply andb_prop in h as [h1 h]; rewrite h1; cbn [andb].
destruct l1 as [|s' l1].
- cbn [lastM] in h2; rewrite hs in h2; exact h2.
- apply IH; [exact h|discriminate|exact h2].
Qed.

Lemma lastM_app l1 l2 : l2 <> [] -> lastM (l1 ++ l2) = lastM l2.
Proof.
intros hne; induction l1 as [|s l1 IH]; [reflexivity|].
destruct l1 as [|s' l1]; [|exact IH].
destruct l2; [congruence|reflexivity].
Qed.

Lemma contig_nil ls : contig ls = true -> ls <> [].
Proof. destruct ls; [discriminate|intros _; discriminate]. Qed.

Theorem contig_app l1 l2 : contig l1 = true -> contig l2 = true ->
  firstM l2 = lastM l1 + 1 ->
  contig (l1 ++ l2) = true /\ firstM (l1 ++ l2) = firstM l1 /\
  lastM (l1 ++ l2) = lastM l2.
Proof.
intros h1 h2 hj.
assert (hf : firstM (l1 ++ l2) = firstM l1)
  by (destruct l1; [discriminate|reflexivity]).
split; [|split; [exact hf|apply lastM_app, contig_nil, h2]].
destruct l1 as [|s l1]; [discriminate|].
change (chain (firstM ((s :: l1) ++ l2)) ((s :: l1) ++ l2) = true).
rewrite hf.
apply chain_app; [exact h1|discriminate|].
destruct l2 as [|s' l2]; [discriminate|].
rewrite <- hj; exact h2.
Qed.

(** ** Joining many lists *)

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
  firstM (concat (l0 :: Ls)) = firstM l0 /\
  lastM (concat (l0 :: Ls)) = lastM (last Ls l0).
Proof.
revert l0; induction Ls as [|l1 Ls IH]; intros l0 hc hj.
- cbn [concat]; rewrite app_nil_r.
  inversion hc; subst; split; [assumption|split; reflexivity].
- inversion hc as [|x y h0 hc1]; subst.
  cbn [joins] in hj; apply andb_prop in hj as [hb hj].
  apply Z.eqb_eq in hb.
  destruct (IH l1 hc1 hj) as [hc2 [hf2 hl2]].
  change (concat (l0 :: l1 :: Ls)) with (l0 ++ concat (l1 :: Ls)).
  destruct (contig_app l0 (concat (l1 :: Ls)) h0 hc2 ltac:(lia))
    as [hc3 [hf3 hl3]].
  rewrite last_cons, <- hl2; split; [exact hc3|split; assumption].
Qed.

(** ** Coverage of the table *)

(** If the slices [l0 :: Ls] are each contiguous, join, and hold good
    lines, every significand from the first [M0] to the last [M0 + n]
    is in the range of a line that satisfies the six conditions. *)
Theorem cover_ok l0 Ls :
  Forall (fun l => contig l = true) (l0 :: Ls) ->
  Forall lines_good (l0 :: Ls) ->
  joins (l0 :: Ls) = true ->
  forall M, firstM l0 <= M <= lastM (last Ls l0) ->
  exists s M0 n B, In s (concat (l0 :: Ls)) /\
    parse s = Some (M0, n, B) /\ line_ok M0 n B /\ M0 <= M <= M0 + n.
Proof.
intros hc hg hj M hM.
destruct (contig_concat l0 Ls hc hj) as [hc1 [hf hl]].
rewrite <- hf, <- hl in hM.
destruct (contig_cover _ M hc1 hM) as [s [M0 [n [B [hs [hp hr]]]]]].
exists s, M0, n, B; split; [exact hs|split; [exact hp|split; [|exact hr]]].
apply in_concat in hs as [l [hl0 hsl]].
rewrite Forall_forall in hg.
destruct (hg l hl0 s hsl) as [M1 [n1 [B1 [hp1 hok]]]].
rewrite hp in hp1; injection hp1 as -> -> ->; exact hok.
Qed.
