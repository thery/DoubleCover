(** * What a line of the table says, and [parse] reads exactly that

    A line of [in_lt] is the text

      0x1.F p+X N 0xW_0 0xW_1 ... 0xW_(k l - 1)

    with single spaces between the fields (none inside [0x1.Fp+X]):
    [F] is 1 to 13 hexadecimal digits, [X] decimal digits of value
    [xbin], [N] decimal digits and each [W_j] hexadecimal digits.  So
    [x0 = (1 + F / 16^|F|) 2^xbin]; with
    [M0 = 16^13 + F 16^(13 - |F|)] this is [x0 = M0 2^-52 2^xbin], that
    is [x0 = M0 2^uexp] as [uexp = xbin - 52].  The line gives [n = N],
    and [B_i = w_(i l) + w_(i l + 1) beta + ... + w_(i l + l - 1)
    beta^(l-1)] for [i < k], [w_j] being the value of [W_j].

    [line_text] states this; [parse_sound] proves that whatever [parse]
    returns is what the text says.  A character is its code, an [int]. *)

From Stdlib Require Import PrimString PrimStringAxioms Uint63.
From ExpTable Require Import ExpCheck ExpParse.
From Stdlib Require Import ZArith List Lia.
Import ListNotations.

Open Scope Z_scope.

(** ** Digits and numbers *)

(** The characters [c_0], [c_a], ... are those of [ExpParse]. *)

(** [c] is the decimal digit of value [d]: '0' .. '9'. *)
Definition decdigit (c : int) (d : Z) : Prop :=
  0 <= d <= 9 /\ to_Z c = to_Z c_0 + d.

(** [c] is the hexadecimal digit of value [d]: '0' .. '9', 'a' .. 'f'. *)
Definition hexdigit (c : int) (d : Z) : Prop :=
  decdigit c d \/ (10 <= d <= 15 /\ to_Z c = to_Z c_a + (d - 10)).

(** [d_0 b^(len-1) + d_1 b^(len-2) + ... + d_(len-1)], most significant
    first. *)
Fixpoint value (b : Z) (ds : list Z) : Z :=
  match ds with
  | [] => 0
  | d :: ds' => d * b ^ Z.of_nat (length ds') + value b ds'
  end.

(** [cs] is a nonempty decimal numeral of value [v]. *)
Definition dec_text (cs : list int) (v : Z) : Prop :=
  cs <> [] /\ exists ds, Forall2 decdigit cs ds /\ v = value 10 ds.

(** [cs] is a nonempty hexadecimal numeral of value [v]. *)
Definition hex_text (cs : list int) (v : Z) : Prop :=
  cs <> [] /\ exists ds, Forall2 hexdigit cs ds /\ v = value 16 ds.

(** [W] is a word [0xhh...h] of value [w]. *)
Definition word_text (W : list int) (w : Z) : Prop :=
  exists H, W = c_0 :: c_x :: H /\ hex_text H w.

(** [f 0 + f 1 + ... + f (N-1)]. *)
Fixpoint sumZ (f : nat -> Z) (N : nat) : Z :=
  match N with O => 0 | S N' => sumZ f N' + f N' end.

(** ** A line *)

Definition frac_digits : nat := 13.  (* hex digits of a binary64 fraction *)

(** [cs] is the line [0x1.Fp+X N W_0 ... W_(k l - 1)] of [(M0, n, B)]. *)
Definition line_text (cs : list int) (M0 n : Z) (B : list Z) : Prop :=
  exists F f X N Ws ws,
  cs = [c_0; c_x; c_1; c_dot] ++ F ++ [c_p; c_plus] ++ X ++
       c_space :: N ++ concat (map (fun W => c_space :: W) Ws) /\
  (* x0 = 0x1.Fp+X, 1 to 13 digits after the point, X = xbin *)
  hex_text F f /\ (length F <= frac_digits)%nat /\
  M0 = 16 ^ Z.of_nat frac_digits +
       f * 16 ^ (Z.of_nat frac_digits - Z.of_nat (length F)) /\
  dec_text X xbin /\
  (* n = N *)
  dec_text N n /\
  (* the k l words w_j *)
  length Ws = (k * Z.to_nat l)%nat /\ Forall2 word_text Ws ws /\
  (* B_i = sum_(j < l) w_(i l + j) beta^j *)
  B = map (fun i => sumZ (fun j => nth (i * Z.to_nat l + j) ws 0 *
                                   beta ^ Z.of_nat j) (Z.to_nat l))
          (seq 0 k).

(** ** Proofs *)

Lemma decdP c d : decd c = Some d -> decdigit c d.
Proof.
unfold decd, decdigit.
destruct ((c_0 <=? c)%uint63 && (c <=? c_9)%uint63) eqn:E1; [|discriminate].
intros [= <-]; apply andb_prop in E1 as [E1 E2].
apply leb_spec in E1, E2.
pose proof (to_Z_bounded c) as Hc.
change (to_Z c_0) with 48 in *; change (to_Z c_9) with 57 in *.
rewrite sub_spec; change (to_Z c_0) with 48.
rewrite Z.mod_small; lia.
Qed.

Lemma hexdP c d : hexd c = Some d -> hexdigit c d.
Proof.
unfold hexd, hexdigit.
destruct ((c_0 <=? c)%uint63 && (c <=? c_9)%uint63) eqn:E1.
{ intros H; left; apply decdP; unfold decd; rewrite E1; exact H. }
destruct ((c_a <=? c)%uint63 && (c <=? c_f)%uint63) eqn:E2; [|discriminate].
intros [= <-]; right; apply andb_prop in E2 as [E2 E3].
apply leb_spec in E2, E3.
pose proof (to_Z_bounded c) as Hc.
change (to_Z c_a) with 97 in *; change (to_Z c_f) with 102 in *.
rewrite sub_spec; change (to_Z c_a) with 97.
rewrite Z.mod_small; lia.
Qed.

Lemma digitsP d b acc cs v : digits d b acc cs = Some v ->
  exists ds, Forall2 (fun c x => d c = Some x) cs ds /\
             v = acc * b ^ Z.of_nat (length cs) + value b ds.
Proof.
revert acc; induction cs as [|c cs IH]; intros acc; cbn [digits].
- intros [= <-]; exists []; split; [constructor|simpl; ring].
- destruct (d c) as [x|] eqn:Hc; [|discriminate].
  intros H; destruct (IH _ H) as [ds [H1 H2]].
  exists (x :: ds); split; [constructor; auto|].
  cbn [value List.length].
  rewrite <- (Forall2_length H1), H2, Nat2Z.inj_succ, Z.pow_succ_r by lia.
  ring.
Qed.

Lemma decvP cs v : decv cs = Some v -> dec_text cs v.
Proof.
unfold decv; destruct cs as [|c cs']; [discriminate|].
intros H; apply digitsP in H as [ds [H1 H2]].
split; [discriminate|]; exists ds; split.
- eapply Forall2_impl; [|exact H1]; intros ? ? ?; apply decdP; assumption.
- rewrite H2; ring.
Qed.

Lemma hexvP cs v : hexv cs = Some v -> hex_text cs v.
Proof.
unfold hexv; destruct cs as [|c cs']; [discriminate|].
intros H; apply digitsP in H as [ds [H1 H2]].
split; [discriminate|]; exists ds; split.
- eapply Forall2_impl; [|exact H1]; intros ? ? ?; apply hexdP; assumption.
- rewrite H2; ring.
Qed.

Lemma wordvP cs w : wordv cs = Some w -> word_text cs w.
Proof.
unfold wordv; destruct cs as [|c0 [|cx cs']]; try discriminate.
destruct (c0 =? c_0)%uint63 eqn:E0; [|discriminate].
destruct (cx =? c_x)%uint63 eqn:Ex; [|discriminate].
apply eqb_spec in E0, Ex; subst; intros H.
exists cs'; split; [reflexivity|apply hexvP; exact H].
Qed.

Lemma wordsvP fs ws : wordsv fs = Some ws -> Forall2 word_text fs ws.
Proof.
revert ws; induction fs as [|f fs IH]; intros ws; simpl.
- intros [= <-]; constructor.
- destruct (wordv f) as [w|] eqn:Hf; [|discriminate].
  destruct (wordsv fs) as [ws'|] eqn:Hfs; [|discriminate].
  intros [= <-]; constructor; [apply wordvP|apply IH]; auto.
Qed.

Lemma split_pP cs a b : split_p cs = (a, b) -> b <> [] ->
  cs = a ++ c_p :: b.
Proof.
revert a; induction cs as [|c cs IH]; intros a; simpl.
- intros [= <- <-]; contradiction.
- destruct (c =? c_p)%uint63 eqn:Ec.
  + apply eqb_spec in Ec; subst; intros [= <- <-]; reflexivity.
  + destruct (split_p cs) as [a' b'] eqn:Hs.
    intros [= <- <-] Hb; simpl; f_equal; apply IH; auto.
Qed.

Lemma x0vP cs M0 : x0v cs = Some M0 ->
  exists F f X,
  cs = [c_0; c_x; c_1; c_dot] ++ F ++ [c_p; c_plus] ++ X /\
  hex_text F f /\ (length F <= frac_digits)%nat /\
  M0 = 16 ^ Z.of_nat frac_digits +
       f * 16 ^ (Z.of_nat frac_digits - Z.of_nat (length F)) /\
  dec_text X xbin.
Proof.
unfold x0v; destruct cs as [|c0 [|cx [|c1 [|cd cs']]]]; try discriminate.
destruct (c0 =? c_0)%uint63 eqn:E0; [|discriminate].
destruct (cx =? c_x)%uint63 eqn:Ex; [|discriminate].
destruct (c1 =? c_1)%uint63 eqn:E1; [|discriminate].
destruct (cd =? c_dot)%uint63 eqn:Ed; [|discriminate]; cbn [andb].
apply eqb_spec in E0, Ex, E1, Ed; subst.
destruct (split_p cs') as [fr ex] eqn:Hs.
destruct fr as [|c fr']; [discriminate|].
destruct ex as [|cplus ce]; [discriminate|].
destruct (cplus =? c_plus)%uint63 eqn:Ep; [|discriminate].
destruct (Nat.leb_spec (length (c :: fr')) 13) as [Hl|]; [|discriminate].
cbn [andb].
destruct (digits hexd 16 1 (c :: fr')) as [f1|] eqn:Hd; [|discriminate].
destruct (decv ce) as [e|] eqn:He; [|discriminate].
destruct (Z.eqb_spec e xbin) as [->|]; [|discriminate].
intros [= <-].
apply eqb_spec in Ep; subst.
apply split_pP in Hs; [|discriminate].
apply digitsP in Hd as [ds [H1 H2]].
exists (c :: fr'), (value 16 ds), ce; split; [|split; [|split; [|split]]].
- rewrite Hs; reflexivity.
- split; [discriminate|]; exists ds; split; [|reflexivity].
  eapply Forall2_impl; [|exact H1]; intros ? ? ?; apply hexdP; assumption.
- exact Hl.
- change (f1 * 16 ^ Z.of_nat (13 - length (c :: fr')) =
          16 ^ Z.of_nat frac_digits + value 16 ds *
          16 ^ (Z.of_nat frac_digits - Z.of_nat (length (c :: fr')))).
  rewrite H2, Nat2Z.inj_sub by exact Hl; unfold frac_digits.
  set (L := Z.of_nat (length (c :: fr'))).
  assert (HL : 0 <= L <= 13) by (unfold L; lia).
  replace (16 ^ Z.of_nat 13) with (16 ^ L * 16 ^ (13 - L))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  change (Z.of_nat 13) with 13; ring.
- apply decvP; exact He.
Qed.

Lemma fields_nil cur cs : fields cur cs <> [].
Proof.
revert cur; induction cs as [|c cs IH]; intros cur; simpl; [discriminate|].
destruct (c =? c_space)%uint63; [discriminate|apply IH].
Qed.

Lemma fieldsP cur cs f fs : fields cur cs = f :: fs ->
  rev cur ++ cs = f ++ concat (map (fun W => c_space :: W) fs).
Proof.
revert cur f fs; induction cs as [|c cs IH]; intros cur f fs; simpl.
- intros [= <- <-]; simpl; rewrite !app_nil_r; reflexivity.
- destruct (c =? c_space)%uint63 eqn:Ec.
  + apply eqb_spec in Ec; subst; intros [= <- <-].
    destruct (fields [] cs) as [|g gs] eqn:Hg; [now apply fields_nil in Hg|].
    apply IH in Hg; simpl in Hg; rewrite Hg; reflexivity.
  + intros H; apply IH in H; rewrite <- H; simpl.
    rewrite <- app_assoc; reflexivity.
Qed.

Lemma sumZ_ext f g N : (forall j, f j = g j) -> sumZ f N = sumZ g N.
Proof. intros H; induction N; simpl; [reflexivity|rewrite IHN, H; ring]. Qed.

Lemma sumZ_shift f N : sumZ f (S N) = f O + sumZ (fun j => f (S j)) N.
Proof.
induction N; [simpl; ring|].
change (sumZ f (S (S N))) with (sumZ f (S N) + f (S N)).
rewrite IHN; simpl; ring.
Qed.

Lemma sumZ_scale c f N :
  sumZ (fun j => c * f j) N = c * sumZ f N.
Proof. induction N; simpl; [ring|rewrite IHN; ring]. Qed.

Lemma wsum_firstn n ws : wsum (firstn n ws) =
  sumZ (fun j => nth j ws 0 * beta ^ Z.of_nat j) n.
Proof.
revert ws; induction n as [|n IH]; intros ws; [reflexivity|].
rewrite sumZ_shift; destruct ws as [|w ws].
- rewrite (sumZ_ext _ (fun j => 0 * beta ^ Z.of_nat (S j)))
    by (intros [|j]; reflexivity).
  rewrite sumZ_scale; unfold wsum; cbn [firstn nth fold_right]; ring.
- change (wsum (firstn (S n) (w :: ws))) with
    (w + beta * wsum (firstn n ws)).
  rewrite IH.
  rewrite (sumZ_ext (fun j => nth (S j) (w :: ws) 0 * beta ^ Z.of_nat (S j))
             (fun j => beta * (nth j ws 0 * beta ^ Z.of_nat j))).
  + rewrite (sumZ_scale beta (fun j => nth j ws 0 * beta ^ Z.of_nat j)).
    cbn [nth]; change (Z.of_nat 0) with 0; ring.
  + intros j; cbn [nth]; rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring.
Qed.

Lemma groupP c ws : group c ws =
  map (fun i => sumZ (fun j => nth (i * Z.to_nat l + j) ws 0 *
                               beta ^ Z.of_nat j) (Z.to_nat l))
      (seq 0 c).
Proof.
revert ws; induction c as [|c IH]; intros ws; [reflexivity|].
change (group (S c) ws) with
  (wsum (firstn (Z.to_nat l) ws) :: group c (skipn (Z.to_nat l) ws)).
rewrite IH, wsum_firstn; cbn [seq map]; rewrite <- seq_shift, map_map.
f_equal; apply map_ext; intros i; apply sumZ_ext; intros j.
rewrite nth_skipn; f_equal; f_equal; lia.
Qed.

(** ** The theorem *)

(** Whatever [parse] returns is what the line says. *)
Theorem parse_sound s M0 n B :
  parse s = Some (M0, n, B) -> line_text (to_list s) M0 n B.
Proof.
unfold parse.
destruct (fields [] (to_list s)) as [|fx [|fn fw]] eqn:Hf; try discriminate.
destruct (Nat.eqb_spec (length fw) (k * Z.to_nat l)) as [Hl|];
  [|discriminate].
destruct (x0v fx) as [M|] eqn:Hx; [|discriminate].
destruct (decv fn) as [n'|] eqn:Hn; [|discriminate].
destruct (wordsv fw) as [ws|] eqn:Hw; [|discriminate].
intros [= <- <- <-].
apply fieldsP in Hf; simpl in Hf.
apply x0vP in Hx as (F & f & X & -> & HF & HL & HM & HX).
exists F, f, X, fn, fw, ws.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]];
  auto.
- rewrite Hf; simpl; rewrite <- !app_assoc; reflexivity.
- apply decvP; exact Hn.
- apply wordsvP; exact Hw.
- exact (groupP k ws).
Qed.

(** ** A short example *)

(** Eight words [0x0]. *)
Definition zeros8 : string := " 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0"%pstring.

(** [x0 = 0x1.8p+9 = 3 2^51 u], [n = 3], words [1, 2, 0, ..., 0]. *)
Definition example_line : string :=
  cat "0x1.8p+9 3 0x1 0x2 0x0 0x0 0x0 0x0 0x0 0x0"%pstring
  (cat zeros8 (cat zeros8 (cat zeros8 zeros8))).

Example parse_example : parse example_line =
  Some (3 * 2 ^ 51, 3, [1 + 2 * beta; 0; 0; 0; 0; 0; 0; 0]).
Proof. vm_compute; reflexivity. Qed.
