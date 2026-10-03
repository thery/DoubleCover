Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common.
Lemma row_split sh m (rows : list (list val)) i p :
  0 <= i < m -> Zlength rows = m ->
  data_at sh (tarray (tarray tulong 6) m) rows p =
  (data_at sh (tarray (tarray tulong 6) i) (sublist 0 i rows) p *
   data_at sh (tarray tulong 6) (Znth i rows)
     (field_address0 (tarray (tarray tulong 6) m) [ArraySubsc i] p) *
   data_at sh (tarray (tarray tulong 6) (m - (i + 1))) (sublist (i + 1) m rows)
     (field_address0 (tarray (tarray tulong 6) m) [ArraySubsc (i + 1)] p))%logic.
Proof.
  intros Hi Hl.
  rewrite (split3_data_at_Tarray sh (tarray tulong 6) m i (i + 1) rows rows
             (sublist 0 i rows) (sublist i (i + 1) rows) (sublist (i + 1) m rows))
    ; try reflexivity; try lia; try (rewrite sublist_same; auto; lia).
  2: (simpl; tauto). 2: (split; [lia| exact (Z.eq_le_incl _ _ (eq_sym Hl))]).
  rewrite sublist_len_1 by lia.
  replace (i + 1 - i) with 1 by lia.
  rewrite (data_at_singleton_array_eq sh (tarray tulong 6) (Znth i rows)) by reflexivity.
  reflexivity.
Qed.

Lemma row_addr m i p : 0 <= i < m ->
  field_compatible (tarray (tarray tulong 6) m) [] p ->
  field_address0 (tarray (tarray tulong 6) m) [ArraySubsc i] p =
  offset_val (48 * i) p.
Proof.
  intros Hi Hc.
  rewrite field_address0_offset.
  - simpl. f_equal; lia.
  - auto with field_compatible.
Qed.
