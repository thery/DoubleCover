(* =========================================================================  *)
(*  RowFoldEmpty.v -- the map the folded run starts from.                     *)
(* =========================================================================  *)

(* Two facts about RowFold.mkempty, and the folded run needs both of them at  *)
(* its first level: it holds no member, and it is long enough that every kept *)
(* page's chunk is inside it.  The plain run needs only the first, because    *)
(* the plain level reaches a word through the chunking and not through a      *)
(* page array put back at the end.                                            *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball.
Require Import Row RowMap RowFold RowFoldOk.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Lemma length_makeA (sz : int) (v : arr) :
  PArray.length (PArray.make sz v) =
  (if (sz <=? PArray.max_length)%uint63 then sz else PArray.max_length).
Proof. exact: (@PArray.length_make arr sz v). Qed.

(* ---- it is forty four chunks long ---------------------------------------- *)

Lemma length_mkemptyf : PArray.length (mkempty tt) = nchunkf.
Proof.
rewrite /mkempty.
apply: (@ifold_ind _ (fun a => PArray.length a = nchunkf)).
  by move=> i b hb; rewrite RowMap.length_setA.
by rewrite length_makeA; vm_compute.
Qed.

(* every kept page's chunk is one of the forty four *)
Definition fchkC : bool := iter nrepn 0%uint63 (fun r => (pchk r <? nchunkf)).
Lemma fchkCP : fchkC. Proof. by vm_compute. Qed.

Lemma fchkCE : fchkC = iter nrepn 0%uint63 (fun r => (pchk r <? nchunkf)).
Proof. by []. Qed.

Lemma pchk_mkemptyf r :
  (to_nat r < nrepn)%N -> (pchk r <? PArray.length (mkempty tt)).
Proof.
move=> hr; rewrite length_mkemptyf.
have h1 := fchkCP; rewrite fchkCE in h1.
exact: (Row.iter_at h1 hr).
Qed.

(* ---- and it holds no member ---------------------------------------------- *)

Lemma fget_mkemptyf c :
  PArray.get (mkempty tt) c = PArray.make csizef 0%uint63 \/
  PArray.get (mkempty tt) c = PArray.make 1%uint63 0%uint63.
Proof.
have hset : forall (t : rmap) i (v : arr),
    PArray.get (PArray.set t i v) i = v \/
    PArray.get (PArray.set t i v) i = PArray.get t i.
  move=> t i v; have [hin|hin] := boolP (i <? PArray.length t)%uint63.
    by left; rewrite RowMap.get_setA.
  right; rewrite RowMap.get_oobA ?RowMap.default_setA;
    last by rewrite RowMap.length_setA; apply: negbTE.
  by rewrite (@RowMap.get_oobA _ _ (negbTE hin)).
rewrite /mkempty.
apply: (@ifold_ind _ (fun a => PArray.get a c = PArray.make csizef 0%uint63 \/
                               PArray.get a c = PArray.make 1%uint63 0%uint63));
    last by right; rewrite RowMap.get_makeA.
move=> i b hb.
have [hic|hic] := eqVneq i c; last first.
  by rewrite RowMap.get_set_otherA //; apply/eqP.
by rewrite -hic; case: (hset b i (PArray.make csizef 0%uint63)) => ->;
   [left | rewrite hic].
Qed.

Lemma ftest_mkemptyf fpg fsgr fsbt pg gr bt :
  ftest fpg fsgr fsbt (mkempty tt) pg gr bt = false.
Proof.
rewrite /ftest /fget.
by case: (fget_mkemptyf (pchk (fkpt (PArray.get fpg pg)))) => ->;
   rewrite get_makeE RowMap.land0n.
Qed.

Lemma soundatf_mkemptyf fpg fsgr fsbt (P : int -> int -> int -> Prop) :
  soundatf fpg fsgr fsbt P (mkempty tt).
Proof. by move=> pg gr bt _; rewrite ftest_mkemptyf. Qed.
