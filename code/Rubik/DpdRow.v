(* The constants the two coset theorems use, for ./dpdfiles.py.              *)
(* OUT OF _CoqProject: it needs coq-dpdgraph and the full .vo of both heads. *)
From dpdgraph Require dpdgraph.
Require Rubik.RowCubDone Rubik.RowFoldCubDone.
Set DependGraph File "unfold.dpd".
Print DependGraph Rubik.RowCubDone.real_superflip_row_cub_runO.
Set DependGraph File "fold.dpd".
Print DependGraph Rubik.RowFoldCubDone.real_superflip_row_fold_runO.
