(* =========================================================================  *)
(*  FoldChecksRun.v -- The twelve checks, run at the emitted tables.         *)
(*                                                                           *)
(*  One file each, so the wall time is the largest check and not their sum;  *)
(*  ./mkfoldrun.sh writes them.  Exported, so what requires this file sees   *)
(*  the twelve lemmas exactly as it did when they lived here.                *)
(* =========================================================================  *)

Require Export FoldRun_00 FoldRun_01 FoldRun_02 FoldRun_03 FoldRun_04
               FoldRun_05 FoldRun_06 FoldRun_07 FoldRun_08 FoldRun_09
               FoldRun_10 FoldRun_11.
