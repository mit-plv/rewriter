Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.

Ltac2 rec iterate f n x :=
  if Int.le n 0 then x else iterate f (Int.sub n 1) (f x).
