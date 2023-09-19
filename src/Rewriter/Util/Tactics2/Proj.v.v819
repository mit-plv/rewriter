Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.
Import Constr.Unsafe.

Ltac2 equal (x : projection) (y : projection) : bool
  := let dummy := make (Rel (-1)) in
     Constr.equal (make (Proj x dummy)) (make (Proj y dummy)).
