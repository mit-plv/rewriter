Require Import Coq.ZArith.BinInt.
Require Import Rewriter.Util.Notations.

Infix ">>" := Z.shiftr : Z_scope.
Infix "<<" := Z.shiftl : Z_scope.
Infix "&'" := Z.land : Z_scope.
