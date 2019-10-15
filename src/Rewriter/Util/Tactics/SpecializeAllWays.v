Require Export Rewriter.Util.FixCoqMistakes.
Require Export Rewriter.Util.Tactics.UniquePose.

Ltac specialize_all_ways :=
  repeat match goal with
         | [ H : ?A, H' : forall a : ?A, _ |- _ ]
           => unique pose proof (H' H)
         end.
