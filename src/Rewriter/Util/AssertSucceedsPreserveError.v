Require Import Rewriter.Util.FixCoqMistakes.

Ltac assert_succeeds_preserve_error tac :=
  tryif (assert_fails tac) then once tac else idtac.
Tactic Notation "assert_succeeds_preserve_error" tactic3(tac) :=
    assert_succeeds_preserve_error tac.
