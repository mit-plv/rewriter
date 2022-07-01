Require Import Rewriter.Language.Pre.
Require Import Rewriter.Util.LetIn.
Require Import Rewriter.Util.plugins.RewriterBuild.

Ltac rewrite_perf_level ::= constr:(5%nat).
#[global] Hint Opaque Let_In : rewrite typeclass_instances.
#[global] Hint Constants Opaque : rewrite.
Global Opaque Let_In.
Global Set Printing Width 150.
Global Set NativeCompute Timing.
