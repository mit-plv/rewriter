Require Export Rewriter.Language.Pre.
Require Export Rewriter.Language.IdentifiersBasicGenerate.
Require Export Rewriter.Rewriter.ProofsCommon.
Require Export Rewriter.Rewriter.AllTactics.
Require Import Rewriter.Util.plugins.StrategyTactic.
Export IdentifiersBasicGenerate.Compilers.
Export ProofsCommon.Compilers.
Export AllTactics.Compilers.

Ltac Pre.set_strategy_expand name ::= strategy -1000 [name].
