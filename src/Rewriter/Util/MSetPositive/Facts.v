From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import List.
From Coq Require Import SetoidList.
From Coq Require Import MSetPositive.
From Coq Require Import MSetFacts.
Require Import Rewriter.Util.Tactics.BreakMatch.
Require Import Rewriter.Util.Tactics.SplitInContext.
Require Import Rewriter.Util.Tactics.SpecializeBy.
Require Import Rewriter.Util.Tactics.DestructHead.
Require Import Rewriter.Util.ListUtil.SetoidList.
Require Import Rewriter.Util.Logic.ExistsEqAnd.

Local Set Implicit Arguments.

Set Implicit Arguments.
Unset Strict Implicit.

Module PositiveSetFacts.
  Module F := Facts PositiveSet.
  Include F.
  Import PositiveSet.

  Global Instance elements_Proper_Equal
    : Proper (Equal ==> Logic.eq) elements | 10.
  Proof.
    intros p1 p2 Hp.
    apply eqlistA_eq_iff.
    eapply SortA_equivlistA_eqlistA; try apply elements_spec2; try exact _.
    cbv [equivlistA]; intro.
    rewrite !elements_spec1.
    apply Hp.
  Qed.

  Lemma In_elements_mem_iff {x p}
    : List.In x (elements p) <-> PositiveSet.mem x p = true.
  Proof using Type.
    rewrite elements_b, existsb_exists; cbv [eqb].
    repeat first [ apply conj
                 | progress intros
                 | progress destruct_head'_ex
                 | progress destruct_head'_and
                 | eexists
                 | eassumption
                 | break_innermost_match_step
                 | break_innermost_match_hyps_step
                 | congruence ].
  Qed.
End PositiveSetFacts.
