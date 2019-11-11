(** * Examples of Using the Rewriter *)
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Require Import Rewriter.Util.LetIn.
Require Import Rewriter.Util.Notations.
Require Import Rewriter.Util.NatUtil.
Require Import Rewriter.Util.ListUtil.
Require Import Rewriter.Language.Pre.
Require Import Rewriter.Util.plugins.RewriterBuild.
Import ListNotations.
Local Open Scope list_scope.

Definition prefixSums (ls : list nat) : list nat :=
  let ls' := combine ls (seq 0 (length ls)) in
  let ls'' := map (fun p => fst p * snd p) ls' in
  let '(_, ls''') := fold_left (fun acc_ls''' n =>
                                  let '(acc, ls''') := acc_ls''' in
                                  let acc' := acc + n in
                                  (acc', acc' :: ls''')) ls'' (0, []) in
  ls'''.

Lemma zero_plus : forall n, 0 + n = n.
Proof. trivial. Qed.
Lemma plus_zero : forall n, n + 0 = n.
Proof. intros; lia. Qed.
Lemma times_zero : forall n, n * 0 = 0.
Proof. intros; lia. Qed.
Lemma times_one : forall n, n * 1 = n.
Proof. intros; lia. Qed.

Lemma eval_map : forall A B (f : A -> B) (l : list A),
    map f l = ident.eagerly list_rect _ _ []
                            (fun x _ l' => f x :: l') l.
Proof. cbv [ident.eagerly]; induction l; simpl; f_equal. Qed.

Lemma eval_fold_left : forall A B (f : A -> B -> A)
                              (l : list B) (a : A),
    fold_left f l a = ident.eagerly list_rect _ _ (fun a => a)
                                    (fun x _ r a => r (f a x)) l a.
Proof. cbv [ident.eagerly]; induction l; simpl; intros; f_equal; auto. Qed.

Lemma eval_combine : forall A B (la : list A) (lb : list B),
    combine la lb = list_rect _ (fun _ => [])
                              (fun x _ r lb => list_case (fun _ => _) [] (fun y ys => (x, y) :: r ys) lb) la lb.
Proof. cbv [ident.eagerly]; induction la, lb; simpl; intros; f_equal; auto. Qed.

Lemma eval_length : forall A (ls : list A),
    length ls
    = list_rect _ 0 (fun _ _ n => S n) ls.
Proof. induction ls; cbv; f_equal; reflexivity. Qed.

Global Instance: forall A B,
    Proper ((eq ==> eq ==> eq) ==> eq ==> eq ==> eq)
           (@fold_left A B).
Proof.
  cbv -[fold_left]; intros A B f g Hfg ls ls' ?; subst ls'.
  induction ls; simpl; eauto.
Qed.

Make rewriter := Rewriter For (zero_plus, plus_zero,
                               times_zero, times_one, eval_map,
                               eval_fold_left, do_again eval_length,
                               do_again eval_combine, eval_rect nat, eval_rect list, eval_rect prod)
                          (with delta)
                          (with extra idents (seq)).

Make rewriter2 := Rewriter For (eval_rect prod, eval_rect list).

Lemma prefixSums4 :
  {f : nat -> nat -> nat -> nat -> list nat
  | forall a b c d, f a b c d
                    = prefixSums [a; b; c; d]}.
Proof. eexists; intros; Rewrite_rhs_for rewriter.
       reflexivity. Qed.
