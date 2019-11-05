(** * Examples of Using the Rewriter *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.ZArith.ZArith.
Require Import Rewriter.Util.LetIn.
Require Import Rewriter.Util.Notations.
Require Import Rewriter.Util.NatUtil.
Require Import Rewriter.Util.Prod.
Require Import Rewriter.Language.Pre.
Require Import Rewriter.Util.plugins.RewriterBuild.
Require Export Rewriter.Rewriter.Examples.PerfTesting.Settings.
Require Import Rewriter.Util.Tactics.AssertSucceedsPreserveError.
Local Open Scope Z_scope.

Time Make myrew := Rewriter For (Z.add_0_r, eval_rect nat, eval_rect prod).

Definition iter_plus_acc (m : nat) (acc v : Z) :=
  @nat_rect
    (fun _ => Z -> Z)
    (fun acc => acc)
    (fun _ rec acc => rec (acc + v))
    m
    acc.

Definition make_tree (n : nat) (m : nat) (v : Z) (acc : Z) :=
  Eval cbv [iter_plus_acc] in
    @nat_rect
      (fun _ => Z * Z -> Z)
      (fun '(v, acc) => iter_plus_acc m (acc + acc) v)
      (fun _ rec '(v, acc) => iter_plus_acc m (rec (v, acc) + rec (v, acc)) v)
      n
      (v, acc).

Notation goal n m := (forall acc, make_tree n m 0 acc = acc) (only parsing).
Ltac start _ := cbv [make_tree]; intros.
Ltac verify_form term :=
  lazymatch term with
  | ?x + ?x => verify_form x
  | _ => is_var term
  end.
Ltac verify _ :=
  lazymatch goal with
  | [ |- ?lhs = ?acc ]
    => is_var acc; verify_form lhs
  end.
Ltac timetest0 do_verify :=
  assert_succeeds_preserve_error (once (time "Rewrite_lhs_for" Rewrite_lhs_for myrew); do_verify ()).
Ltac timetest1 do_verify :=
  assert_succeeds_preserve_error (once (time "cbv;rewrite!" (cbv [nat_rect]; rewrite !Z.add_0_r)); do_verify ()).
Ltac timetest2 do_verify :=
  assert_succeeds_preserve_error (once (time "cbv;setoid_rewrite" (cbv [nat_rect]; repeat setoid_rewrite Z.add_0_r)); do_verify ()).
Ltac timetest3 do_verify :=
  assert_succeeds_preserve_error (once (time "cbv;rewrite_strat(topdown)" ((cbv [nat_rect]); rewrite_strat topdown Z.add_0_r)); do_verify ()).
Ltac timetest4 do_verify :=
  assert_succeeds_preserve_error (once (time "cbv;rewrite_strat(bottomup)" ((cbv [nat_rect]); rewrite_strat bottomup Z.add_0_r)); do_verify ()).

Global Open Scope nat_scope.
Ltac test_for_gen do_verify test_tac n m :=
  idtac "Params: n=" n ",m=" m;
  assert_succeeds_preserve_error (once (assert (goal n m); [ start (); test_tac do_verify | ])).
Ltac test_for test_tac n m := test_for_gen ltac:(fun _ => idtac) test_tac n m.
Ltac test_for_safe test_tac n m := test_for_gen verify test_tac n m.

(*
Goal let n := 12%nat in
     let m := 2%nat in
     forall acc, make_tree n m 0 acc = acc.
Proof.
  cbv [make_tree].
  intros.
  Set Printing Width 150.
  time "Rewrite_for" assert_succeeds (Rewrite_lhs_for myrew).
  time "cbv;rewrite!" assert_succeeds (cbv [nat_rect]; rewrite !Z.add_0_r).
  time "cbv;setoid_rewrite" assert_succeeds (cbv [nat_rect]; repeat setoid_rewrite Z.add_0_r).
  time "cbv;rewrite_strat(topdown)" assert_succeeds ((rewrite_strat eval cbv [nat_rect]); rewrite_strat topdown Z.add_0_r).
  time "cbv;rewrite_strat(bottomup)" assert_succeeds ((rewrite_strat eval cbv [nat_rect]); rewrite_strat bottomup Z.add_0_r).
  Fail time "rewrite_strat(cbv;topdown)" (*assert_succeeds*) ((rewrite_strat (eval cbv [nat_rect]; topdown Z.add_0_r))).
  Fail time "rewrite_strat(cbv;bottomup)" (*assert_succeeds*) ((rewrite_strat (eval cbv [nat_rect]; bottomup Z.add_0_r))).
  Time Rewrite_for myrew.
  Show.
Abort.
*)
