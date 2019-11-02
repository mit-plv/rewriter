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

Definition make_lets_def (n : nat) (v : Z) (acc : Z) :=
  @nat_rect_arrow_nodep
    (Z * Z) Z
    (fun '(v, acc) => acc + acc + v)
    (fun _ rec '(v, acc) => dlet acc := acc + acc + v in rec (v, acc))
    n
    (v, acc).

Lemma eval_nat_rect_arrow_nodep
  : forall A B O_case S_case n v,
    @nat_rect_arrow_nodep A B O_case S_case ('n) v
    = ident.eagerly (@nat_rect_arrow_nodep) _ _ O_case S_case ('n) v.
Proof. reflexivity. Qed.

Lemma eval_prod_rect
  : forall A B P f x y, @prod_rect_nodep A B P f (x, y) = f x y.
Proof. reflexivity. Qed.

Time Make myrew := Rewriter For (Z.add_0_r, eval_nat_rect_arrow_nodep, eval_prod_rect).

Notation goal n := (forall acc, make_lets_def n 0 acc = acc) (only parsing).
Ltac start _ := cbv [make_lets_def]; intros.
Ltac verify_form start term :=
  lazymatch term with
  | (dlet x := start + start in ?rest)
    => let x' := fresh in
       let __ := constr:(fun x' : Z
                         => ltac:(let rest' := constr:(match x' return _ with x => rest end) in
                                  verify_form x' rest';
                                  exact I)) in
       idtac
  | start + start => idtac
  end.
Ltac verify _ :=
  lazymatch goal with
  | [ |- ?lhs = ?acc ]
    => is_var acc; verify_form acc lhs
  end.
Ltac timetest0 do_verify :=
  assert_succeeds_preserve_error (once (time "Rewrite_lhs_for" Rewrite_lhs_for myrew); do_verify ()).
Ltac timetest1 do_verify :=
  assert_succeeds_preserve_error (once (time "cbv;setoid_rewrite" (cbv [nat_rect_arrow_nodep nat_rect_nodep]; repeat setoid_rewrite Z.add_0_r)); do_verify ()).
Ltac timetest2 do_verify :=
  assert_succeeds_preserve_error (once (time "cbv;rewrite_strat(topdown)" ((cbv [nat_rect_arrow_nodep nat_rect_nodep]); rewrite_strat topdown Z.add_0_r)); do_verify ()).
Ltac timetest3 do_verify :=
  assert_succeeds_preserve_error (once (time "cbv;rewrite_strat(bottomup)" ((cbv [nat_rect_arrow_nodep nat_rect_nodep]); rewrite_strat bottomup Z.add_0_r)); do_verify ()).

Global Open Scope nat_scope.
Ltac test_from_to_gen do_verify test_tac min max step :=
  idtac;
  let min := (eval vm_compute in min) in
  idtac "Params: n=" min;
  assert_succeeds_preserve_error (once (assert (goal min); [ start (); test_tac do_verify | ]));
  let finished := (eval vm_compute in (max <? (min + step))%nat) in
  lazymatch finished with
  | true => idtac
  | false => test_from_to_gen do_verify test_tac (min + step)%nat max step
  end.
Ltac test_from_to test_tac min max step := test_from_to_gen ltac:(fun _ => idtac) test_tac min max step.
Ltac test_from_to_safe test_tac min max step := test_from_to_gen verify test_tac min max step.

(*
Opaque Let_In.

Ltac rewrite_perf_level ::= constr:(5%nat).

Goal let n := 200%nat in
     forall acc, make_lets_def n 0 acc = make_lets_def n 0 acc.
Proof.
  cbv [make_lets_def].
  intros.
  Set Printing Width 150.
  time "Rewrite_for" assert_succeeds (Rewrite_for myrew).
  time "cbv;setoid_rewrite" assert_succeeds (cbv [nat_rect_arrow_nodep nat_rect_nodep]; setoid_rewrite Z.add_0_r).
  time "cbv;rewrite_strat(topdown)" assert_succeeds ((rewrite_strat eval cbv [nat_rect_arrow_nodep nat_rect_nodep]); rewrite_strat topdown Z.add_0_r).
  time "cbv;rewrite_strat(bottomup)" assert_succeeds ((rewrite_strat eval cbv [nat_rect_arrow_nodep nat_rect_nodep]); rewrite_strat bottomup Z.add_0_r).
  Fail time "rewrite_strat(cbv;topdown)" (*assert_succeeds*) ((rewrite_strat (eval cbv [nat_rect_arrow_nodep nat_rect_nodep]; topdown Z.add_0_r))).
  Fail time "rewrite_strat(cbv;bottomup)" (*assert_succeeds*) ((rewrite_strat (eval cbv [nat_rect_arrow_nodep nat_rect_nodep]; bottomup Z.add_0_r))).
  Time Rewrite_for myrew.
  Show.
Abort.
*)
