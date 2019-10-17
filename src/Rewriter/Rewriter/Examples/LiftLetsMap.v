(** * Examples of Using the Rewriter *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Require Import Rewriter.Util.LetIn.
Require Import Rewriter.Util.Notations.
Require Import Rewriter.Util.NatUtil.
Require Import Rewriter.Util.ListUtil.
Require Import Rewriter.Language.Pre.
Require Import Rewriter.Util.plugins.RewriterBuild.
Require Export Rewriter.Rewriter.Examples.PerfTesting.Settings.
Require Import Rewriter.Util.Tactics.AssertSucceedsPreserveError.
Import ListNotations.
Local Open Scope list_scope. Local Open Scope Z_scope.

Lemma eval_repeat
  : forall A x n,
    @List.repeat A x ('n)
    = ident.eagerly (@nat_rect) _ nil (fun k repeat_k => x :: repeat_k) ('n).
Proof. induction n; cbn; f_equal; eauto. Qed.

Lemma eval_list_rect
  : forall A P N C ls,
    @Thunked.list_rect A P N C ls
    = ident.eagerly (@Thunked.list_rect) A P N C ls.
Proof. reflexivity. Qed.

Lemma eval_nat_rect
  : forall P O_case S_case n,
    @Thunked.nat_rect P O_case S_case ('n)
    = (ident.eagerly (@Thunked.nat_rect) _)
        O_case
        S_case
        ('n).
Proof. reflexivity. Qed.

Time Make myrew := Rewriter For (eval_repeat, eval_list_rect, eval_nat_rect) (with extra idents (Z.add)).

Definition map_double (ls : list Z) :=
  list_rect
    _
    nil
    (fun x xs rec
     => dlet y := x + x in
         y :: rec)
    ls.


Definition make (n : nat) (m : nat) (v : Z)
  := nat_rect
       _
       (List.repeat v n)
       (fun _ rec => map_double rec)
       m.

Lemma lift_let_list_rect T A P N C (v : A) fls
  : @list_rect T P N C (Let_In v fls) = Let_In v (fun v => @list_rect T P N C (fls v)).
Proof. reflexivity. Qed.
Hint Rewrite lift_let_list_rect : mydb2.
Lemma lift_let_cons T A x (v : A) f : @cons T x (Let_In v f) = Let_In v (fun v => @cons T x (f v)).
Proof. reflexivity. Qed.
Hint Rewrite lift_let_cons : mydb1.

Notation goal n m := (forall v, make n m v = nil) (only parsing).
Ltac start _ := cbv [make map_double]; intros.
Ltac verify_form term :=
  lazymatch term with
  | (dlet x := ?v + ?v in ?rest)
    => is_var v;
       let x' := fresh in
       let __ := constr:(fun x' : Z
                         => ltac:(let rest' := constr:(match x' return _ with x => rest end) in
                                  verify_form rest';
                                  exact I)) in
       idtac
  | cons ?v ?rest => is_var v; verify_form rest
  | nil => idtac
  end.
Ltac verify _ :=
  lazymatch goal with
  | [ |- ?lhs = nil ]
    => verify_form lhs
  end.

Ltac timetest0 do_verify :=
  assert_succeeds_preserve_error (once (time "Rewrite_lhs_for" Rewrite_lhs_for myrew); do_verify ()).
Ltac timetest1 do_verify :=
  assert_succeeds_preserve_error
    (once
       (time
          "rewrite_strat(topdown,bottomup)"
          ((cbv [nat_rect List.repeat]);
           repeat (cbn [list_rect];
                   (rewrite_strat ((try repeat topdown hints mydb1); (try repeat bottomup hints mydb2)))))); do_verify ()).
Ltac timetest2 do_verify :=
  assert_succeeds_preserve_error
    (once
       (time
          "rewrite_strat(bottomup,bottomup)"
          ((cbv [nat_rect List.repeat]);
           repeat (cbn [list_rect];
                   (rewrite_strat ((try repeat bottomup hints mydb1); (try repeat bottomup hints mydb2)))))); do_verify ()).

Global Open Scope nat_scope.
Ltac test_for_gen do_verify test_tac n m :=
  idtac "Params: n=" n ",m=" m;
  assert_succeeds_preserve_error (once (assert (goal n m); [ start (); test_tac do_verify | ])).
Ltac test_for test_tac n m := test_for_gen ltac:(fun _ => idtac) test_tac n m.
Ltac test_for_safe test_tac n m := test_for_gen verify test_tac n m.
(*
Opaque Let_In.
Hint Constants Opaque : rewrite.



Goal let n := 5%nat in
     let m := 5%nat in
     forall v, make n m v = nil.
Proof.
  cbv [make map_double]; intro.
  Set Printing Width 150.
  time "Rewrite_for" assert_succeeds (Rewrite_for myrew).
  time "rewrite_strat" assert_succeeds ((rewrite_strat (eval cbv [nat_rect List.repeat]));
                                        repeat (cbn [list_rect];
                                                (rewrite_strat ((try repeat topdown hints mydb1); (try repeat bottomup hints mydb2))))).
  time "repeat_setoid_rewrite" assert_succeeds (cbv [nat_rect List.repeat]; repeat (cbn [list_rect]; repeat setoid_rewrite lift_let_cons; repeat setoid_rewrite lift_let_list_rect)).
*)
