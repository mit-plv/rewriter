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

Time Make myrew := Rewriter For (eval_repeat, eval_rect list, eval_rect nat) (with extra idents (Z.add)).

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

Module Type AxT.
  Axiom Let_InAx : forall {A P} (x : A) (f : forall a : A, P a), P x.
  Axiom ZAddAx : Z -> Z -> Z.
End AxT.
Module Import Ax : AxT.
  Definition Let_InAx : forall {A P} (x : A) (f : forall a : A, P a), P x
    := @Let_In.
  Definition ZAddAx : Z -> Z -> Z
    := Z.add.
End Ax.

Definition map_double_cps {T} (ls : list Z) (k : list Z -> T) :=
  list_rect
    (fun _ => (list Z -> T) -> _)
    (fun k => k nil)
    (fun x xs rec k
     => Let_InAx (ZAddAx x x)
                 (fun y =>
                    rec (fun ys => k (y :: ys))))
    ls
    k.

Definition make_cps {T} (n : nat) (m : nat) (v : Z) (k : list Z -> T)
  := nat_rect
       _
       (fun k => k (List.repeat v n))
       (fun _ rec k => rec (fun ls => map_double_cps ls k))
       m
       k.

Lemma lift_let_list_rect T A P N C (v : A) fls
  : @list_rect T P N C (Let_In v fls) = Let_In v (fun v => @list_rect T P N C (fls v)).
Proof. reflexivity. Qed.
Hint Rewrite lift_let_list_rect : mydb2.
Lemma lift_let_cons T A x (v : A) f : @cons T x (Let_In v f) = Let_In v (fun v => @cons T x (f v)).
Proof. reflexivity. Qed.
Hint Rewrite lift_let_cons : mydb1.

Notation goal n m := (forall v, make n m v = nil) (only parsing).
Notation goal_cps n m := (forall v, make_cps n m v (fun x => x) = nil) (only parsing).
Ltac start _ := cbv [make map_double make_cps map_double_cps]; intros.
Ltac verify_form term :=
  lazymatch term with
  | ?Let_In_f (?Add ?v ?v) (fun x => ?rest)
    => is_var v;
       lazymatch Let_In_f with
       | @Let_In _ _ => idtac
       | @Let_InAx _ _ => idtac
       | _ => fail 0 "invalid let_in" Let_In_f
       end;
       lazymatch Add with
       | Z.add => idtac
       | ZAddAx => idtac
       | _ => fail 0 "invalid add" Add
       end;
       let x' := fresh in
       let __ := constr:(fun x' : Z
                         => ltac:(let rest' := constr:(match x' return _ with x => rest end) in
                                  verify_form rest';
                                  exact I)) in
       idtac
  | cons ?v ?rest => is_var v; verify_form rest
  | nil => idtac
  | _ => fail 0 "invalid:" term
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
Ltac timetest3 do_verify :=
  assert_succeeds_preserve_error
    (once (time "cps+vm_compute" vm_compute); do_verify ()).

Global Open Scope nat_scope.
Ltac test_for_gen do_verify test_tac test_tac_n n m :=
  idtac "Params: n=" n ",m=" m;
  let goalT := lazymatch test_tac_n with
               | 3 => constr:(goal_cps n m)
               | _ => constr:(goal n m)
               end in
  assert_succeeds_preserve_error (once (assert goalT; [ start (); test_tac do_verify | ])).
Ltac test_for test_tac test_tac_n n m := test_for_gen ltac:(fun _ => idtac) test_tac test_tac_n n m.
Ltac test_for_safe test_tac test_tac_n n m := test_for_gen verify test_tac test_tac_n n m.

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
