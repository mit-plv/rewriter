(** * Examples of Using the Rewriter *)
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Rewriter.Util.LetIn.
Require Import Rewriter.Util.Notations.
Require Import Rewriter.Util.NatUtil.
Require Import Rewriter.Util.Bool.
Require Import Rewriter.Util.ListUtil.
Require Import Rewriter.Language.Pre.
Require Import Rewriter.Util.Bool.Reflect.
Require Import Rewriter.Util.plugins.RewriterBuild.
Require Export Rewriter.Rewriter.Examples.PerfTesting.Settings.
Require Import Rewriter.Util.Tactics.AssertSucceedsPreserveError.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope.

Lemma nat_rect_arrow_nodep_eagerly
  : forall A B O_case S_case n v,
    @nat_rect_arrow_nodep A B O_case S_case ('n) v
    = ident.eagerly (@nat_rect_arrow_nodep) _ _ O_case S_case ('n) v.
Proof. reflexivity. Qed.

Lemma eval_prod_rect
  : forall A B P f x y, @Prod.prod_rect_nodep A B P f (x, y) = f x y.
Proof. reflexivity. Qed.

Lemma eval_fold_right
  : forall A B f x ls,
    @List.fold_right A B f x ls
    = ident.eagerly (@list_rect) _ _ x (fun l ls fold_right_ls => f l fold_right_ls) ls.
Proof. induction ls; cbn; f_equal; auto. Qed.

Lemma eval_app
  : forall A xs ys,
    xs ++ ys
    = ident.eagerly (@list_rect) A _ ys (fun x xs app_xs_ys => x :: app_xs_ys) xs.
Proof. induction xs; cbn; intros; f_equal; auto. Qed.

Lemma eval_list_rect
  : forall A P N C ls,
    @Thunked.list_rect A P N C ls
    = ident.eagerly (@Thunked.list_rect) A P N C ls.
Proof. reflexivity. Qed.

Lemma eval_map
  : forall A B f ls,
    @List.map A B f ls
    = ident.eagerly (@list_rect) _ _ nil (fun l ls map_ls => cons (f l) map_ls) ls.
Proof. induction ls; cbn; f_equal; auto. Qed.

Lemma eval_bool_rect_true : forall T t f, @Thunked.bool_rect T t f true = t tt.
Proof. reflexivity. Qed.
Lemma eval_bool_rect_false : forall T t f, @Thunked.bool_rect T t f false = f tt.
Proof. reflexivity. Qed.

Lemma eval_rev
  : forall A xs,
    @List.rev A xs
    = (@list_rect _ (fun _ => _))
        (@nil _)
        (fun x xs rev_xs => rev_xs ++ [x])%list
        xs.
Proof. intros ? ls; induction ls; cbn; f_equal. Qed.

Scheme Equality for PositiveSet.tree.

Definition PositiveSet_t_beq : PositiveSet.t -> PositiveSet.t -> bool := tree_beq.

Global Instance PositiveSet_reflect_eqb : reflect_rel (@eq PositiveSet.t) PositiveSet_t_beq
  := reflect_of_brel Equality.PositiveSet.internal_tree_dec_bl Equality.PositiveSet.internal_tree_dec_lb.

Notation lemmas := (nat_rect_arrow_nodep_eagerly, eval_prod_rect, eval_fold_right, eval_map, do_again eval_rev, eval_bool_rect_true, eval_bool_rect_false, @Prod.fst_pair, eval_list_rect, eval_app) (only parsing).
Notation extra_idents := (Z.eqb, orb, Z.gtb, PositiveSet.elements, @fst, @snd, PositiveSet.mem, Pos.succ, PositiveSet.add, List.fold_right, List.map, List.seq, Pos.mul, S, Pos.of_nat, Z.to_nat, Z.div, Z.pos, O, PositiveSet.empty) (only parsing).

Time Make myrew := Rewriter For lemmas (with extra idents extra_idents) (with delta).

Definition sieve' (fuel : nat) (max : Z)
  := List.rev
       (fst
          (@nat_rect_arrow_nodep
             (list Z (* primes *) * PositiveSet.t (* composites *) * positive (* next_prime *)) (list Z (* primes *) * PositiveSet.t (* composites *))
             (fun '(primes, composites, next_prime) => (primes, composites))
             (fun _ rec '(primes, composites, next_prime)
              => rec
                   (if (PositiveSet.mem next_prime composites || (Z.pos next_prime >? max))%bool%Z
                    then (primes, composites, Pos.succ next_prime)
                    else (Z.pos next_prime :: primes,
                          List.fold_right
                            PositiveSet.add
                            composites
                            (List.map (fun n => Pos.mul (Pos.of_nat (S n)) next_prime)
                                      (List.seq 0 (Z.to_nat (max / Z.pos next_prime)))),
                          Pos.succ next_prime)))
             fuel
             (nil, PositiveSet.empty, 2%positive))).

Definition sieve (n : Z)
  := Eval cbv [sieve'] in sieve' (Z.to_nat n) n.

Global Arguments Pos.to_nat !_ / .

Notation goal n := (sieve n = nil) (only parsing).
Ltac start _ := cbv [sieve].
Ltac verify_form term :=
  lazymatch term with
  | nil => idtac
  | cons ?n ?rest
    => let n' := (eval vm_compute in n) in
       constr_eq n n';
       verify_form rest
  end.
Ltac verify _ :=
  lazymatch goal with
  | [ |- ?lhs = nil ]
    => verify_form lhs
  end.
Ltac timetest0 do_verify :=
  assert_succeeds_preserve_error (once (time "Rewrite_lhs_for" Rewrite_lhs_for myrew); do_verify ()).
Ltac timetest1 do_verify :=
  assert_succeeds_preserve_error (once (time "vm_compute" vm_compute); do_verify ()).
Ltac timetest2 do_verify :=
  assert_succeeds_preserve_error (once (time "lazy" lazy); do_verify ()).
Ltac timetest3 do_verify :=
  assert_succeeds_preserve_error (once (time "cbv" cbv); do_verify ()).
Ltac timetest4 do_verify :=
  assert_succeeds_preserve_error (once (time "native_compute(1)" native_compute); do_verify ());
  assert_succeeds_preserve_error (once (time "native_compute(2)" native_compute); do_verify ()).
Ltac timetest5 do_verify :=
  assert_succeeds_preserve_error (once (time "cbn" cbn); do_verify ()).
Ltac timetest6 do_verify :=
  assert_succeeds_preserve_error (once (time "simpl" simpl); do_verify ()).

Global Open Scope Z_scope.

Ltac test_from_to_gen do_verify test_tac min max step :=
  idtac;
  let min := (eval vm_compute in min) in
  idtac "Params: n=" min;
  assert_succeeds_preserve_error (once (assert (goal min); [ start (); test_tac do_verify | ]));
  let finished := (eval vm_compute in ((min + step) >? max)%Z) in
  lazymatch finished with
  | true => idtac
  | false => test_from_to_gen do_verify test_tac (min + step)%Z max
  end.
Ltac test_from_to test_tac min max step := test_from_to_gen ltac:(fun _ => idtac) test_tac min max step.
Ltac test_from_to_safe test_tac min max step := test_from_to_gen verify test_tac min max step.
(*

Goal let n := 5000%Z in
     sieve n = nil.
Proof.
  cbv [sieve].
  Time assert_succeeds vm_compute.
  Time assert_succeeds cbv.
  Time assert_succeeds lazy.
  Set Printing Width 150.
  time "Rewrite_for" assert_succeeds (Rewrite_lhs_for myrew).
  Rewrite_lhs_for myrew.
  Set Printing Depth 1000000.
  time "cbv;rewrite!" assert_succeeds (cbv [nat_rect_arrow_nodep nat_rect_nodep]; rewrite !Z.add_0_r).
  time "cbv;setoid_rewrite" assert_succeeds (cbv [nat_rect_arrow_nodep nat_rect_nodep]; repeat setoid_rewrite Z.add_0_r).
  time "cbv;rewrite_strat(topdown)" assert_succeeds ((rewrite_strat eval cbv [nat_rect_arrow_nodep nat_rect_nodep]); rewrite_strat topdown Z.add_0_r).
  time "cbv;rewrite_strat(bottomup)" assert_succeeds ((rewrite_strat eval cbv [nat_rect_arrow_nodep nat_rect_nodep]); rewrite_strat bottomup Z.add_0_r).
  Fail time "rewrite_strat(cbv;topdown)" (*assert_succeeds*) ((rewrite_strat (eval cbv [nat_rect_arrow_nodep nat_rect_nodep]; topdown Z.add_0_r))).
  Fail time "rewrite_strat(cbv;bottomup)" (*assert_succeeds*) ((rewrite_strat (eval cbv [nat_rect_arrow_nodep nat_rect_nodep]; bottomup Z.add_0_r))).
  Time Rewrite_for myrew.
  Show.
Abort.
*)
