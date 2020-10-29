Require Import Coq.QArith.QArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Export Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Rewriter.Util.Prod.
Require Import Rewriter.Util.Bool.Reflect.
Require Import Rewriter.Rewriter.Examples.PerfTesting.Harness.
Require Rewriter.Rewriter.Examples.PerfTesting.Sample.
Require Import Rewriter.Util.plugins.RewriterBuild.
Require Export Rewriter.Rewriter.Examples.PerfTesting.Settings.
Import ListNotations.
Local Open Scope list_scope. Local Open Scope Z_scope.

Definition sieve' (fuel : nat) (max : Z)
  := List.rev
       (fst
          (@nat_rect
             (fun _ => list Z (* primes *) * PositiveSet.t (* composites *) * positive (* next_prime *) -> list Z (* primes *) * PositiveSet.t (* composites *))
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

Lemma eval_map
  : forall A B f ls,
    @List.map A B f ls
    = ident.eagerly (@list_rect) _ _ nil (fun l ls map_ls => cons (f l) map_ls) ls.
Proof. induction ls; cbn; f_equal; auto. Qed.

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

Notation lemmas := (eval_rect nat, eval_rect prod, eval_fold_right, eval_map, do_again eval_rev, eval_rect bool, @fst_pair, eval_rect list, eval_app) (only parsing).
Notation extra_idents := (Z.eqb, orb, Z.gtb, PositiveSet.elements, @fst, @snd, PositiveSet.mem, Pos.succ, PositiveSet.add, List.fold_right, List.map, List.seq, Pos.mul, S, Pos.of_nat, Z.to_nat, Z.div, Z.pos, O, PositiveSet.empty) (only parsing).

Time Make myrew := Rewriter For lemmas (with extra idents extra_idents) (with delta).

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

Inductive red_kind := vm | native | cbv | lazy | cbn | simpl | rewrite_lhs_for.

Local Notation "'eta_kind' ( k' => f ) k"
  := match k with
     | vm => subst! vm for k' in f
     | native => subst! native for k' in f
     | cbv => subst! cbv for k' in f
     | lazy => subst! lazy for k' in f
     | cbn => subst! cbn for k' in f
     | simpl => subst! simpl for k' in f
     | rewrite_lhs_for => subst! rewrite_lhs_for for k' in f
     end
       (only parsing, at level 70, k' ident).

Local Lemma sanity : forall T f k, eta_kind (k => f k) k = f k :> T.
Proof. intros; repeat match goal with |- context[match ?e with _ => _ end] => destruct e end; reflexivity. Qed.

Definition size_of_kind (k : red_kind) (arg : Z) : Q
  := let x := inject_Z arg in
     match k with
     | vm
       => 9.56E-04 + 9.75E-06*x + 1.55E-08*x^2
     | native
       => (0.0963 + 6.75E-06*x + 4.29E-09*x^2)
          (* * 2 *)
     | cbv
       => 1.93E-03 + 4.25E-05*x + 3.01E-07*x^2
     | lazy
       => 1.07E-03 + 3.93E-05*x + 7.6E-07*x^2
     | rewrite_lhs_for
       => 1.08365515226278e-06*x^2+0.00014590531005911*x+0.518568221580904
     | cbn
       => -2.11 + 0.262*x + -3.49E-03*x^2 + 3.16E-05*x^3
     | simpl
       => -1.48 + 0.162*x + -1.52E-03*x^2 + 2.45E-05*x^3
     end%Q.

Definition max_input_of_kind (k : red_kind) : option Z
  := match k with
     | vm => None
     | native => None
     | rewrite_lhs_for => None
     | cbv => None
     | lazy => None
     | cbn => None
     | simpl => None
     end.
(*   Definition args_of_size (test_tac_n : nat) (s : size)
    := match test_tac_n, s with
       | 0%nat, SuperFast => [(2, 3, 1); (5, 49, 2)]
       | 1%nat, SuperFast => [(2, 3, 1); (5, 1199, 2)]
       | 2%nat, SuperFast => [(2, 3, 1); (5, 449, 2)]
       | 3%nat, SuperFast => [(2, 3, 1); (5, 499, 2)]
       | 4%nat, SuperFast => [(2, 3, 1); (5, 39, 2)]
       | 5%nat, SuperFast => [(2, 3, 1); (5, 39, 2)]
       | 6%nat, SuperFast => [(2, 3, 1); (5, 39, 2)]
       | 0%nat, Fast => [(51, 4999, 2)]
       | 1%nat, Fast => [(1201, 4999, 2)]
       | 2%nat, Fast => [(451, 3999, 2)]
       | 3%nat, Fast => [(501, 4999, 2)]
       | 4%nat, Fast => [(41, 4999, 2)]
       | 5%nat, Fast => [(41, 79, 2)]
       | 6%nat, Fast => [(41, 79, 2)]
       | 2%nat, Medium => [(4001, 4999, 2)]
       | 5%nat, Medium => [(81, 149, 2)]
       | 6%nat, Medium => [(81, 149, 2)]
       | 5%nat, Slow => [(151, 189, 2)]
       | 6%nat, Slow => [(151, 189, 2)]
       | 5%nat, VerySlow => [(191, 4999, 2)]
       | 6%nat, VerySlow => [(191, 4999, 2)]
       | 0%nat, _ | 1%nat, _ | 2%nat, _ | 3%nat, _ | 4%nat, _ => []
       | _, _ => []
       end%Z.
*)

Definition args_of_size' (k : red_kind) (s : size) : list Z
  := Eval cbv beta iota in
      eta_size
        (s'
         => if match s' with Sanity => true | _ => false end
            then [2; 3; 4; 5; 6; 7; 8; 9; 10]
            else eta_kind
                   (k'
                    => Sample.generate_inputs
                         (T:=Z)
                         2
                         (size_of_kind k')
                         (Qseconds_of_size s')
                         (Qstandard_max_seconds_of_size s')
                         Sample.default_max_points
                         (max_input_of_kind k'))
                   k)
        s.
Local Set NativeCompute Profiling.
Local Set NativeCompute Timing.
(* Takes about 0.6 seconds *)
Time Definition args_of_size (k : red_kind) (s : size)
  := Eval native_compute in eta_size (s' => eta_kind (k' => args_of_size' k' s') k) s.

Ltac mkgoal kind n := constr:(goal n).
Ltac redgoal _ := start ().
Ltac describe_goal n :=
  let n := (eval vm_compute in n) in
  idtac "Params: n=" n.

Ltac time_solve_goal kind
  := lazymatch kind with
     | vm
       => fun n
          => time "vm_compute-regression-quadratic" vm_compute
     | native
       => fun n
          => let G := match goal with |- ?G => G end in
             cut G; [ intros _ | ];
             [ time "native_compute(1)-regression-quadratic" native_compute
             | time "native_compute(2)-regression-quadratic" native_compute;
               shelve ]
     | rewrite_lhs_for
       => fun n
          => time "Rewrite_lhs_for-regression-quadratic" Rewrite_lhs_for myrew
     | cbv
       => fun n
          => time "cbv-regression-quadratic" cbv
     | lazy
       => fun n
          => time "lazy-regression-quadratic" lazy
     | cbn
       => fun n
          => time "cbn-regression-cubic" cbn
     | simpl
       => fun n
          => time "simpl-regression-cubic" simpl
     end.

(**
<<<

#!/usr/bin/env python3

print(r'''(**
<<<
''')
print(open(__file__, 'r').read())
print(r'''>>>
 *)''')

for i, c in enumerate(('vm', 'native', 'cbv', 'lazy', 'cbn', 'simpl', 'rewrite_lhs_for')):
    print(f'Ltac mkgoal{i} := mkgoal constr:({c}).\nLtac time_solve_goal{i} := time_solve_goal constr:({c}).\nLtac run{i} sz := Harness.runtests_verify_sanity (args_of_size ({c})) describe_goal mkgoal{i} redgoal time_solve_goal{i} verify sz.\n')

>>>
 *)
Ltac mkgoal0 := mkgoal constr:(vm).
Ltac time_solve_goal0 := time_solve_goal constr:(vm).
Ltac run0 sz := Harness.runtests_verify_sanity (args_of_size (vm)) describe_goal mkgoal0 redgoal time_solve_goal0 verify sz.

Ltac mkgoal1 := mkgoal constr:(native).
Ltac time_solve_goal1 := time_solve_goal constr:(native).
Ltac run1 sz := Harness.runtests_verify_sanity (args_of_size (native)) describe_goal mkgoal1 redgoal time_solve_goal1 verify sz.

Ltac mkgoal2 := mkgoal constr:(cbv).
Ltac time_solve_goal2 := time_solve_goal constr:(cbv).
Ltac run2 sz := Harness.runtests_verify_sanity (args_of_size (cbv)) describe_goal mkgoal2 redgoal time_solve_goal2 verify sz.

Ltac mkgoal3 := mkgoal constr:(lazy).
Ltac time_solve_goal3 := time_solve_goal constr:(lazy).
Ltac run3 sz := Harness.runtests_verify_sanity (args_of_size (lazy)) describe_goal mkgoal3 redgoal time_solve_goal3 verify sz.

Ltac mkgoal4 := mkgoal constr:(cbn).
Ltac time_solve_goal4 := time_solve_goal constr:(cbn).
Ltac run4 sz := Harness.runtests_verify_sanity (args_of_size (cbn)) describe_goal mkgoal4 redgoal time_solve_goal4 verify sz.

Ltac mkgoal5 := mkgoal constr:(simpl).
Ltac time_solve_goal5 := time_solve_goal constr:(simpl).
Ltac run5 sz := Harness.runtests_verify_sanity (args_of_size (simpl)) describe_goal mkgoal5 redgoal time_solve_goal5 verify sz.

Ltac mkgoal6 := mkgoal constr:(rewrite_lhs_for).
Ltac time_solve_goal6 := time_solve_goal constr:(rewrite_lhs_for).
Ltac run6 sz := Harness.runtests_verify_sanity (args_of_size (rewrite_lhs_for)) describe_goal mkgoal6 redgoal time_solve_goal6 verify sz.

Global Set NativeCompute Timing.
Global Open Scope Z_scope.

(*
Goal True.
  run6 Sanity.
  cut (goal 10).
  shelve.
  cbn.
  run5 Sanity.
*)
