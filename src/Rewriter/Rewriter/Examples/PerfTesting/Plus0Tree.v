Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Rewriter.Util.Option Rewriter.Util.Strings.ParseArithmetic.
Require Import Rewriter.Rewriter.Examples.PerfTesting.Harness.
Require Import Rewriter.Util.plugins.RewriterBuild.
Require Rewriter.Rewriter.Examples.PerfTesting.Sample.
Require Export Rewriter.Rewriter.Examples.PerfTesting.Settings.
Local Open Scope Z_scope.

Definition iter_plus_acc (m : nat) (acc v : Z) :=
  @nat_rect
    (fun _ => Z -> Z)
    (fun acc => acc)
    (fun _ rec acc => rec (acc + v))
    m
    acc.

Definition make_tree (n : nat) (m : nat) (v : Z) (acc : Z) :=
  Eval cbv [iter_plus_acc pred] in
    @nat_rect
      (fun _ => Z * Z -> Z)
      (fun '(v, acc) => iter_plus_acc m (acc + acc) v)
      (fun _ rec '(v, acc) => iter_plus_acc m (rec (v, acc) + rec (v, acc)) v)
      n
      (v, acc).

Definition eval_Z_to_nat n : Z.to_nat ('n) = '(Z.to_nat n).
Proof. reflexivity. Qed.

Time Make myrew := Rewriter For (Z.add_0_r, eval_Z_to_nat, eval_rect nat, eval_rect prod).

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

(* size(iter_plus_acc(m, acc, v)) := size(acc) + m * (1 + size(v))
   size(make_tree(0, m, v, acc)) := size(iter_plus_acc(m, 1+2*size(acc), v))
   size(make_tree(1+n,m,v, acc)) := size(iter_plus_acc(m, 1+2*size(make_tree(n,m,v,acc)), v)) *)
(* RSolve[{mt[0, m, v, acc] == ipa[m, 1 + 2*acc, v],
   mt[n, m, v, acc] == ipa[m, 1 + 2*mt[n - 1, m, v, acc], v]} /.
  ipa[m_, acc_, v_] :> acc + m*(1 + v), mt[n, m, v, acc], n]
 *)
(* mt[n, m, v, acc] -> -1 + 2^(1 + n) + 2^(1 + n) acc - m + 2^(1 + n) m -
   m v + 2^(1 + n) m v *)
(* mt[n, m, 1, 1] -> 1 + 2 (2^(n + 1) - 1) (m + 1) *)
Definition input_num_nodes (n : Z) (m : Z) : Z
  := (1 + 2 * (2^(n+1) - 1) * (m + 1))%Z.

(* size(iter_plus_acc(m, acc)) := size(acc)
   size(make_tree(0, m, v, acc)) := size(iter_plus_acc(m, 1+2*size(acc), v))
   size(make_tree(1+n,m,v, acc)) := size(iter_plus_acc(m, 1+2*size(make_tree(n,m,v,acc)), v)) *)
(* RSolve[{mt[0, m, v, acc] == ipa[m, 1 + 2*acc, v],
   mt[n, m, v, acc] == ipa[m, 1 + 2*mt[n - 1, m, v, acc], v]} /.
  ipa[m_, acc_, v_] :> acc, mt[n, m, v, acc], n]
 *)
(* mt[n, m, v, acc] -> -1 + 2^(1 + n) + 2^(1 + n) acc *)
(* mt[n, m, _, 1] -> -1 + 2^(2 + n) *)
Definition output_num_nodes (n : Z) (m : Z) : Z
  := (2^(n+2)-1)%Z.

(* #0s(iter_plus_acc(m, acc, v)) := #0s(acc) + m * #0s(v)
   #0s(make_tree(0, m, v, acc)) := #0s(iter_plus_acc(m, 2*#0s(acc), v))
   #0s(make_tree(1+n,m,v, acc)) := #0s(iter_plus_acc(m, 2*#0s(make_tree(n,m,v,acc)), v)) *)
(* RSolve[{mt[0, m, v, acc] == ipa[m, 2*acc, v],
   mt[n, m, v, acc] == ipa[m, 2*mt[n - 1, m, v, acc], v]} /.
  ipa[m_, acc_, v_] :> acc + m*v, mt[n, m, v, acc], n]
 *)
(* mt[n, m, v, acc] -> 2^(1 + n) acc - m v + 2^(1 + n) m v *)
(* mt[n, m, 1, 0] -> (-1 + 2^(n + 1)) m *)
Definition output_num_rewrites (n : Z) (m : Z) : Z
  := ((2^(n+1) - 1) * m)%Z.

Definition size_of_arg (arg : Z * Z) : Z
  := Eval cbv [output_num_nodes output_num_rewrites] in
      output_num_rewrites (fst arg) (snd arg).

Definition invert_size_of_arg_dumb (v : Z) : Z * Z
  := (0%Z, v).

Local Lemma invert_size_of_arg_dumb_correct v
  : size_of_arg (invert_size_of_arg_dumb v) = v.
Proof. cbv [size_of_arg invert_size_of_arg_dumb]; cbn [fst snd]; vm_compute Z.pow; lia. Qed.

Local Instance Z_prod_has_compress : Sample.has_compress (Z * Z) Z := size_of_arg.
Local Instance Z_prod_has_make : Sample.has_make (Z * Z) Z := { make_T := invert_size_of_arg_dumb ; make_T_correct := invert_size_of_arg_dumb_correct }.

Module Import instances.
  Import Coq.QArith.QArith Coq.QArith.Qround Coq.QArith.Qabs Coq.QArith.Qminmax.
  Import Sample.
  Local Open Scope Z_scope.
  Local Set Warnings Append "-ambiguous-paths".
  Local Coercion N.of_nat : nat >-> N.
  Local Coercion N.to_nat : N >-> nat.
  Local Coercion Z.of_N : N >-> Z.
  Local Coercion inject_Z : Z >-> Q.
  Local Coercion Npos : positive >-> N.

  Definition allocate_points_for (n : Z) (min max : Z) (max_points : N) : list (Z * Z)
    := let v : Z := compress_T (n:Z, 1) in
       List.map (fun m => (n:Z, m))
                (Zrange_max_points (Qceiling (min / v))
                                   (Qfloor (max / v))
                                   max_points).
  Fixpoint alloc_down_from (points_remaining : N) (min max : Z) (n : nat) : list (Z * Z)
    := match points_remaining with
       | 0%N => []
       | 1%N => [(0, max)]
       | 2%N => [(0, min); (0, max)]
       | _
         => let max_cur_points := (points_remaining / S n)%N in
            let cur_points := allocate_points_for n min max max_cur_points in
            match n with
            | O => []
            | S n' => alloc_down_from (points_remaining - List.length cur_points) min max n'
            end
              ++ cur_points
       end.

  (** If we don't have enough points, start going through from the smallest value of [n] and filling in all possible points *)
  Fixpoint extra_alloc_at_bottom (extra_points_remaining : N)
           (min max : Z)
           (sparse_points dense_points : list (Z * Z))
           (cur_n : nat)
           (fuel : nat)
    : list (Z * Z)
    := if ((extra_points_remaining =? 0)%N || (max <? min))
       then dense_points ++ sparse_points
       else
         let '(removed_points, sparse_points) := List.partition (fun '(n, m) => (n =? cur_n)) sparse_points in
         let extra_points_remaining := (extra_points_remaining + List.length removed_points)%N in
         let new_points := allocate_points_for extra_points_remaining min max cur_n in
         let extra_points_remaining := (extra_points_remaining - List.length new_points)%N in
         let dense_points := dense_points ++ new_points in
         match fuel with
         | O => dense_points ++ sparse_points
         | S fuel
           => extra_alloc_at_bottom extra_points_remaining min max sparse_points dense_points (S cur_n) fuel
         end.

  Definition extra_alloc_if_necessary
             (max_n : Z)
             (min max : Z)
             (n_points : N)
             (cur_points : list (Z * Z))
    := extra_alloc_at_bottom (n_points - List.length cur_points) min max cur_points [] O (Z.to_nat max_n).

  Global Instance Z_prod_has_alloc : has_alloc (Z * Z)
  := { alloc_T min max n
       := match n with
          | 0%N => []
          | 1%N => [max]
          | 2%N => [min; max]
          | _
            => (let min := compress_T min in
                let max := compress_T max in
                let max_n := (* max = (2^(n+1) - 1) * m; m = 1 *) Z.log2 (max + 1) - 1 in
                if max_n + 1 <=? (1 + (n+1)/3)
                then
                   (* we want all the possible values of the first pair *)
                  alloc_down_from n min max (Z.to_nat max_n)
                else
                  extra_alloc_if_necessary
                    max_n min max n
                    (List.flat_map
                       (fun v => allocate_points_for v min max 3)
                       (alloc_T 0 max_n (1 + (n+1)/3))))%Z
          end }.
End instances.

Inductive rewrite_strat_kind := topdown | bottomup.
Inductive kind_of_rewrite := kind_rewrite_strat (_ : rewrite_strat_kind) | kind_setoid_rewrite | kind_rewrite | kind_autorewrite | kind_ssr_rewrite | kind_rewrite_lhs_for.

Local Notation "'eta_kind' ( k' => f ) k"
  := match k with
     | kind_rewrite_strat topdown
       => subst! (kind_rewrite_strat topdown) for k' in f
     | kind_rewrite_strat bottomup
       => subst! (kind_rewrite_strat bottomup) for k' in f
     | kind_setoid_rewrite => subst! kind_setoid_rewrite for k' in f
     | kind_rewrite => subst! kind_rewrite for k' in f
     | kind_autorewrite => subst! kind_autorewrite for k' in f
     | kind_ssr_rewrite => subst! kind_ssr_rewrite for k' in f
     | kind_rewrite_lhs_for => subst! kind_rewrite_lhs_for for k' in f
     end
       (only parsing, at level 70, k' ident).

Local Lemma sanity : forall T f k, eta_kind (k => f k) k = f k :> T.
Proof. intros; repeat match goal with |- context[match ?e with _ => _ end] => destruct e end; reflexivity. Qed.

(* datastr = <....>;
tbl = Map[
   Map[(If[StringLength[#] == 0, Null,
        If[StringMatchQ[#, NumberString], ToExpression[#], #]]) &,
     StringSplit[#, ",", All]] &, StringSplit[datastr, "\n"]];
cols = Transpose[tbl] /. {x_String, ___} :>
    Sequence[] /;
     Not[StringMatchQ[x, "param-" ~~ ___] ||
       StringMatchQ[x, ___ ~~ "-regression-" ~~ ___ ~~ "-real"]];
data = Map[{#[[1]],
      Transpose[{Drop[cols[[1]], 1], Drop[#, 1]}] /. {_, Null} :>
        Sequence[]} &, cols] /. {x_String, _} :>
    Sequence[] /; StringMatchQ[x, "param-" ~~ ___];
data3D = Map[{#[[1]],
      Transpose[{Drop[cols[[2]], 1], Drop[cols[[3]], 1],
         Drop[#, 1]}] /. {_, _, Null} :> Sequence[]} &,
    cols] /. {x_String, _} :>
    Sequence[] /; StringMatchQ[x, "param-" ~~ ___];
fits = Map[{#[[1]],
     NonlinearModelFit[#[[2]],
      a + b X + c Y + d X Y + e X^2 + f Y^2 + g X^3 + h X^2 Y +
        i X Y^2 + j Y^3 /. {X -> 2^n, Y -> m}, {a, b, c, d, e, f, g,
       h, i, j}, {n, m}]} &, data3D];
fits2 = Map[{#[[1]],
     NonlinearModelFit[#[[2]],
      a + b X + c Y + d X Y + e X^2 + f Y^2 /. {X -> 2^n, Y -> m}, {a,
        b, c, d, e, f}, {n, m}]} &, data3D];
ListPlot[Map[#[[2]] &, data], PlotLegends -> Map[#[[1]] &, data], PlotRange -> Full]
ListPointPlot3D[Map[#[[2]] &, data3D],
 PlotLegends -> Map[#[[1]] &, data3D], PlotRange -> Full,
 AxesLabel -> {n, m, z}]
Table[Function[{d}, {Show[
     ListPointPlot3D[Map[#[[2]] &, data3D[[{d}]]],
      PlotLegends -> Map[#[[1]] &, data3D[[{d}]]],
      PlotRange -> {Full, Full, {0, 10}}, AxesLabel -> {n, m, z}],
     Plot3D[fits[[d]][[2]][n, m], {n, 0, 10}, {m, 0, 1500}(*,
      PlotLegends\[Rule]{Normal[fits[[d]][[2]]]}*)],
     ImageSize -> Large], Normal[fits[[d]][[2]]]}][d], {d, 1,
  Length[data3D]}]
Map[{#[[1]], Normal[#[[2]]] /. n -> 0 /. m -> x} &, fits]
Map[{#[[1]], Normal[#[[2]]] /. n -> 0 /. m -> x} &, fits2]
(*ExpandAll[
 Map[{#[[1]], Normal[#[[2]]] /. n -> Log2[x + 1] - 1 /. m -> 1} &,
  fits]]*)
 *)

Local Notation parse x := (invert_Some (parseQ_arith_strict x)) (only parsing).
Local Notation parse_poly_expr p x := (invert_Some (parseQexpr_arith_with_vars [("x"%string, x)] p)) (only parsing).
Local Notation red_vm_compute x := (ltac:(let z := (eval vm_compute in x) in
                                          exact z)) (only parsing).
Local Notation parse_poly p x := (invert_Some (eval_Qexpr_strict (red_vm_compute (parse_poly_expr p x)))) (only parsing).

Definition size_of_kind (k : kind_of_rewrite) (arg : Z * Z) : Q
  := let termsize := size_of_arg arg in
     let x := inject_Z termsize in
     let '(n, m) := (fst arg, inject_Z (snd arg)) in
     match k with
     | kind_rewrite_strat bottomup
       => (*-0.218 + 3.68E-03*x + 6.64E-06*x^2*)
       parse_poly "-0.964971 + 0.00567641*x + 0.000133294*x^2"%string x
(*       -0.0419087 - 0.015458 * 2^n - 0.000126407 * 2^(2 * n) -
 1.08304E-7 * 2^(3 * n) - 0.0248191 * m + 0.00639815 * 2^n * m +
 0.00021925 * 2^(2 * n) * m + 0.000265979 * m^2 + 0.000269755 * 2^n * m^2 -
 3.14699E-6 * m^3*)
     | kind_rewrite_strat topdown
       => (*0.141 + -8.55E-04*x + 3.28E-06*x^2*)
       parse_poly "-0.151224 + 0.000230063*x + 4.83713E-6*x^2 + 4.31671E-10*x^3"%string x
(*       -0.144716 - 0.00652151 * 2^n + 0.0000138788 * 2^(2 * n) -
 7.77221E-9 * 2^(3 * n) - 0.00374702 * m + 0.00397668 * 2^n * m +
 4.03926E-7 * 2^(2 * n) * m - 0.0000288226 * m^2 + 0.0000336598 * 2^n * m^2 +
 4.31671E-10 * m^3*)
     | kind_setoid_rewrite
       => (*3.51E-03 + 4.45E-04*x + 3.73E-06*x^2*)
       parse_poly "-0.169646 + 0.00123046*x + 8.46486E-6*x^2"%string x
(*       -0.0916119 - 0.0127236 * 2^n + 0.0000322477 * 2^(2 * n) -
 7.57294E-8 * 2^(3 * n) - 0.00446198 * m + 0.00482246 * 2^n * m +
 0.0000287754 * 2^(2 * n) * m - 0.0000508636 * m^2 + 0.0000606788 * 2^n * m^2 -
 5.46448E-10 * m^3*)
     | kind_rewrite
       => (*5.67E-03 + 1.33E-04*x + 1.1E-06*x^2*)
       parse_poly "-0.0698785 + 0.000620073*x + 3.63E-6*x^2 + 9.61722E-10*x^3"%string x
(*       -0.0683191 - 0.00156502 * 2^n + 5.57927E-6 * 2^(2 * n) -
 1.73021E-9 * 2^(3 * n) - 0.000478266 * m + 0.00110145 * 2^n * m -
 3.1091E-6 * 2^(2 * n) * m - 0.0000256011 * m^2 + 0.0000292311 * 2^n * m^2 +
 9.61722E-10 * m^3*)
     | kind_autorewrite
       => (*0.0219 + 2.31E-04*x + 1.02E-06*x^2*)
       parse_poly "-0.0585252 + 0.00014934*x + 4.96778E-6*x^2 + 2.96753E-10*x^3"%string x
(*       -0.0586838 + 0.000158133 *2^n + 4.35038E-7 *2^(2* n) +
 5.13011E-10 *2^(3* n) - 0.000282043 * m + 0.000432666 *2^n* m -
 1.28322E-6 *2^(2 *n) *m - 0.0000307768 *m^2 + 0.0000357446 * 2^n * m^2 +
 2.96753E-10 *m^3*)
     | kind_ssr_rewrite
       => (*3.98E-03 + 2.32E-04*x + 2.01E-06*x^2*)
       parse_poly "-0.0684302 + 0.000469109*x + 7.5704E-6*x^2 + 5.51547E-10*x^3"%string x
(*       -0.0667915 - 0.00164326 * 2^n + 4.56044E-6 * 2^(2 * n) -
 1.29764E-9 * 2^(3 * n) - 0.000935073 * m + 0.00140678 * 2^n * m -
 2.59326E-6 * 2^(2 * n) * m - 0.0000493663 * m^2 + 0.0000569367 * 2^n * m^2 +
 5.51547E-10 * m^3*)
     | kind_rewrite_lhs_for
       => parse_poly "0.256649 - 8.2992E-7 *x + 7.03001E-10 *x^2"%string x
     end%Q.

Definition max_input_of_kind (k : kind_of_rewrite) : option (Z * Z)
  := match k with
     | kind_rewrite_strat _
       => None
     | kind_setoid_rewrite
       => None
     | kind_rewrite
       => None
     | kind_autorewrite
       => None
     | kind_ssr_rewrite
       => None
     | kind_rewrite_lhs_for
       => None
     end%Z.

Definition args_of_size' (k : kind_of_rewrite) (s : size) : list (Z * Z)
  := Eval cbv beta iota in
      eta_size
        (s'
         => if match s' with Sanity => true | _ => false end
            then [(0, 1); (0, 2); (0, 3); (1, 1); (0, 4); (0, 5); (0, 6); (1, 2)]
            else eta_kind
                   (k'
                    => Sample.generate_inputs
                         (T:=Z*Z)
                         (0, 1)
                         (size_of_kind k')
                         (Qseconds_of_size s')
                         (Qstandard_max_seconds_of_size s')
                         Sample.default_max_points
                         (max_input_of_kind k'))
                   k)
        s.
Local Set NativeCompute Profiling.
Local Set NativeCompute Timing.
(* Takes about 2 seconds *)
Time Definition args_of_size (k : kind_of_rewrite) (s : size)
  := Eval native_compute in eta_size (s' => eta_kind (k' => args_of_size' k' s') k) s.


Ltac mkgoal kind nm
  := let Z_to_nat := (eval vm_compute in Z.to_nat) in
     lazymatch nm with
     | (?n, ?m)
       => let n := constr:(id Z_to_nat n) in
          let m := constr:(id Z_to_nat m) in
          constr:(goal n m)
     end.
Ltac redgoal _ := start ().
Ltac describe_goal nm :=
  lazymatch nm with
  | (?n, ?m)
    => let sz := (eval vm_compute in (size_of_arg nm)) in
       let input_num_nodes := (eval vm_compute in (input_num_nodes n m)) in
       let output_num_nodes := (eval vm_compute in (output_num_nodes n m)) in
       let num_rewrites := (eval vm_compute in (output_num_rewrites n m)) in
       idtac "Params: 0-nm=" sz ", 1-n=" n ", 2-m=" m ", 3-input-size=" input_num_nodes ", 4-output-size=" output_num_nodes ", 5-num-rewrites=" num_rewrites
  end.

Hint Rewrite Z.add_0_r : mydb.

Ltac do_coq_rewrite _ := rewrite -> !Z.add_0_r.

Require Import Coq.ssr.ssreflect.

Ltac do_ssr_rewrite _ := rewrite !Z.add_0_r.

Ltac time_solve_goal kind
  := let Z_to_nat := (eval cbv in Z.to_nat) in
     let change_Z_to_nat _ := (change (id Z_to_nat) with Z.to_nat) in
     lazymatch kind with
     | kind_rewrite_strat topdown
       => fun nm
          => time "rewrite_strat(topdown)-regression-cubic"
                  (cbv [nat_rect id]; repeat rewrite_strat topdown hints mydb)
     | kind_rewrite_strat bottomup
       => fun nm
          => time "rewrite_strat(bottomup)-regression-cubic"
                  (cbv [nat_rect id]; repeat rewrite_strat bottomup hints mydb)
     | kind_setoid_rewrite
       => fun nm
          => time "setoid_rewrite-regression-cubic"
                  (cbv [nat_rect id]; repeat setoid_rewrite Z.add_0_r)
     | kind_rewrite
       => fun nm
          => time "rewrite!-regression-cubic"
                  (cbv [nat_rect id]; do_coq_rewrite ())
     | kind_ssr_rewrite
       => fun nm
          => time "ssr-rewrite!-regression-cubic"
                  (cbv [nat_rect id]; do_ssr_rewrite ())
     | kind_autorewrite
       => fun nm
          => time "autorewrite-regression-cubic"
                  (cbv [nat_rect id]; repeat autorewrite with mydb)
     | kind_rewrite_lhs_for
       => fun nm
          => time "Rewrite_lhs_for-regression-quadratic" (change_Z_to_nat (); Rewrite_lhs_for myrew)
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

for i, c in enumerate(('kind_rewrite_strat topdown', 'kind_rewrite_strat bottomup', 'kind_setoid_rewrite', 'kind_rewrite', 'kind_ssr_rewrite', 'kind_autorewrite')):
    print(f'Ltac mkgoal{i} := mkgoal constr:({c}).\nLtac time_solve_goal{i} := time_solve_goal constr:({c}).\nLtac run{i} sz := Harness.runtests_verify_sanity (args_of_size ({c})) describe_goal mkgoal{i} redgoal time_solve_goal{i} verify sz.\n')

>>>
 *)
Ltac mkgoal0 := mkgoal constr:(kind_rewrite_strat topdown).
Ltac time_solve_goal0 := time_solve_goal constr:(kind_rewrite_strat topdown).
Ltac run0 sz := Harness.runtests_verify_sanity (args_of_size (kind_rewrite_strat topdown)) describe_goal mkgoal0 redgoal time_solve_goal0 verify sz.

Ltac mkgoal1 := mkgoal constr:(kind_rewrite_strat bottomup).
Ltac time_solve_goal1 := time_solve_goal constr:(kind_rewrite_strat bottomup).
Ltac run1 sz := Harness.runtests_verify_sanity (args_of_size (kind_rewrite_strat bottomup)) describe_goal mkgoal1 redgoal time_solve_goal1 verify sz.

Ltac mkgoal2 := mkgoal constr:(kind_setoid_rewrite).
Ltac time_solve_goal2 := time_solve_goal constr:(kind_setoid_rewrite).
Ltac run2 sz := Harness.runtests_verify_sanity (args_of_size (kind_setoid_rewrite)) describe_goal mkgoal2 redgoal time_solve_goal2 verify sz.

Ltac mkgoal3 := mkgoal constr:(kind_rewrite).
Ltac time_solve_goal3 := time_solve_goal constr:(kind_rewrite).
Ltac run3 sz := Harness.runtests_verify_sanity (args_of_size (kind_rewrite)) describe_goal mkgoal3 redgoal time_solve_goal3 verify sz.

Ltac mkgoal4 := mkgoal constr:(kind_ssr_rewrite).
Ltac time_solve_goal4 := time_solve_goal constr:(kind_ssr_rewrite).
Ltac run4 sz := Harness.runtests_verify_sanity (args_of_size (kind_ssr_rewrite)) describe_goal mkgoal4 redgoal time_solve_goal4 verify sz.

Ltac mkgoal5 := mkgoal constr:(kind_autorewrite).
Ltac time_solve_goal5 := time_solve_goal constr:(kind_autorewrite).
Ltac run5 sz := Harness.runtests_verify_sanity (args_of_size (kind_autorewrite)) describe_goal mkgoal5 redgoal time_solve_goal5 verify sz.

Ltac mkgoal6 := mkgoal constr:(kind_rewrite_lhs_for).
Ltac time_solve_goal6 := time_solve_goal constr:(kind_rewrite_lhs_for).
Ltac run6 sz := Harness.runtests_verify_sanity (args_of_size (kind_rewrite_lhs_for)) describe_goal mkgoal6 redgoal time_solve_goal6 verify sz.

Hint Opaque Z.add : rewrite typeclass_instances.

Global Instance : forall {A}, Proper (eq ==> eq ==> Basics.flip Basics.impl) (@eq A) := _.
Global Instance : Proper (eq ==> eq ==> eq) Z.add := _.
Global Instance : forall {acc}, @ProperProxy Z (@eq Z) acc := _.
Global Instance : forall {A}, subrelation (@eq A) (@eq A) := _.

Global Set NativeCompute Timing.
Global Open Scope Z_scope.

(*
Goal True.
  run3 Sanity.
*)
