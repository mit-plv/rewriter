(** Utility file for subsampling large distributions *)
From Coq Require Import String.
From Coq Require Import Orders.
From Coq Require Import Lia.
From Coq Require Import Bool.
From Coq Require Import Mergesort.
From Coq Require Import QArith Qround Qabs Qminmax.
From Coq Require Import NArith.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import List.
Require Import Rewriter.Util.LetIn.
Import ListNotations.
Local Open Scope list_scope.
Local Set Implicit Arguments.

Definition extra_fuel : nat := 100%nat.
Definition cutoff_elem_count := 6%N.
Definition default_max_points := 1000%N.
Definition precision_binary_digits := 32%N.
Definition smallest_time_Q := Qpower (10#1) (-5). (* don't allow times smaller than this *)
Definition min_fractional_change_for_nonlinear_sample : Q := 1%Q. (* if going from [a] to [b] increases by less than this number times the size at [a], just distribute points uniformly *)
Definition max_subdivisions := 8%nat.
Definition continued_fraction_precision := 4%nat.

Local Set Warnings Append "-ambiguous-paths".
Local Coercion N.of_nat : nat >-> N.
Local Coercion N.to_nat : N >-> nat.
Local Coercion Z.of_N : N >-> Z.
Local Coercion inject_Z : Z >-> Q.
Local Coercion Npos : positive >-> N.

Definition Qround (v : Q) : Z (* away from 0 *)
  := if Qle_bool 0 v
     then Qfloor (v + 1/2)
     else Qceiling (v - 1/2).

Fixpoint continued_fraction (v : Q) (count : nat) : list Z * Q (* 1/remainder *)
  := if Qeq_bool 0 v
     then ([], 0)
     else match count with
          | O => ([], v)
          | S count
            => let a0 := Qfloor v in
               let rem := 1 / (v - a0) in
               let '(rest, rem) := continued_fraction rem count in
               (a0 :: rest, rem)
          end.

Fixpoint eval_continued_fraction' (cfrac : list Z) (rem : Q) : Q
  := match cfrac with
     | [] => rem
     | a0 :: rest
       => a0 + 1 / (eval_continued_fraction' rest rem)
     end.
Definition eval_continued_fraction (v : list Z * Q) : Q
  := eval_continued_fraction' (fst v) (snd v).

Lemma continued_fraction_correct v n
  : eval_continued_fraction (continued_fraction v n) == v.
Proof.
  cbv [eval_continued_fraction].
  revert v; induction n; intro; cbn -[Qeq_bool]; case Qeq_bool eqn:H.
  all: rewrite ?Qeq_bool_iff in H; rewrite <- ?H.
  all: try reflexivity.
  { rewrite (surjective_pairing (continued_fraction _ _)); cbn.
    rewrite IHn.
    cbv [Qdiv]; rewrite !Qmult_1_l, Qinv_involutive.
    ring. }
Qed.

Definition Qround_cfrac_gen (v : Q) (digits : nat) : Q
  := let '(cfrac, _) := continued_fraction v digits in
     eval_continued_fraction (cfrac, 0).

Definition Qround_cfrac (v : Q) : Q := Qround_cfrac_gen v continued_fraction_precision.

Definition lift_1op_cfrac {A} (f : A -> Q) (x : A) := Qround_cfrac (f x).
Definition lift_2op_cfrac {A B} (f : A -> B -> Q) (x : A) (y : B) := Qround_cfrac (f x y).
Definition Qplus_cfrac := lift_2op_cfrac Qplus.
Definition Qminus_cfrac := lift_2op_cfrac Qminus.
Definition Qmult_cfrac := lift_2op_cfrac Qmult.
Definition Qdiv_cfrac := lift_2op_cfrac Qdiv.
Definition Qpower_cfrac := lift_2op_cfrac Qpower.

Module QOrder <: TotalLeBool.
  Local Open Scope Q_scope.
  Local Open Scope Z_scope.
  Definition t := Q.
  Definition leb : t -> t -> bool := Qle_bool.
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb]; intros a1 a2; rewrite !Qle_bool_iff.
    cbv [Qle Qnum Qden]; destruct a1, a2; lia.
  Qed.
End QOrder.

Module QSort := Sort QOrder.
Local Notation sort := QSort.sort.

Module NatIndexOrder (Order : TotalLeBool) <: TotalLeBool.
  Definition t := (nat * Order.t)%type.
  Definition leb : t -> t -> bool := fun '(_, x) '(_, y) => Order.leb x y.
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb]; intros [_ a1] [_ a2]; apply Order.leb_total.
  Qed.
End NatIndexOrder.

Module NatIndexQOrder := NatIndexOrder QOrder.
Module NatIndexQSort := Sort NatIndexQOrder.

Definition sort_by {T} (size : T -> Q) (ls : list T) : list T
  := match ls with
     | nil => nil
     | default :: _
       => List.map (fun '(idx, _) => nth idx ls default)
                   (NatIndexQSort.sort (List.combine (seq 0 (length ls))
                                                     (List.map size ls)))
     end.

Fixpoint find_above_max_size {T} (double : T -> T) (size : T -> Q) (max_size : Q) (ndoublings : nat) (t_prev t_cur : T) (fuel : nat) : T * T * nat (* ndoublings *)
  := match fuel with
     | O => (t_prev, t_cur, ndoublings)
     | S fuel
       => if Qle_bool max_size (size t_cur)
          then (t_prev, t_cur, ndoublings)
          else find_above_max_size double size max_size (S ndoublings) t_cur (double t_cur) fuel
     end.

Fixpoint find_just_below_max_size {T} (avg : T -> T -> T) (size : T -> Q) (max_size : Q) (t_lo t_hi : T) (fuel : nat) : T
  := match fuel with
     | O => t_lo
     | S fuel
       => let sz_lo := size t_lo in
          let sz_hi := size t_hi in
          if Qeq_bool sz_lo sz_hi
          then t_lo
          else let t_mid := avg t_lo t_hi in
               let sz_mid := size t_mid in
               if (Qeq_bool sz_lo sz_mid || Qeq_bool sz_mid sz_hi)
               then t_lo
               else
                 let '(t_lo, t_hi) :=
                     if Qle_bool max_size sz_mid
                     then (t_lo, t_mid)
                     else (t_mid, t_hi) in
                 find_just_below_max_size avg size max_size t_lo t_hi fuel
     end.

Definition find_max {T} (double : T -> T) (avg : T -> T -> T) (size : T -> Q) (max_size : Q) (init : T) : T
  := let '(t_lo, t_hi, ndoublings) := find_above_max_size double size max_size 0 init init (extra_fuel + Z.to_nat (Qceiling max_size)) in
     find_just_below_max_size avg size max_size t_lo t_hi (extra_fuel + Nat.pow 2 (pred ndoublings)).

Class has_double_avg T := { double_T : T -> T ; avg_T : T -> T -> T }.

Class has_leb T := leb_T : T -> T -> bool.
Class has_min T := min_T : T -> T -> T.

Global Instance min_of_leb {T} {leb : has_leb T} : has_min T
  := fun x y => if leb x y
                then x
                else y.

Definition Qred_to_precision (v : Q) (max_lg2_denominator : N) : Q
  := let v := Qred v in
     if (max_lg2_denominator <? N.log2 (Qden v))%N
     then Qred (Qround (v * 2^max_lg2_denominator) / 2^max_lg2_denominator)
     else v.

Definition Qred_to_default_precision (v : Q) : Q
  := Qred_to_precision v precision_binary_digits.

(** Allocate 1/n time to each 1/n of the codomain *)
Fixpoint binary_alloc_QT_fueled
         {T} {HDA : has_double_avg T}
         (size : T -> Q)
         (count_elems : forall min max : T, N)
         (total_time_all_elems : forall min max : T, Q)
         (allocation : Q)
         (min : T) (max : T)
         (cutoff_elem_count : N)
         (max_point_count : N)
         (min_fractional_change_for_nonlinear_sample : Q)
         (fuel : nat)
  : list ((T * T (* min * max *)) * N) * (Q (* allocation used *) * N (* points allocated *))
  := let allocation := Qmax 0 allocation in
     let empty := (nil, (0, 0%N)) in
     let count := count_elems min max in
     if (count =? 0)%N
     then empty
     else
       let time_per_elem := total_time_all_elems min max / count in
       let n_elem := N.min max_point_count (Z.to_N (Qfloor (allocation / time_per_elem))) in
       if (n_elem =? 0)%N
       then empty
       else
         let uniform_result := ([((min, max), n_elem)], (time_per_elem * n_elem, n_elem)) in
         match fuel with
         | O => uniform_result
         | S fuel
           =>
           let '(min_sz, max_sz) := (size min, size max) in
           if ((n_elem <=? cutoff_elem_count)%N
               || (count <=? 2 * n_elem)%N
               || (Qle_bool ((max_sz - min_sz) / min_sz) min_fractional_change_for_nonlinear_sample))
                (* if there are few enough elements left, or if the number of elements that we want is nearly all of them, or we're not changing all that much from [min] to [max], we just distribute the points uniformly *)
           then uniform_result
           else
             let mid := avg_T min max in
             let mid_sz := size mid in
             if Qeq_bool min_sz max_sz || Qeq_bool min_sz mid_sz || Qeq_bool mid_sz max_sz
             then
               ([((min, max), n_elem)], (time_per_elem * n_elem, n_elem))
             else
               let alloc_hi := allocation * (max_sz - mid_sz) / (max_sz - min_sz) in
               let '(ret_hi, (alloc_hi, n_hi)) := binary_alloc_QT_fueled size count_elems total_time_all_elems (Qred alloc_hi) mid max cutoff_elem_count ((1 + max_point_count) / 2) min_fractional_change_for_nonlinear_sample fuel in
               let '(ret_lo, (alloc_lo, n_lo)) := binary_alloc_QT_fueled size count_elems total_time_all_elems (Qred (allocation - alloc_hi)) min mid cutoff_elem_count (max_point_count- n_hi) min_fractional_change_for_nonlinear_sample fuel in
               (ret_lo ++ ret_hi, (Qred (alloc_lo + alloc_hi), (n_lo + n_hi)%N))
         end.

Definition binary_alloc
           {T} {_ : has_double_avg T}
           (size : T -> Q)
           (count_elems : forall min max : T, N)
           (total_time_all_elems : forall min max : T, Q)
           (allocation : Q)
           (min : T) (max : T)
           (cutoff_elem_count : N)
           (max_point_count : N)
           (min_fractional_change_for_nonlinear_sample : Q)
           (alloc : forall min max : T, N -> list T)
  : list T
  := List.flat_map
       (fun '((min, max), n) => alloc min max n)
       (fst (binary_alloc_QT_fueled
               size count_elems total_time_all_elems allocation min max cutoff_elem_count max_point_count min_fractional_change_for_nonlinear_sample
               (Nat.min (Nat.log2_up max_subdivisions)
                        (100 + N.to_nat (N.min 1000 (* we don't want to go too much above 1000, because that would make the nat very big *) max_point_count) + N.to_nat (N.log2_up (count_elems min max)))))).

Fixpoint subdivide
         {T} {HDA : has_double_avg T}
         (min : T) (max : T)
         (lg2_n_parts : nat)
  : list (T * T)
  := match lg2_n_parts with
     | O => [(min, max)]
     | S lg2_n_parts
       => let mid := avg_T min max in
          subdivide min mid lg2_n_parts ++ subdivide mid max lg2_n_parts
     end.

Inductive surplus_state {T} :=
| surplus
| deficit (waiting_max : T).

(** Divide the region up into [2^lg2_n_parts] parts, and allocate
    [1/2^lg2_n_parts] time to each of these parts by assuming that
    every point in each part costs as much as the upper-bound on the
    part; if there is not enough allocation for one of the intervals,
    then we allocate nothing to the intervals before it until we
    recover enough allocation.  Each interval has at least
    [min_point_count] elements, and we allocate at most
    [max_point_count] points total *)
Fixpoint piecewise_uniform_alloc_helper
         {T} {HDA : has_double_avg T}
         (size : T -> Q)
         (allocation_per_subdivision : Q)
         (min_point_count : N)
         (max_point_count_per_subdivision : N)
         (surplus_allocation : Q)
         (extra_unallocated_points : N)
         (st : @surplus_state T)
         (subdivisions : list (T * T))
  : list ((T * T (* min * max *)) * N)
  := match subdivisions, st with
     | [], _ => []
     | (min, max) :: rest, surplus
     | (min, _):: rest, deficit max
       => let max_sz := size max in
          let cur_allocation := allocation_per_subdivision + surplus_allocation in
          let cur_unallocated_points := (max_point_count_per_subdivision + extra_unallocated_points)%N in
          let '(cur_alloc, st, surplus_allocation, extra_unallocated_points)
              := if Qle_bool cur_allocation (min_point_count * max_sz)
                 then ([], deficit max, cur_allocation, cur_unallocated_points)
                 else
                   let n_points := N.min
                                     cur_unallocated_points
                                     (Z.to_N (Qfloor (cur_allocation / max_sz))) in
                   ([((min, max), n_points)],
                    surplus,
                    cur_allocation - n_points * max_sz,
                    (extra_unallocated_points - n_points)%N) in
          cur_alloc
            ++ (piecewise_uniform_alloc_helper
                  size allocation_per_subdivision min_point_count max_point_count_per_subdivision
                  surplus_allocation extra_unallocated_points st
                  rest)
     end.

Definition piecewise_uniform_prealloc
           {T} {HDA : has_double_avg T}
           (size : T -> Q)
           (allocation : Q)
           (min : T) (max : T)
           (min_point_count : N)
           (max_point_count : N)
           (lg2_n_parts : nat)
  := let subdivisions := subdivide min max lg2_n_parts in
     let allocation_per_subdivision := allocation / List.length subdivisions in
     let allocations
         := piecewise_uniform_alloc_helper
              size allocation_per_subdivision min_point_count
              (max_point_count / List.length subdivisions)%N
              0 0 surplus
              (List.rev subdivisions) in
     List.rev allocations.

Definition piecewise_uniform_alloc
           {T} {_ : has_double_avg T}
           (size : T -> Q)
           (allocation : Q)
           (min : T) (max : T)
           (min_points : N)
           (max_points : N)
           (alloc : forall min max : T, N -> list T)
  : list T
  := List.flat_map
       (fun '((min, max), n) => alloc min max n)
       (piecewise_uniform_prealloc size allocation min max min_points max_points (Nat.log2_up max_subdivisions)).

Class has_count T :=
  { count_elems_T : forall min max : T, N }.

Class has_alloc T :=
  { alloc_T : forall min max : T, N -> list T }.

Class has_size T := size_T : T -> Q.

Definition adjust_time (t : Q) : Q
  := Qmax t smallest_time_Q.

Definition adjusted_size_T {T} {size : has_size T} (v : T) : Q
  := adjust_time (size v).

Class has_total_time T :=
  total_time_all_elems_T : forall min max : T, Q.

Definition adjusted_total_time_all_elems_T {T} {_ : has_total_time T} (min max : T) : Q
  := adjust_time (total_time_all_elems_T min max).

Definition op_from_to {T} (op : T -> T -> T) (id : T)
           (lower upper : Z) (f : Z -> T) : T
  := if (lower <=? upper)%Z
     then List.fold_right op
                          id
                          (List.map (fun x:nat => f (lower + x)%Z) (seq 0 (1 + Z.to_nat (upper - lower))))
     else id.

Definition Zprod_from_to (lower upper : Z) (f : Z -> Z) : Z
  := op_from_to Z.mul 1%Z lower upper f.
Definition Zsum_from_to (lower upper : Z) (f : Z -> Z) : Z
  := op_from_to Z.add 0%Z lower upper f.

Local Notation "'Π_{' x = lower '}^{' upper } f"
  := (Zprod_from_to lower upper (fun x => f))
       (x ident, at level 35) : Z_scope.
Local Notation "'∑_{' x = lower '}^{' upper } f"
  := (Zsum_from_to lower upper (fun x => f))
       (x ident, at level 35) : Z_scope.
Definition Qprod_from_to (lower upper : Z) (f : Z -> Q) : Q
  := op_from_to Qmult 1%Q lower upper f.
Definition Qsum_from_to (lower upper : Z) (f : Z -> Q) : Q
  := op_from_to Qplus 0%Q lower upper f.

Local Notation "'Π_{' x = lower '}^{' upper } f"
  := (Qprod_from_to lower upper (fun x => f))
       (x ident, at level 35) : Q_scope.
Local Notation "'∑_{' x = lower '}^{' upper } f"
  := (Qsum_from_to lower upper (fun x => f))
       (x ident, at level 35) : Q_scope.

Fixpoint group_by' {T} (eqb : T -> T -> bool) (ls : list T) (acc : list T) {struct ls}
  : list (list T)
  := match ls, acc with
     | [], [] => []
     | [], acc => [List.rev acc]
     | x::xs, [] => group_by' eqb xs [x]
     | x::xs, y::_ => if eqb x y
                      then group_by' eqb xs (x::acc)
                      else acc :: group_by' eqb xs [x]
     end.

Definition group_by {T} (eqb : T -> T -> bool) (ls : list T)
  := group_by' eqb ls [].

Definition Qsqrt_up (v : Q) : Q
  := Z.sqrt_up (Qnum v) # (Z.to_pos (Z.sqrt (Qden v))).
Definition Qsqrt_down (v : Q) : Q
  := Z.sqrt (Qnum v) # (Z.to_pos (Z.sqrt_up (Qden v))).

Fixpoint take_uniform_n' {T} (ls : list T) (len : nat) (n : nat) : list T
  := match n, ls, List.rev ls with
     | 0%nat, _, _ => []
     | _, [], _ => []
     | _, _, [] => []
     | 1%nat, x::_, _ => [x]
     | 2%nat, [x], _ => [x]
     | 2%nat, x::_, y::_ => [x; y]
     | S n', x::xs, _
       => let skip := Z.to_nat (Qfloor (1/2 + len / n - 1)) in
          x :: take_uniform_n' (skipn skip xs) (len - 1 - skip) n'
     end.

Definition take_uniform_n {T} ls n := @take_uniform_n' T ls (List.length ls) n.


Definition Qrange (min step max : Q) : list Q
  := if Qle_bool min max
     then List.map (fun n:nat => min + step * n)
                   (seq 0 (1 + Z.to_nat (Qfloor ((max - min) / step))))
     else [].

Definition Zrange (min : Z) (step : Q) (max : Z) : list Z
  := List.map Qround (Qrange min step max).

Definition Zrange_max_points (min max : Z) (max_points : N) : list Z
  := Zrange min (Qceiling (Qmax 1 ((max - min) / (max_points - 1)))) max.

Class integrable (f : Z -> Q) {fint : Z -> Q} := {}.

Definition polynomial := list (Q * Z) (* coef, exp *).

Definition degree (p : polynomial) : Z
  := match List.map (@snd _ _) (List.filter (fun '(coeff, _) => negb (Qeq_bool coeff 0)) p) with
     | [] => 0%Z
     | e :: rest
       => List.fold_right Z.max e rest
     end.

Definition poly_mul (p q : polynomial) : polynomial
  := List.flat_map
       (fun '(coeff, exp)
        => List.map
             (fun '(coeff', exp') => (coeff * coeff', (exp + exp')%Z))
             q)
       p.

Definition poly_add (p q : polynomial) : polynomial := p ++ q.

Definition poly_opp (p : polynomial) : polynomial
  := List.map (fun '(coeff, e) => (-coeff, e)) p.

Definition poly_sub (p q : polynomial) : polynomial := poly_add p (poly_opp q).

Definition poly_power (p : polynomial) (e : N) : polynomial
  := match e with
     | 0%N => [(1%Q, 0%Z)]
     | Npos e
       => pow_pos poly_mul p e
     end.

Definition eval_poly_gen {T}
           (add : T -> T -> T)
           (pow : T -> Z -> T)
           (sc_mul : Q -> T -> T)
           (zero : T)
           (p : polynomial) (x : T) : T
  := List.fold_right add zero
                     (List.map (fun '(coeff, exp) => sc_mul coeff (pow x exp)) p).

Definition eval_poly (p : polynomial) (x : Q) : Q
  := eval_poly_gen Qplus Qpower Qmult 0%Z p x.
Definition eval_poly_cfrac (p : polynomial) (x : Q) : Q
  := eval_poly_gen Qplus_cfrac Qpower_cfrac Qmult_cfrac 0%Z p x.
Definition compose_poly (f : polynomial) (x : polynomial) : polynomial
  := eval_poly_gen poly_add
                   (fun p e => poly_power p (Z.to_N e) (* UNSAFE!!! *))
                   (fun c p => poly_mul [(c, 0%Z)] p (* c * p *))
                   [] f x.

Definition integrate_poly (p : polynomial) : polynomial * Q (* logarithmic factor *)
  := (List.flat_map (fun '(coeff, exp) => if negb (exp =? -1)%Z
                                          then [(coeff / (exp + 1)%Z, (exp + 1)%Z)]
                                          else [])
                    p,
      List.fold_right
        (fun x y => x + y)%Q
        0%Q
        (List.map (fun '(coeff, exp) => if (exp =? -1)%Z then coeff else 0%Q) p)).
Definition diff_poly (p : polynomial) : polynomial
  := List.map (fun '(coeff, exp) => (coeff * (exp:Z), (exp - 1)%Z)) p.

Definition e_Q : Q := Eval compute in 2 + (7182818284590452353602874713526624977572470936999595749669676277 # (10^Pos.of_nat (String.length "7182818284590452353602874713526624977572470936999595749669676277"))).
Definition log2_e_Q : Q := Eval compute in 1 + 4426950408889634073599246810018921374266459541529859341354494069 # (10^Pos.of_nat (String.length "4426950408889634073599246810018921374266459541529859341354494069")).

Fixpoint fact (n : nat) : N
  := match n with
     | O => 1
     | S n' => n * fact n'
     end%N.

Definition fact0 : N := Eval compute in fact 0.
Definition fact1 : N := Eval compute in fact 1.
Definition fact2 : N := Eval compute in fact 2.
Definition fact3 : N := Eval compute in fact 3.
Definition fact4 : N := Eval compute in fact 4.
Definition fact5 : N := Eval compute in fact 5.
Definition fact6 : N := Eval compute in fact 6.
Definition fact7 : N := Eval compute in fact 7.

Fixpoint taylor_series_exp (deg : nat) : polynomial
  := match deg with
     | O => [(1, 0%Z)]
     | S deg'
       => ((1/fact deg), Z.of_nat deg) :: taylor_series_exp deg'
     end.

Definition taylor_series_exp_for_exp := Eval compute in taylor_series_exp 5.

Fixpoint taylor_series_ln1px (deg : nat) : polynomial
  := match deg with
     | O => []
     | S deg'
       => (((-1)^(deg'))%Z / deg, Z.of_nat deg) :: taylor_series_ln1px deg'
     end.

Definition taylor_series_ln1px_for_ln := Eval compute in taylor_series_ln1px 5.

Fixpoint taylor_series_1pxpow (exp : Q) (deg : nat) : polynomial
  := match deg with
     | O => [(1, 0%Z)]
     | S deg'
       => let '(s, t) := (Qnum exp, Qden exp) in
          let n := deg in
          ((Π_{ k = 0 }^{ n - 1 } (s - k * t)) / (fact n * t^n)%Z,
           Z.of_nat n)
            :: taylor_series_1pxpow exp deg'
     end.

Local Arguments Pos.to_nat !_ / .

Definition taylor_series_1pxpow_for_pow (exp : Q)
  := Eval cbn [taylor_series_1pxpow fact N.mul N.of_nat Pos.of_succ_nat Pos.succ Pos.mul Pos.add Z.of_nat] in taylor_series_1pxpow exp 5.

Definition Qlog2_up (x : Q) : Z
  := (Z.log2_up (Qnum x) - Z.log2 (Qden x))%Z.
Definition Qlog2 (x : Q) : Z
  := (Z.log2 (Qnum x) - Z.log2_up (Qden x))%Z.

Definition Qln (x : Q) : Q
  := (* let x = 2^k * (1+q), so that either k:=log2_up(x) or k:=log2(x) and q:=x/2^k-1; then ln(x) = k/log2(e) + ln(1+q) *)
    let k := if Qle_bool ((2^Qlog2_up x)%Z - x) (x - (2^Qlog2 x)%Z)
             then Qlog2_up x
             else Qlog2 x in
    let q := x / (2^k)%Z - 1 in
    k / log2_e_Q + if Qeq_bool q 0 then 0 else eval_poly taylor_series_ln1px_for_ln q.

Definition Qln_cfrac (x : Q) : Q
  := (* let x = 2^k * (1+q), so that either k:=log2_up(x) or k:=log2(x) and q:=x/2^k-1; then ln(x) = k/log2(e) + ln(1+q) *)
    let k := if Qle_bool ((2^Qlog2_up x)%Z - x) (x - (2^Qlog2 x)%Z)
             then Qlog2_up x
             else Qlog2 x in
    let q := x / (2^k)%Z - 1 in
    Qround_cfrac (k / log2_e_Q + if Qeq_bool q 0 then 0 else eval_poly_cfrac taylor_series_ln1px_for_ln q).

Definition Qexp (x : Q) : Q
  := let (int_part, rest)
         := if Qle_bool (x - Qfloor x) (Qceiling x - x)
            then (Qfloor x, x - Qfloor x)
            else (Qceiling x, x - Qceiling x) in
     Qpower e_Q int_part
     * if Qeq_bool rest 0 then 1 else eval_poly taylor_series_exp_for_exp rest.

Definition Qpow' (x : Q) (k : Q)
  := let (int_part, rest)
         := if Qle_bool (k - Qfloor k) (Qceiling k - k)
            then (Qfloor k, k - Qfloor k)
            else (Qceiling k, k - Qceiling k) in
     Qred (Qpower x int_part)
     * (* x^k = exp(ln(x^k)) = exp(k ln x) *)
     Qexp (rest * Qln x).

Definition Qroot_of_Qroot_up_down (e : positive) (Qroot_up : Q -> Q) (Qroot_down : Q -> Q)
           (x : Q) : Q
  := if Qle_bool 0 x
     then let vu := Qroot_up x in
          let vd := Qroot_down x in
          let v := if Qle_bool (x - Qpower vd e) (Qpower vu e - x) then vd else vu in
          (* x^(1/e) = v(1 + (x - v^e)/v^e)^(1/e) *)
          v * eval_poly (taylor_series_1pxpow_for_pow (1#e)) (x / Qpower v e - 1)
     else Qpow' x (1#e).

Definition Qsqrt (x : Q)
  := Qroot_of_Qroot_up_down
       2
       (fun x => (Z.sqrt_up (Qnum x)) # (Pos.sqrt (Qden x)))
       (fun x => (Z.sqrt (Qnum x)) # (Z.to_pos (Z.sqrt_up (Qden x))))
       x.

Ltac reify_to_poly fx x :=
  let fx := (eval cbv beta in fx) in
  let orig := fx in
  let rec_binop binop fx gx :=
      let fp := reify_to_poly fx x in
      let gp := reify_to_poly gx x in
      constr:(binop fp gp) in
  let rec_unop unop fx :=
      let fp := reify_to_poly fx x in
      constr:(unop fp) in
  lazymatch fx with
  | x => constr:([(1%Q, 1%Z)])
  | context[x]
    => lazymatch fx with
       | Qplus ?fx ?gx => rec_binop poly_add fx gx
       | Z.add ?fx ?gx => rec_binop poly_add fx gx
       | N.add ?fx ?gx => rec_binop poly_add fx gx
       | Nat.add ?fx ?gx => rec_binop poly_add fx gx
       | Qminus ?fx ?gx => rec_binop poly_sub fx gx
       | Z.sub ?fx ?gx => rec_binop poly_sub fx gx
       | N.sub ?fx ?gx => rec_binop poly_sub fx gx
       | Nat.sub ?fx ?gx => rec_binop poly_sub fx gx
       | Qmult ?fx ?gx => rec_binop poly_mul fx gx
       | Z.mul ?fx ?gx => rec_binop poly_mul fx gx
       | N.mul ?fx ?gx => rec_binop poly_mul fx gx
       | Nat.mul ?fx ?gx => rec_binop poly_mul fx gx
       | Qdiv ?fx ?gx => reify_to_poly (fx * / gx) x
       | Qpower ?fx ?gx
         => lazymatch gx with
            | context[x] => idtac "non-constant exponent" gx "in" x "(" orig;
                            fail 0 "non-constant exponent" gx "in" x "(" orig
            | _ => let fp := reify_to_poly fx x in
                   constr:(poly_power fp (Z.to_N gx))
            end
       | Z.pow ?fx ?gx => reify_to_poly (Qpower (inject_Z fx) gx) x
       | N.pow ?fx ?gx
         => lazymatch gx with
            | context[x] => idtac "non-constant exponent" gx "in" x "(" orig;
                            fail 0 "non-constant exponent" gx "in" x "(" orig
            | _ => let fp := reify_to_poly fx x in
                   constr:(poly_power fp gx)
            end
       | Nat.pow ?fx ?gx => reify_to_poly (N.pow (N.of_nat fx) (N.of_nat gx)) x
       | / / ?fx => reify_to_poly fx x
       | / (?fx * ?gx) => reify_to_poly (/ fx * / gx) x
       | Qexp ?fx
         => let fp := reify_to_poly fx x in
            constr:(compose_poly taylor_series_exp_for_exp fp)
       | Qln ?fx
         => let fp := reify_to_poly (Qminus fx 1) x in
            constr:(compose_poly taylor_series_ln1px_for_ln fp)
       | inject_Z ?fx => reify_to_poly fx x
       | Z.to_nat ?fx => reify_to_poly fx x
       | Z.of_nat ?fx => reify_to_poly fx x
       | Z.of_N ?fx => reify_to_poly fx x
       | Z.to_N ?fx => reify_to_poly fx x
       | N.to_nat ?fx => reify_to_poly fx x
       | N.of_nat ?fx => reify_to_poly fx x
       | ?v => idtac "unrecognized:" v;
               fail 0 "unrecognized:" v
       end
  | _ => let fx := lazymatch type of fx with
                   | Q => fx
                   | Z => constr:(inject_Z fx)
                   | N => constr:(inject_Z (Z.of_N fx))
                   | nat => constr:(inject_Z (Z.of_nat fx))
                   | _ => constr:(fx : Q)
                   end in
         constr:([(fx, 0%Z)])
  end.

Class reified (f : Z -> Q) := reify : polynomial.
Arguments reify _ {_}.

Class factors_through_prod {T} (f : N * N -> T) :=
  { factor_through_prod : N -> T
    ; factor_correctness : forall x, f x = factor_through_prod (fst x * snd x)%N }.
Arguments factor_through_prod {T} f {_}.

#[global] Hint Unfold id : solve_factors_through_prod.

Ltac subst_context_vars f :=
  let run := match goal with
             | [ x := _ |- _ ]
               => match f with
                  | context[x]
                    => let f := (eval cbv [x] in f) in
                       fun k => k f
                  end
             | _ => fun k => f
             end in
  run ltac:(fun f => subst_context_vars f).

Ltac reify_poly f :=
  let x := fresh "x" in
  let f := subst_context_vars f in
  let f := (eval cbv [factor_through_prod has_size] in f) in
  lazymatch constr:(fun x : Z => ltac:(let r := reify_to_poly (f x) x in exact r)) with
  | fun _ => ?v => v
  | ?v => idtac "failed to eliminate functional dependencies of" v;
          fail 0 "failed to eliminate functional dependencies of" v
  end.

Ltac solve_factors_through_prod :=
  lazymatch goal with
  | [ |- factors_through_prod _ ]
    => repeat match goal with
              | [ H := _ |- _ ] => subst H
              end;
       autounfold with solve_factors_through_prod;
       econstructor;
       let x1 := fresh in
       let x2 := fresh in
       intros [x1 x2];
       cbn [fst snd];
       let ev := fresh "ev" in
       match goal with
       | [ |- context[?e] ] => is_evar e; set (ev := e)
       end;
       repeat match goal with
              | [ |- context[N.mul x2 x1] ] => rewrite (N.mul_comm x2 x1)
              | [ |- context[Nat.mul (N.to_nat ?x) (N.to_nat ?y)] ] => rewrite <- !(N2Nat.inj_mul x y)
              | [ |- context[Z.mul (Z.of_N ?x) (Z.of_N ?y)] ] => rewrite <- !(N2Z.inj_mul x y)
              | [ |- context[Z.mul (Z.of_nat ?x) (Z.of_nat ?y)] ] => rewrite <- !(Nat2Z.inj_mul x y)
              | [ |- context[Qmult (inject_Z ?x) (inject_Z ?y)] ] => rewrite <- !(inject_Z_mult x y)
              end;
       let ev := (eval cbv [ev] in ev) in
       lazymatch goal with
       | [ |- ?f = _ ]
         => lazymatch (eval pattern (N.mul x1 x2) in f) with
            | ?f _
              => let __ := constr:(eq_refl : ev = f) in
                 reflexivity
            end
       end
  end.

Definition total_time_of_N_prod_exact
         {size : has_size (N * N)}
  : has_total_time (N * N)
  := fun min max
     => let min := (fst min * snd min)%N in
        let max := (fst max * snd max)%N in
        (* ∑_{i=1}^max ∑_{j=⌈min/i⌉}^{⌊max/i⌋} 1*)
        ∑_{i=1}^{max} (∑_{j=Qceiling (min/i)}^{Qfloor (max/i)} (adjusted_size_T (Z.to_N i, Z.to_N j))).

Definition cutoff := 50%N.

Definition small_table (* the [n]th element is the number of ways there are to write [n] as a product of two things *)
  := Eval native_compute in
      List.map
        (fun n:nat
         => (n:N, ∑_{i=1}^{n} if (n mod i =? 0) then 1 else 0)%Z)
        (seq 0 (Z.to_nat (1 + cutoff))).

#[global] Hint Extern 0 (reified ?f) => let v := reify_poly f in exact v : typeclass_instances.

#[global] Hint Extern 0 (factors_through_prod _) => solve_factors_through_prod : typeclass_instances.
#[global] Hint Extern 0 => progress unfold factor_through_prod : typeclass_instances.

Global Instance nat_has_double_avg : has_double_avg nat
  := { double_T := Nat.mul 2 ; avg_T x y := ((x + y) / 2)%nat }.

Global Instance N_has_double_avg : has_double_avg N
  := { double_T := N.mul 2 ; avg_T x y := ((x + y) / 2)%N }.

Global Instance Z_has_double_avg : has_double_avg Z
  := { double_T := Z.mul 2 ; avg_T x y := ((x + y) / 2)%Z }.

Global Instance nat_has_min : has_min nat := Nat.min.
Global Instance N_has_min : has_min N := N.min.
Global Instance Z_has_min : has_min Z := Z.min.

Global Instance nat_has_leb : has_leb nat := Nat.leb.
Global Instance N_has_leb : has_leb N := N.leb.
Global Instance Z_has_leb : has_leb Z := Z.leb.

Global Instance Q_has_alloc : has_alloc Q
  := { alloc_T min max n
       := let step := (max - min) / (n - 1) in
          List.map (fun i:nat => min + i * step) (seq 0 (N.to_nat n)) }.

Global Instance Z_has_count : has_count Z
  := { count_elems_T min max
       := Z.to_N (1 + max - min) }.

Global Instance N_has_count : has_count N
  := { count_elems_T min max := count_elems_T (min:Z) (max:Z) }.

Global Instance nat_has_count : has_count nat
  := { count_elems_T min max := count_elems_T (min:N) (max:N) }.

Global Instance Z_has_alloc : has_alloc Z
  := { alloc_T min max n
       := List.map (fun v:Q => Qfloor (1/2 + v)) (alloc_T (min:Q) (max:Q) n) }.

Global Instance N_has_alloc : has_alloc N
  := { alloc_T min max n := List.map Z.to_N (alloc_T (min:Z) (max:Z) n) }.

Global Instance nat_has_alloc : has_alloc nat
  := { alloc_T min max n := List.map N.to_nat (alloc_T (min:N) (max:N) n) }.

Definition Z_prod_count_exact (min max : Z * Z) : N
  := (let min := fst min * snd min in
      let max := fst max * snd max in
      (*∑_{i=1}^max ∑_{j=min/i}^{max/i} 1*)
      (*∑_{i=1}^max 1 + ⌊max/i⌋-⌈min/i⌉ *)
      Z.to_N (∑_{i=1}^{max} (1 + Qfloor (max/i) + Qceiling (min/i))))%Z.

Definition EulerMascheroni_γ : Q := 0 + 5772156649015328606065120900824024310421593359399235988057672348 # (10^Pos.of_nat (String.length "5772156649015328606065120900824024310421593359399235988057672348")).

Global Instance Z_prod_has_count : has_count (Z * Z)
  := { count_elems_T min max
       := (let minv := fst min * snd min in
           let maxv := fst max * snd max in
           (*∑_{i=1}^max ∑_{j=min/i}^{max/i} 1*)
           (*∑_{i=1}^max 1 + ⌊max/i⌋-⌈min/i⌉ *)
           (* For large differences, this is approximately *)
           (* max + (max - min) ∑_{i=1}^max 1/i ≈ max + (max - min) (ln(max) + γ), c.f. https://mathworld.wolfram.com/HarmonicNumber.html *)
           if (maxv - minv <=? cutoff)%Z
           then Z_prod_count_exact min max
           else
             Z.to_N (maxv + Qfloor (1/2 + (maxv - minv) * (Qln maxv + EulerMascheroni_γ))))%Z }.

Global Instance N_prod_has_count : has_count (N * N)
  := { count_elems_T '(x1, x2) '(y1, y2) := count_elems_T (x1:Z, x2:Z) (y1:Z, y2:Z) }.

Global Instance nat_prod_has_count : has_count (nat * nat)
  := { count_elems_T '(x1, x2) '(y1, y2) := count_elems_T (x1:N, x2:N) (y1:N, y2:N) }.

Local Instance Z_prod_has_alloc : has_alloc (Z * Z)
  := { alloc_T min max n
       := match n with
          | 0%N => []
          | 1%N => [max]
          | 2%N => [min; max]
          | _
            => (let min := fst min * snd min in
                let max := fst max * snd max in
                (if min <=? 5
                 then
                   List.filter (fun '(x, y) => x*y <=? max) [(1, 1); (1, 2); (2, 1); (1, 3); (3, 1); (1, 4); (2, 2); (4, 1); (1, 5); (5, 1)]
                 else
                   nil)
                  ++ let min := Z.max min 6 in
                     let max := Z.max max 6 in
                     if max - min <=? (n+1)/3
                     then
                       List.flat_map
                         (fun vals:list Z
                          => match vals with
                             | v::_
                               => let n := List.length vals in
                                  (*∑_{i=1}^max ∑_{j=⌈min/i⌉}^{⌊max/i⌋} 1*)
                                  take_uniform_n
                                    (List.flat_map
                                       (fun i:Z
                                        => List.map
                                             (fun j:Z => (i, j))
                                             (Zrange (Qceiling (v/i)) 1 (Qfloor (v/i))))
                                       (Zrange 1 1 v))
                                    (3*n)
                             | [] => []
                             end)
                         (tl (group_by Z.eqb (alloc_T min max (1 + (n+1)/3))))
                     else
                       List.flat_map
                         (fun v
                          => let mid := (Z.sqrt v, Z.sqrt_up v) in
                             let midv := fst mid * snd mid in
                             if midv <? v
                             then [mid; (1, v); (v, 1)]
                             else if midv =? v
                                  then [(1, v); mid; (v, 1)]
                                  else [(1, v); (v, 1); mid])
                         (tl (alloc_T min max (1 + (n+1)/3))))%Z
          end }.

Local Instance N_prod_has_alloc : has_alloc (N * N)
  := { alloc_T '(x1, x2) '(y1, y2) n
       := List.map (fun '(x, y) => (Z.to_N x, Z.to_N y)) (alloc_T (x1:Z, x2:Z) (y1:Z, y2:Z) n) }.
Local Instance nat_prod_has_alloc : has_alloc (nat * nat)
  := { alloc_T '(x1, x2) '(y1, y2) n
       := List.map (fun '(x, y) => (N.to_nat x, N.to_nat y)) (alloc_T (x1:N, x2:N) (y1:N, y2:N) n) }.

(** Work around COQBUG(https://github.com/coq/coq/issues/13239) *)
Definition total_time_of_Zpoly
       {size : has_size Z}
       {p : reified size}
  : has_total_time Z
  := fun min max
     => let '(p_int, ln_coef) := integrate_poly p in
        let f_int := if Qeq_bool ln_coef 0
                     then fun x => eval_poly_cfrac p_int x
                     else fun x => Qround_cfrac (eval_poly_cfrac p_int x + ln_coef * Qln_cfrac x) in
        if (max - min <=? 25)%Z
        then ∑_{i=min}^{max} (size i)
        else f_int max - f_int min.
#[global] Hint Extern 0 (has_total_time Z) => simple eapply @total_time_of_Zpoly : typeclass_instances.

Definition total_time_of_Npoly
       {size : has_size N}
       {p : reified (fun x => size (Z.to_N x))}
  : has_total_time N
  := fun min max => @total_time_of_Zpoly _ p min max.
#[global] Hint Extern 0 (has_total_time N) => simple eapply @total_time_of_Npoly : typeclass_instances.

Definition total_time_of_nat_poly
       {size : has_size nat}
       {p : reified (fun x => size (N.to_nat (Z.to_N x)))}
  : has_total_time nat
  := fun min max => @total_time_of_Zpoly _ p min max.
#[global] Hint Extern 0 (has_total_time nat) => simple eapply @total_time_of_nat_poly : typeclass_instances.

Fixpoint make_cumulants'
         {T} (add : T -> T -> T) (acc : T) (ls : list T)
  : list T
  := match ls with
     | [] => []
     | x :: xs
       => let acc := add acc x in
          acc :: make_cumulants' add acc xs
     end.

Definition make_cumulants {T} (add : T -> T -> T) (ls : list T) : list T
  := match ls with
     | [] => []
     | x :: xs => x :: make_cumulants' add x xs
     end.

(** Element [n] holds the sum of the times from element [n] of [small_table] up through the end *)
Definition small_table_rev_cached
           {size : has_size (N * N)}
  : list Q
  := List.rev
       (List.map
          Qred
          (make_cumulants
             Qplus
             (List.rev
                (List.map
                   (fun '((i, count) : N*Z) => count * (adjusted_size_T (1, i)%N))
                   small_table)))).

(** Get the total time from [minv] to the end of the table *)
Definition total_time_of_cached_table
           (cached_table : list Q)
  : forall (minv : nat), Q
  := fun minv => nth_default 0%Q cached_table minv.

Definition total_time_of_N_prod_poly_cached
       {size : has_size (N * N)}
       {_ : factors_through_prod size}
       {p : reified (fun x:Z => factor_through_prod size (Z.to_N x))}
       (cached_table : list Q)
  : has_total_time (N * N)
  := fun min max
     => (* If we look at all the products up to [V], we are approximately integrating under the curve [x y = V], so we have ∫_1^V (V/x) dx = V ln(V) *)
       (* Hence the number of ways to write [V] as a product is roughly V (ln(V)-ln(V-1)) ≈ V(ln(V+1) - ln(V)) = V ln(1 + 1/V) *)
       (* So we want to compute ∫ p(x) x ln(1+1/x) dx, which we do by taylor expansion *)
       let deg_series := Nat.max 5 (Z.to_nat (degree p)) in
       let p' := poly_mul p (poly_mul [(1%Q, 1%Z)] (compose_poly (taylor_series_ln1px deg_series) [(1%Q, (-1)%Z)])) (* p * x * (series(ln(1+k),k))(k:=1/x); N.B. We don't hit the UNSAFE case of [compose_poly] because [taylor_series_ln1px] has only non-negative exponents *) in
       let '(p_int, ln_coef) := integrate_poly p' in
       let f_int := if Qeq_bool ln_coef 0
                    then fun x => eval_poly_cfrac p_int x
                    else fun x => eval_poly_cfrac p_int x + ln_coef * Qln_cfrac x in
       let minv := (fst min * snd min)%N in
       let maxv := (fst max * snd max)%N in
       if (maxv - minv <=? cutoff)%N
       then
         @total_time_of_N_prod_exact size min max
       else
         if (minv <=? cutoff)%N
         then (* compute the exact of the first ones *)
           total_time_of_cached_table cached_table minv
           (* same as:
                 List.fold_right
                   (fun x y => Qred (Qplus x y)) (* Qred here for speed; empirically this seems to be the best place to put it *)
                   0
                   (List.map
                      (fun '((i, count) : N*Z) => count * (adjusted_size_T (1, i)%N))
                      (skipn (Z.to_nat minv) small_table))
            *)
           + adjust_time (f_int maxv - f_int cutoff)
         else
           adjust_time (f_int maxv - f_int minv).
Definition total_time_of_N_prod_poly
       {size : has_size (N * N)}
       {_ : factors_through_prod size}
       {p : reified (fun x:Z => factor_through_prod size (Z.to_N x))}
  : has_total_time (N * N)
  := dlet cached_table := small_table_rev_cached in total_time_of_N_prod_poly_cached cached_table.
#[global] Hint Extern 0 (has_total_time (N * N)) => simple eapply @total_time_of_N_prod_poly : typeclass_instances.

Definition total_time_of_Z_prod_poly_cached
       {size : has_size (Z * Z)}
       (size' := fun '((x, y) : N*N) => size (x:Z, y:Z))
       {_ : factors_through_prod size'}
       {p : reified (fun x => factor_through_prod size' (Z.to_N x))}
       (cached_table : list Q)
  : has_total_time (Z * Z)
  := fun '(x1, x2) '(y1, y2) => @total_time_of_N_prod_poly_cached _ _ p cached_table (Z.to_N x1, Z.to_N x2) (Z.to_N y1, Z.to_N y2).
Definition total_time_of_Z_prod_poly
       {size : has_size (Z * Z)}
       (size' := fun '((x, y) : N*N) => size (x:Z, y:Z))
       {_ : factors_through_prod size'}
       {p : reified (fun x => factor_through_prod size' (Z.to_N x))}
  : has_total_time (Z * Z)
  := dlet cached_table := @small_table_rev_cached size' in total_time_of_Z_prod_poly_cached cached_table.
#[global] Hint Extern 0 (has_total_time (Z * Z)) => simple eapply @total_time_of_Z_prod_poly : typeclass_instances.

Definition total_time_of_nat_prod_poly_cached
       {size : has_size (nat * nat)}
       (size' := fun '((x, y) : N*N) => size (x:nat, y:nat))
       {_ : factors_through_prod size'}
       {p : reified (fun x => factor_through_prod size' (Z.to_nat x))}
       (cached_table : list Q)
  : has_total_time (nat * nat)
  := fun '(x1, x2) '(y1, y2) => @total_time_of_N_prod_poly_cached size' _ p cached_table (x1:N, x2:N) (y1:N, y2:N).
Definition total_time_of_nat_prod_poly
       {size : has_size (nat * nat)}
       (size' := fun '((x, y) : N*N) => size (x:nat, y:nat))
       {_ : factors_through_prod size'}
       {p : reified (fun x => factor_through_prod size' (Z.to_nat x))}
  : has_total_time (nat * nat)
  := dlet cached_table := @small_table_rev_cached size' in total_time_of_nat_prod_poly_cached cached_table.
#[global] Hint Extern 0 (has_total_time (nat * nat)) => simple eapply @total_time_of_nat_prod_poly : typeclass_instances.

Class with_assum {T} (v : T) (T' : Type) := val : T'.

#[global] Hint Extern 0 (@with_assum ?T ?v ?T') => pose (v : T); change T' : typeclass_instances.

Class has_compress {A B} := compress_T : A -> B.
Global Arguments has_compress : clear implicits.

Class has_make {A B} {HC : has_compress A B} :=
  { make_T : B -> A
    ; make_T_correct : forall v, compress_T (make_T v) = v }.
Global Arguments has_make A B {_}.

Global Hint Mode has_double_avg + : typeclass_instances.
Global Hint Mode has_leb + : typeclass_instances.
Global Hint Mode has_min + : typeclass_instances.

Global Instance has_double_avg_of_make
       {A B}
       {_ : has_compress A B} {_ : has_make A B}
       {_ : has_double_avg B}
  : has_double_avg A
  := { double_T x := make_T (double_T (compress_T x))
       ; avg_T x y := make_T (avg_T (compress_T x) (compress_T y)) }.

Global Instance has_leb_of_compress
       {A B} {_ : has_compress A B}
       {leb : has_leb B}
  : has_leb A
  := fun x y => leb (compress_T x) (compress_T y).

Definition generate_inputs
           {T} {_ : has_double_avg T} (*{_ : has_count T}*) {_ : has_alloc T} (*{_ : has_min T}*)
           (init : T)
           (size : has_size T)
           (*{HTT : with_assum size (has_total_time T)}
           (HTT' : has_total_time T := HTT)*)
           (allocation : Q)
           (max_size : Q)
           (max_points : N)
           (max_input : option T)
  : list T
  := let max_size := Qmin max_size (allocation / cutoff_elem_count) in
     let use_max_input := option_map (fun max_input => Qle_bool (size max_input) max_size) max_input in
     let max
         := match max_input, use_max_input with
            | Some max_input, Some true
              => max_input
            | _, _ => find_max double_T avg_T size max_size init
            end in
     (*let noop 'tt := binary_alloc adjusted_size_T count_elems_T adjusted_total_time_all_elems_T allocation init max cutoff_elem_count max_points min_fractional_change_for_nonlinear_sample alloc_T in*)
     piecewise_uniform_alloc adjusted_size_T allocation init max cutoff_elem_count max_points alloc_T.
