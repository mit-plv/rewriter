Require Import Coq.QArith.QArith.
Require Import Coq.Structures.Orders.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Mergesort.
Require Export Coq.Lists.List.
Require Export Coq.ZArith.ZArith.
Export ListNotations.

Global Set Printing Width 1000.
Global Open Scope Z_scope.
Global Open Scope nat_scope.
Global Open Scope list_scope.

(** divisions should be roughly:
- The [Sanity] tests should be just enough to ensure that the code compiles and runs.
- All [SuperFast] tests in a file should finish in under 10 seconds total
- The [Fast] test files should take about a minute each
- The [Medium] tests should go up to about a minute each
- The [Slow] tests should go up to about 10 minutes each
- The [VerySlow] tests may take longer than 10 minutes each *)

Inductive size := Sanity | SuperFast | Fast | Medium | Slow | VerySlow.

Definition seconds_of_size (sz : size) : nat
  := match sz with
     | Sanity => 1
     | SuperFast => 10
     | Fast => 120
     | Medium => 600
     | Slow => 3600
     | VerySlow => 3600 * 10
     end.

Notation "'subst!' x 'for' y 'in' f"
  := (match x return _ with y => f end) (only parsing, at level 200, x at level 200, y ident, f at level 200).

Notation "'eta_size' ( sz' => f ) sz"
  := match sz with
     | Sanity => subst! Sanity for sz' in f
     | SuperFast => subst! SuperFast for sz' in f
     | Fast => subst! Fast for sz' in f
     | Medium => subst! Medium for sz' in f
     | Slow => subst! Slow for sz' in f
     | VerySlow => subst! VerySlow for sz' in f
     end (only parsing, at level 70, sz' ident).

Local Lemma eta_size_sanity : forall T f k, eta_size (k => f k) k = f k :> T.
Proof. intros; repeat match goal with |- context[match ?e with _ => _ end] => destruct e end; reflexivity. Qed.

Definition Zseconds_of_size (sz : size) : Z
  := Z.of_nat (seconds_of_size sz).

Definition Qseconds_of_size (sz : size) : Q
  := inject_Z (Zseconds_of_size sz).

Definition standard_max_seconds_of_size (sz : size) : nat
  := match sz with
     | Sanity => 10
     | SuperFast => 10
     | Fast => 10
     | Medium => 60
     | Slow => 60
     | VerySlow => 60
     end%nat.
Definition Zstandard_max_seconds_of_size (sz : size) : Z
  := Z.of_nat (standard_max_seconds_of_size sz).
Definition Qstandard_max_seconds_of_size (sz : size) : Q
  := inject_Z (Zstandard_max_seconds_of_size sz).

Definition standard_max_seconds : nat := standard_max_seconds_of_size Fast.
Definition Zstandard_max_seconds : Z := Z.of_nat standard_max_seconds.
Definition Qstandard_max_seconds : Q := inject_Z Zstandard_max_seconds.

Definition nat_of_size (sz : size) : nat
  := match sz with
     | Sanity => 0
     | SuperFast => 1
     | Fast => 2
     | Medium => 3
     | Slow => 4
     | VerySlow => 5
     end%nat.

Definition smaller_sizes (sz : size) : list size
  := match sz with
     | Sanity => []
     | SuperFast => [Sanity]
     | Fast => [Sanity; SuperFast]
     | Medium => [Sanity; SuperFast; Fast]
     | Slow => [Sanity; SuperFast; Fast; Medium]
     | VerySlow => [Sanity; SuperFast; Fast; Medium; Slow]
     end.

Definition size_pred (sz : size) : option size
  := match sz with
     | Sanity => None
     | SuperFast => Some Sanity
     | Fast => Some SuperFast
     | Medium => Some Fast
     | Slow => Some Medium
     | VerySlow => Some Slow
     end.

Fixpoint uniquify {T} (T_beq : T -> T -> bool) (ls : list T) : list T
  := match ls with
     | nil => nil
     | cons x xs
       => x :: filter (fun y => negb (T_beq x y)) (uniquify T_beq xs)
     end.

Definition remove_smaller_args_of_size {T} (T_beq : T -> T -> bool) (sz : size)
           (args_of_size : size -> list T)
  : list T
  := let args := uniquify T_beq (args_of_size sz) in
     let smaller_args := flat_map args_of_size (smaller_sizes sz) in
     filter (fun v => negb (existsb (T_beq v) smaller_args)) args.

Module NatProdOrder <: TotalLeBool.
  Definition t := (nat * nat)%type.
  Definition t_to_Z (v : t) : Z := (Z.of_nat (fst v) * Z.of_nat (snd v))%Z.
  Definition ltb (x y : t) : bool
    := (t_to_Z x <? t_to_Z y)%Z
       || (((t_to_Z x =? t_to_Z y)%Z)
             && ((fst x <? fst y)
                 || ((fst x =? fst y) && (snd x <? snd y)))).
  Definition leb (x y : t) : bool
    := ltb x y || ((fst x =? fst y) && (snd x =? snd y)).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Nat.eqb_eq
                 | rewrite !Z.eqb_eq
                 | rewrite !Z.ltb_lt
                 | rewrite !Nat.ltb_lt ].
    destruct (Z.lt_total (t_to_Z a1) (t_to_Z a2)) as [?|[?|?]];
      try solve [ auto ]; [].
    destruct (Nat.lt_total (fst a1) (fst a2)) as [?|[?|?]];
      try solve [ auto 6 ]; [].
    destruct (Nat.lt_total (snd a1) (snd a2)) as [?|[?|?]];
      solve [ auto 7 ].
  Qed.
End NatProdOrder.

Module NatProdSort := Sort NatProdOrder.
Notation sort_by_prod := NatProdSort.sort.

Module NatFstOrder <: TotalLeBool.
  Definition t := (nat * nat)%type.
  Definition ltb (x y : t) : bool
    := (fst x <? fst y)
       || ((fst x =? fst y)
             && (snd x <? snd y)).
  Definition leb (x y : t) : bool
    := ltb x y || ((fst x =? fst y) && (snd x =? snd y)).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Nat.eqb_eq
                 | rewrite !Nat.ltb_lt ].
    destruct (Nat.lt_total (fst a1) (fst a2)) as [?|[?|?]];
      try solve [ auto 6 ]; [].
    destruct (Nat.lt_total (snd a1) (snd a2)) as [?|[?|?]];
      solve [ auto 7 ].
  Qed.
End NatFstOrder.

Module NatFstSort := Sort NatFstOrder.
Notation sort_by_fst := NatFstSort.sort.

Module ZProdOrder <: TotalLeBool.
  Local Open Scope Z_scope.
  Definition t := (Z * Z)%type.
  Definition t_to_Z (v : t) : Z := (fst v * snd v)%Z.
  Definition ltb (x y : t) : bool
    := (t_to_Z x <? t_to_Z y)%Z
       || (((t_to_Z x =? t_to_Z y)%Z)
             && ((fst x <? fst y)
                 || ((fst x =? fst y) && (snd x <? snd y)))).
  Definition leb (x y : t) : bool
    := ltb x y || ((fst x =? fst y) && (snd x =? snd y)).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Z.eqb_eq
                 | rewrite !Z.ltb_lt
                 | rewrite !Z.ltb_lt ].
    destruct (Z.lt_total (t_to_Z a1) (t_to_Z a2)) as [?|[?|?]];
      try solve [ auto ]; [].
    destruct (Z.lt_total (fst a1) (fst a2)) as [?|[?|?]];
      try solve [ auto 6 ]; [].
    destruct (Z.lt_total (snd a1) (snd a2)) as [?|[?|?]];
      solve [ auto 7 ].
  Qed.
End ZProdOrder.

Module ZProdSort := Sort ZProdOrder.
Notation Zsort_by_prod := ZProdSort.sort.

Module ZFstOrder <: TotalLeBool.
  Local Open Scope Z_scope.
  Definition t := (Z * Z)%type.
  Definition ltb (x y : t) : bool
    := (fst x <? fst y)
       || ((fst x =? fst y)
             && (snd x <? snd y)).
  Definition leb (x y : t) : bool
    := ltb x y || ((fst x =? fst y) && (snd x =? snd y)).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Z.eqb_eq
                 | rewrite !Z.ltb_lt ].
    destruct (Z.lt_total (fst a1) (fst a2)) as [?|[?|?]];
      try solve [ auto 6 ]; [].
    destruct (Z.lt_total (snd a1) (snd a2)) as [?|[?|?]];
      solve [ auto 7 ].
  Qed.
End ZFstOrder.

Module ZFstSort := Sort ZFstOrder.
Notation Zsort_by_fst := ZFstSort.sort.


Module ZOrder <: TotalLeBool.
  Local Open Scope Z_scope.
  Definition t := Z.
  Definition ltb := Z.ltb.
  Definition leb := Z.leb.
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Z.eqb_eq
                 | rewrite !Z.ltb_lt
                 | rewrite !Z.leb_le ].
    lia.
  Qed.
End ZOrder.

Module ZSort := Sort ZOrder.

Module Import LocalReflect.
  Definition reflect := reflect. (* a local copy *)
  Existing Class reflect.
  Notation reflect_rel R1 R2 := (forall x y, reflect (R1 x y) (R2 x y)).
End LocalReflect.
Global Hint Opaque reflect : typeclass_instances.

Lemma reflect_of_beq {beq : bool} {R : Prop}
      (bp : beq = true -> R)
      (pb : R -> beq = true)
  : reflect R beq.
Proof.
  destruct beq; constructor; intuition (discriminate || auto).
Qed.

Definition reflect_rel_of_beq {T} {beq : T -> T -> bool} {R : T -> T -> Prop}
      (bp : forall x y, beq x y = true -> R x y)
      (pb : forall x y, R x y -> beq x y = true)
  : reflect_rel R beq
  := fun x y => reflect_of_beq (bp x y) (pb x y).

Definition reflect_rel_of_beq_iff {T} {beq : T -> T -> bool} {R : T -> T -> Prop}
      (bp : forall x y, beq x y = true <-> R x y)
  : reflect_rel R beq
  := reflect_rel_of_beq (fun x y => proj1 (bp x y)) (fun x y => proj2 (bp x y)).

Definition reflect_rel_to_beq_iff {T} {beq : T -> T -> bool} {R : T -> T -> Prop}
           (Hr : reflect_rel R beq)
  : forall x y, beq x y = true <-> R x y.
Proof.
  intros x y; specialize (Hr x y); destruct Hr; intuition (eauto; congruence).
Qed.

Global Instance reflect_eq_nat : reflect_rel (@eq nat) Nat.eqb
  := reflect_rel_of_beq_iff Nat.eqb_eq.

Global Instance reflect_eq_Z : reflect_rel (@eq Z) Z.eqb
  := reflect_rel_of_beq_iff Z.eqb_eq.

Local Set Implicit Arguments.
Scheme Equality for prod.

Definition prod_beq_iff {A B eqA eqB}
           (A_iff : forall x y : A, eqA x y = true <-> x = y)
           (B_iff : forall x y : B, eqB x y = true <-> x = y)
  : forall x y, prod_beq eqA eqB x y = true <-> x = y.
Proof.
  split; [ apply internal_prod_dec_bl | apply internal_prod_dec_lb ];
    first [ apply A_iff | apply B_iff ].
Defined.
Local Unset Implicit Arguments.

Global Instance reflect_eq_prod {A B eqA eqB} {_ : reflect_rel (@eq A) eqA} {_ : reflect_rel (@eq B) eqB}
  : reflect_rel (@eq (A * B)) (prod_beq eqA eqB)
  := reflect_rel_of_beq_iff (prod_beq_iff (reflect_rel_to_beq_iff _) (reflect_rel_to_beq_iff _)).

Class has_sub T := sub : T -> T -> T.
Global Instance: has_sub nat := Nat.sub.
Global Instance: has_sub Z := Z.sub.

Class has_succ T := succ : T -> T.
Global Instance: has_succ nat := S.
Global Instance: has_succ Z := Z.succ.

Class has_zero T := zero : T.
Global Instance: has_zero nat := O.
Global Instance: has_zero Z := Z0.

Class has_sort T := sort : list T -> list T.
Global Instance: has_sort nat := NatSort.sort.
Global Instance: has_sort Z := ZSort.sort.

Definition remove_smaller_args_of_size_by_reflect
           {T} {T_beq : T -> T -> bool}
           {T_reflect : reflect_rel (@eq T) T_beq}
           (sz : size)
           (args_of_size : size -> list T)
  : list T
  := let args := uniquify T_beq (args_of_size sz) in
     let smaller_args := flat_map args_of_size (smaller_sizes sz) in
     filter (fun v => negb (existsb (T_beq v) smaller_args)) args.

Ltac default_describe_goal x :=
  idtac "Params: n=" x.

Ltac runtests args_of_size describe_goal mkgoal redgoal time_solve_goal sz :=
  let args := (eval vm_compute in (remove_smaller_args_of_size_by_reflect sz args_of_size)) in
  let rec iter ls :=
      lazymatch ls with
      | [] => idtac
      | ?x :: ?xs
        => describe_goal x;
           let T := mkgoal x in
           try (solve [ assert T by (redgoal x; once (time_solve_goal x + fail 2 "time_solve_goal failed!")) ]; []);
           iter xs
      end in
  iter args.

Ltac runtests_verify_sanity args_of_size describe_goal mkgoal redgoal time_solve_goal do_verify sz :=
  let time_solve_goal'
      := lazymatch sz with
         | Sanity
           => fun x => time_solve_goal x; do_verify ()
         | _
           => fun x => time_solve_goal x
         end in
  runtests args_of_size describe_goal mkgoal redgoal time_solve_goal' sz.

Ltac step_goal_from_to_constr step_goal cur_n target_n G :=
  let test := match constr:(Set) with
              | _ => let __ := match constr:(Set) with _ => constr_eq cur_n target_n end in
                     true
              | _ => false
              end in
  lazymatch test with
  | true => G
  | false
    => let next_n := (eval cbv in (succ cur_n)) in
       let G := step_goal next_n G in
       step_goal_from_to_constr step_goal next_n target_n G
  end.

Ltac runtests_step_arg_constr args_of_size describe_goal step_goal redgoal_constr redgoal time_solve_goal sz G extra_args :=
  let args := (eval vm_compute in (remove_smaller_args_of_size_by_reflect sz args_of_size)) in
  let T := lazymatch type of args with list ?T => T end in
  let rec iter cur ls G :=
      lazymatch ls with
      | [] => idtac
      | ?x :: ?xs
        => let G := step_goal_from_to_constr step_goal cur x G in
           let G := redgoal_constr x G in
           describe_goal x;
           try (solve [ redgoal x; once (time_solve_goal x G extra_args + fail 2 "time_solve_goal failed!") ]; []);
           iter x xs G
      end in
  let zero := (eval cbv in (@zero T _)) in
  iter zero args G.

Ltac runtests_step_constr args_of_size describe_goal step_goal redgoal_constr time_solve_goal sz G :=
  runtests_step_arg_constr args_of_size describe_goal step_goal redgoal_constr ltac:(fun _ => idtac) ltac:(fun n G args => time_solve_goal n G) sz G ().

Ltac constr_run_tac f x :=
  lazymatch goal with
  | _ => f x
  end.

Ltac runtests_step_arg args_of_size describe_goal step_goal redgoal time_solve_goal sz extra_args :=
  runtests_step_arg_constr args_of_size describe_goal ltac:(fun n G => constr_run_tac step_goal n) ltac:(fun _ G => G) redgoal ltac:(fun n G args => time_solve_goal n args) sz () extra_args.

Ltac runtests_step args_of_size describe_goal step_goal redgoal time_solve_goal sz :=
  runtests_step_arg args_of_size describe_goal step_goal redgoal ltac:(fun n args => time_solve_goal n) sz ().
