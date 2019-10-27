Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Export Rewriter.Rewriter.Examples.PerfTesting.Settings.
Require Rewriter.Rewriter.Examples.LiftLetsMap.
Require Rewriter.Rewriter.Examples.Plus0Tree.
Require Rewriter.Rewriter.Examples.SieveOfEratosthenes.
Require Rewriter.Rewriter.Examples.UnderLetsPlus0.
Import ListNotations.
Global Open Scope Z_scope.
Global Open Scope nat_scope.
Local Open Scope list_scope.

(** divisions should be roughly:
- All [SuperFast] tests in a file should finish in under 10 seconds total
- The [Fast] tests should take under 10 seconds each
- The [Medium] tests should go up to about a minute each
- The [Slow] tests should go up to about 10 minutes each
- The [VerySlow] tests may take longer than 10 minutes each *)

Inductive size := SuperFast | Fast | Medium | Slow | VerySlow.

Ltac test_for_of_size sz test_for_safe test_for :=
  let do_test_for := lazymatch sz with
                     | SuperFast => test_for_safe
                     | _ => test_for
                     end in
  let do_optimize_heap
      := lazymatch sz with
         | SuperFast => fun _ => constr:(I)
         | Fast => fun _ => constr:(I)
         | _
           => fun _
              => let __ := match constr:(Set) with _ => optimize_heap end in
                 constr:(I)
         end in
  (* now we insert optimize_heap if necessary *)
  fun timetest =>
    let timetest := fun arg => let __ := do_optimize_heap () in
                               timetest arg in
    do_test_for timetest.

Definition smaller_sizes (sz : size) : list size
  := match sz with
     | SuperFast => []
     | Fast => [SuperFast]
     | Medium => [SuperFast; Fast]
     | Slow => [SuperFast; Fast; Medium]
     | VerySlow => [SuperFast; Fast; Medium; Slow]
     end.

Definition remove_smaller_args_of_size {T} (T_beq : T -> T -> bool) (sz : size)
           (args_of_size : size -> list T)
  : list T
  := let args := args_of_size sz in
     let smaller_args := flat_map args_of_size (smaller_sizes sz) in
     filter (fun v => negb (existsb (T_beq v) smaller_args)) args.

Module LiftLetsMap.
  Import Examples.LiftLetsMap.
  Global Open Scope nat_scope.

  Definition args_of_size' (test_tac_n : nat) (s : size)
    := let '(n_count, m_count)
           := match test_tac_n, s with
              | _, SuperFast => (5, 5)
              | _, Fast => (10, 10)
              | _, Medium => (20, 20)
              | _, Slow => (50, 50)
              | _, VerySlow => (100, 100)
              end in
       flat_map (fun n => map (fun m => (n, m)) (seq 1 m_count)) (seq 1 n_count).
  Definition args_of_size (test_tac_n : nat) (s : size)
    := remove_smaller_args_of_size (Prod.prod_beq _ _ Nat.eqb Nat.eqb) s (args_of_size' test_tac_n).

  Ltac run test_tac_n size :=
    let test_for_tac := test_for_of_size size test_for_safe test_for in
    let args := (eval vm_compute in (args_of_size test_tac_n size)) in
    let test_tac := lazymatch test_tac_n with
                    | 0 => timetest0
                    | 1 => timetest1
                    | 2 => timetest2
                    end in
    let rec iter ls :=
        lazymatch ls with
        | [] => idtac
        | (?n, ?m) :: ?ls
          => test_for test_tac n m;
             iter ls
        end in
    iter args.
End LiftLetsMap.

Module Plus0Tree.
  Import Examples.Plus0Tree.
  Global Open Scope nat_scope.

  Definition args_of_size' (test_tac_n : nat) (s : size)
    := let '(n_count, m_count)
           := match test_tac_n, s with
              | _, SuperFast => (12, 2)
              | _, Fast => (20, 10)
              | _, Medium => (50, 50)
              | _, Slow => (100, 100)
              | _, VerySlow => (1000, 1000)
              end in
       flat_map (fun n => map (fun m => (n, m)) (seq 1 m_count)) (seq 1 n_count).
  Definition args_of_size (test_tac_n : nat) (s : size)
    := remove_smaller_args_of_size (Prod.prod_beq _ _ Nat.eqb Nat.eqb) s (args_of_size' test_tac_n).

  Ltac run test_tac_n size :=
    let test_for_tac := test_for_of_size size test_for_safe test_for in
    let args := (eval vm_compute in (args_of_size test_tac_n size)) in
    let test_tac := lazymatch test_tac_n with
                    | 0 => timetest0
                    | 1 => timetest1
                    | 2 => timetest2
                    | 3 => timetest3
                    | 4 => timetest4
                    end in
    let rec iter ls :=
        lazymatch ls with
        | [] => idtac
        | (?n, ?m) :: ?ls
          => test_for test_tac n m;
             iter ls
        end in
    iter args.
End Plus0Tree.

Module SieveOfEratosthenes.
  Import Examples.SieveOfEratosthenes.
  Global Open Scope nat_scope.

  Definition args_of_size (test_tac_n : nat) (s : size)
    := match test_tac_n, s with
       | _, SuperFast => [(2, 3, 1); (5, 99, 2)]
       | _, Fast => [(101, 499, 2)]
       | _, Medium => [(501, 1001, 2)]
       | _, Slow => [(1001, 2999, 2)]
       | _, VerySlow => [(3001, 4999, 2)]
       end%Z.

  Ltac run test_tac_n size :=
    let test_from_to_tac := test_for_of_size size test_from_to_safe test_from_to in
    let args := (eval vm_compute in (args_of_size test_tac_n size)) in
    let test_tac := lazymatch test_tac_n with
                    | 0 => timetest0
                    | 1 => timetest1
                    | 2 => timetest2
                    | 3 => timetest3
                    | 4 => timetest4
                    | 5 => timetest5
                    | 6 => timetest6
                    end in
    let rec iter ls :=
        lazymatch ls with
        | [] => idtac
        | (?min, ?max, ?step) :: ?ls
          => test_from_to_tac test_tac min max step;
             iter ls
        end in
    iter args.
End SieveOfEratosthenes.

Module UnderLetsPlus0.
  Import Examples.UnderLetsPlus0.
  Global Open Scope nat_scope.

  Definition args_of_size (test_tac_n : nat) (s : size)
    := match test_tac_n, s with
       | _, SuperFast => [(1, 10, 1)]
       | _, Fast => [(11, 100, 1)]
       | _, Medium => [(100, 500, 1)]
       | _, Slow => [(500, 1000, 1)]
       | _, VerySlow => [(1000, 5000, 1)]
       end.

  Ltac run test_tac_n size :=
    let test_from_to_tac := test_for_of_size size test_from_to_safe test_from_to in
    let args := (eval vm_compute in (args_of_size test_tac_n size)) in
    let test_tac := lazymatch test_tac_n with
                    | 0 => timetest0
                    | 1 => timetest1
                    | 2 => timetest2
                    | 3 => timetest3
                    end in
    let rec iter ls :=
        lazymatch ls with
        | [] => idtac
        | (?min, ?max, ?step) :: ?ls
          => test_from_to_tac test_tac min max step;
             iter ls
        end in
    iter args.
End UnderLetsPlus0.
