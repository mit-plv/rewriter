Require Import Ltac2.Ltac2.
Require Export Ltac2.Notations.
Require Export Rewriter.Util.FixCoqMistakes.

(** We replace notations taking constr with tactic, so that we don't
    pay the cost of retyping, see
    COQBUG(https://github.com/coq/coq/issues/16586) *)

(** Base tactics *)

Ltac2 Notation "eval" "red" "in" c(tactic(6)) :=
  Std.eval_red c.

Ltac2 Notation "eval" "hnf" "in" c(tactic(6)) :=
  Std.eval_hnf c.

Ltac2 Notation "eval" "simpl" s(strategy) pl(opt(seq(pattern, occurrences))) "in" c(tactic(6)) :=
  Std.eval_simpl s pl c.

Ltac2 Notation "eval" "cbv" s(strategy) "in" c(tactic(6)) :=
  Std.eval_cbv s c.

Ltac2 Notation "eval" "cbn" s(strategy) "in" c(tactic(6)) :=
  Std.eval_cbn s c.

Ltac2 Notation "eval" "lazy" s(strategy) "in" c(tactic(6)) :=
  Std.eval_lazy s c.

Ltac2 Notation "eval" "unfold" pl(list1(seq(reference, occurrences), ",")) "in" c(tactic(6)) :=
  Std.eval_unfold pl c.
(*
Ltac2 Notation "eval" "fold" pl(thunk(list1(open_constr))) "in" c(constr) :=
  Std.eval_fold (pl ()) c.
*)
Ltac2 Notation "eval" "pattern" pl(list1(seq(tactic(2), occurrences), ",")) "in" c(tactic(6)) :=
  Std.eval_pattern pl c.

Ltac2 Notation "eval" "vm_compute" pl(opt(seq(pattern, occurrences))) "in" c(tactic(6)) :=
  Std.eval_vm pl c.

Ltac2 Notation "eval" "native_compute" pl(opt(seq(pattern, occurrences))) "in" c(tactic(6)) :=
  Std.eval_native pl c.
