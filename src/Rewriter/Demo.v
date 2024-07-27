(** * Demonstration of the Rewriter *)
(** This file is intended as a step-by-step guide for getting
    acquainted with how to use the rewriter, and all of the features
    thereof.  It is not intended to explain anything about how the
    rewriter is implemented; for that, see the README. *)
(** We begin by importing the entry-point for using the rewriter. *)
Require Import Rewriter.Util.plugins.RewriterBuild.

(** We will be working with examples involving arithmetic on [nat] and
    [Z], as well as some examples on [list], so we import the relevant
    files. *)
From Coq Require Import Arith ZArith List.
Import ListNotations. Local Open Scope list_scope.

(** We [Unset Ltac Backtrace] to get prettier error messages. *)
Local Unset Ltac Backtrace.

(** We start with a simple example: we want to use the rewriter to
    solve [x + 0 = 0 + x]. *)
Search (?x + 0 = ?x).
(** We make a rewriter with the rules for [x + 0 = x] and [0 + x =
    x]. *)
Make rew0nat := Rewriter For (Nat.add_0_r, Nat.add_0_l).
(* Note that if we add [Time], I get:
   Finished transaction in 10.741 secs (10.732u,0.007s) (successful) *)

(** Now we can rewrite in the goal. *)
Goal forall x, x + 0 = 0 + x.
Proof.
  Rewrite_for rew0nat.
  (** The goal is now [x = x] *)
  reflexivity.
Qed.

(** Note that we can also rewrite just on one side. *)
Goal forall x, x + 0 = 0 + x.
Proof.
  Rewrite_lhs_for rew0nat.
  (** The goal is now [x = 0 + x] *)
  Rewrite_rhs_for rew0nat.
  (** The goal is now [x = x] *)
  reflexivity.
Qed.

(** Note that [Rewrite_for] will run [intros] if necessary, and
    otherwise only supports goals which are equalities.  If you want
    to rewrite with a non-equality goal, you can use [replace]. *)

(** It would be nice if [ereplace] existed.  We make it exist. *)
Tactic Notation "ereplace" uconstr(from) "with" open_constr(to)
  := replace from with to.
Tactic Notation "ereplace" uconstr(from) "with" open_constr(to) "by" tactic3(tac)
  := replace from with to by tac.

Goal forall (P : nat -> Prop) x, P x -> P (x + 0).
Proof.
  intros P x H.
  Fail Rewrite_for rew0nat.
  (** The command has indeed failed with message:
      Tactic failure: The goal (P (x + 0)) is not an equality. *)
  ereplace (x + 0) with _.
  2: Rewrite_rhs_for rew0nat; reflexivity.
  exact H.
Qed.

(** You might ask, why not replace [P (x + 0)] rather than [x + 0].
    The answer is that the rewriter doesn't currently support
    identifiers landing in [Type], [Prop], etc.  This is primarily an
    engineering limitation.  We can see the error messages that we
    get: *)

Goal forall (P : nat -> Prop) x, P x -> P (x + 0).
Proof.
  intros P x H.
  ereplace (P (x + 0)) with _.
  Fail 2: Rewrite_rhs_for rew0nat; reflexivity.
  (** The command has indeed failed with message:
      Tactic failure: Unrecognized type: Prop. *)
Abort.
