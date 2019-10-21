(** Definitions for use in pre-reified rewriter rules *)
Require Import Rewriter.Util.Notations.
Require Export Rewriter.Language.PreCommon.
Require Rewriter.Util.PrimitiveHList.
Require Rewriter.Util.InductiveHList.
Export InductiveHList.Notations.

(** Change this with [Ltac reify_debug_level ::= constr:(1).] to get
    more debugging. *)
Ltac ident_basic_assembly_debug_level := constr:(1%nat).
Ltac ident_assembly_debug_level := constr:(1%nat).
Ltac rewrite_perf_level := constr:(0%nat).

Module Named.
  Local Set Primitive Projections.
  Inductive maybe_name := no_name | a_name (_ : forall P : Prop, P -> P).
  Record t := { type : Type ; value : type ; naming : maybe_name }.
End Named.
Notation with_name name v := (@Named.Build_t _ v (Named.a_name (fun (P : Prop) (name : P) => name))) (only parsing).
Notation without_name v := (@Named.Build_t _ v Named.no_name) (only parsing).

Local Definition mymap {A B} := Eval cbv in @List.map A B.
Local Definition myapp {A} := Eval cbv in @List.app A.
Local Notation dont_do_again := (pair false) (only parsing).
Local Notation do_again := (pair true) (only parsing).

Definition rules_proofsT_with_args {T} (rules_proofs : T) :=
  { rules : _ & PrimitiveHList.hlist (@snd bool Prop) rules }.
Existing Class rules_proofsT_with_args.

Module Import RewriteRuleNotationsTactics.
  Ltac mymap_dont_do_again ls' :=
    let v := (eval cbv [mymap myapp ls'] in (mymap dont_do_again ls')) in
    exact v.
  Ltac mymap_do_again ls' :=
    let v := (eval cbv [mymap myapp ls'] in (mymap do_again ls')) in
    exact v.
  Ltac myapp x' y' :=
    let v := (eval cbv [mymap myapp x' y'] in (myapp x' y')) in
    exact v.
End RewriteRuleNotationsTactics.

Module RewriteRuleNotations.
  Notation "()" := tt : core_scope.
  Notation "' x" := (ident.literal x).

  Module ident.
    Notation literal := Pre.ident.literal (only parsing).
    Notation eagerly := Pre.ident.eagerly (only parsing).
  End ident.

  Module Import Types.
    Notation dont_do_again := (pair false) (only parsing).
    Notation do_again := (pair true) (only parsing).
    Notation default_do_again := dont_do_again (only parsing).
  End Types.

  Notation all_dont_do_again ls
    := (match ls return _ with
        | ls'
          => ltac:(mymap_dont_do_again ls')
        end) (only parsing).


  Notation all_do_again ls
    := (match ls return _ with
        | ls' => ltac:(mymap_do_again ls')
        end) (only parsing).

  Delimit Scope rew_rules_scope with rew_rules.
  Notation "x ++ y"
    := (match x%rew_rules, y%rew_rules return _ with
        | x', y' => ltac:(myapp x' y')
        end) (only parsing).
  Notation "[ ]" := nil (format "[ ]") : rew_rules_scope.
  Notation "[ x ]" := (cons x nil) : rew_rules_scope.
  Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : rew_rules_scope.

  Notation do_again := (@id (@snd bool Prop (Types.do_again _))) (only parsing).
End RewriteRuleNotations.
