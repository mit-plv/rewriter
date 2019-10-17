(** Definitions for use in pre-reified rewriter rules *)
Require Import Rewriter.Util.Notations.
Require Rewriter.Util.PrimitiveHList.

Module ident.
  Definition literal {T} (v : T) := v.
  Definition eagerly {T} (v : T) := v.
  Definition gets_inlined (real_val : bool) {T} (v : T) : bool := real_val.
End ident.

(** Modify this to get more match-to-elim conversion *)
Ltac reify_preprocess_extra term := term.
Ltac reify_ident_preprocess_extra term := term.
(** Change this with [Ltac reify_debug_level ::= constr:(1).] to get
    more debugging. *)
Ltac reify_debug_level := constr:(0%nat).
Ltac ident_basic_assembly_debug_level := constr:(1%nat).
Ltac ident_assembly_debug_level := constr:(1%nat).

Module GallinaIdentList.
  Inductive t := nil | cons {T : Type} (v : T) (vs : t).

  Fixpoint nth_type (n : nat) (l : t) (default : Type) {struct l} :=
    match n, l with
    | O, @cons T _ _ => T
    | S m, @cons _ _ l => nth_type m l default
    | _, _ => default
    end.

  Fixpoint nth (n : nat) (l : t) {T} (default : T) {struct l} : nth_type n l T :=
    match n, l return nth_type n l T with
    | O, @cons _ x _ => x
    | S m, @cons _ _ l => nth m l default
    | _, _ => default
    end.

  Module Export Notations.
    Delimit Scope gallina_ident_list_scope with gi_list.
    Bind Scope gallina_ident_list_scope with t.
    Notation "[ ]" := nil (format "[ ]") : gallina_ident_list_scope.
    Notation "[ x ]" := (cons x nil) : gallina_ident_list_scope.
    Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : gallina_ident_list_scope.
  End Notations.
End GallinaIdentList.
Export GallinaIdentList.Notations.

Module Named.
  Local Set Primitive Projections.
  Inductive maybe_name := no_name | a_name (_ : forall P : Prop, P -> P).
  Record t := { type : Type ; value : type ; naming : maybe_name }.
End Named.
Notation with_name name v := (@Named.Build_t _ v (Named.a_name (fun (P : Prop) (name : P) => name))) (only parsing).
Notation without_name v := (@Named.Build_t _ v Named.no_name) (only parsing).

Module ScrapedData.
  Local Set Primitive Projections.
  Record t :=
    {
      base_type_list_named : GallinaIdentList.t
      ; all_ident_named_interped : GallinaIdentList.t
    }.

  Definition t_with_args {rewrite_rulesT} (rules_proofs : PrimitiveHList.hlist (@snd bool Prop) rewrite_rulesT) := t.
  Existing Class t_with_args.
End ScrapedData.

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
