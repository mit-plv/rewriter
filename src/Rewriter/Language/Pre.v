(** Definitions for use in pre-reified rewriter rules *)
Require Import Coq.ZArith.BinInt.
Require Import Rewriter.Util.ZUtil.Definitions.
Require Import Rewriter.Util.ZUtil.Notations.
Require Import Rewriter.Util.ListUtil.
Require Import Rewriter.Util.Notations.
Require Rewriter.Util.PrimitiveHList.
Local Open Scope bool_scope.
Local Open Scope Z_scope.

Module ident.
  Definition literal {T} (v : T) := v.
  Definition eagerly {T} (v : T) := v.
  Definition gets_inlined (real_val : bool) {T} (v : T) : bool := real_val.

  Module Thunked.
    Definition bool_rect P (t f : Datatypes.unit -> P) (b : bool) : P
      := Datatypes.bool_rect (fun _ => P) (t tt) (f tt) b.
    Definition list_rect {A} P (N : Datatypes.unit -> P) (C : A -> list A -> P -> P) (ls : list A) : P
      := Datatypes.list_rect (fun _ => P) (N tt) C ls.
    Definition list_case {A} P (N : Datatypes.unit -> P) (C : A -> list A -> P) (ls : list A) : P
      := ListUtil.list_case (fun _ => P) (N tt) C ls.
    Definition nat_rect P (O_case : unit -> P) (S_case : nat -> P -> P) (n : nat) : P
      := Datatypes.nat_rect (fun _ => P) (O_case tt) S_case n.
    Definition option_rect {A} P (S_case : A -> P) (N_case : unit -> P) (o : option A) : P
      := Datatypes.option_rect (fun _ => P) S_case (N_case tt) o.
  End Thunked.
End ident.

Local Set Implicit Arguments.
Scheme Minimality for bool Sort Type.
Scheme Minimality for prod Sort Type.
Scheme Minimality for nat Sort Type.
Scheme Minimality for list Sort Type.
Scheme Minimality for option Sort Type.

Definition nat_rect_arrow_nodep P Q := @nat_rect_nodep (P -> Q).
Definition list_rect_arrow_nodep A P Q := @list_rect_nodep A (P -> Q).

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

Module TypeList.
  Inductive t := nil | cons (T : Type) (vs : t).

  Fixpoint nth (n : nat) (l : t) (default : Type) {struct l} :=
    match n, l with
    | O, cons x _ => x
    | S m, cons _ l => nth m l default
    | _, _ => default
    end.

  Module Export Notations.
    Delimit Scope type_list_scope with type_list.
    Bind Scope type_list_scope with t.
    Notation "[ ]" := nil (format "[ ]") : type_list_scope.
    Notation "[ x ]" := (cons x nil) : type_list_scope.
    Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : type_list_scope.
  End Notations.
End TypeList.
Export TypeList.Notations.

Module Named.
  Local Set Primitive Projections.
  Inductive maybe_name := no_name | a_name (_ : forall P : Prop, P -> P).
  Record t := { type : Type ; value : type ; naming : maybe_name }.
End Named.
Notation with_name name v := (@Named.Build_t _ v (Named.a_name (fun (P : Prop) (name : P) => name))) (only parsing).
Notation without_name v := (@Named.Build_t _ v Named.no_name) (only parsing).

Module GallinaAndReifiedIdentList.
  Inductive t := nil | cons {T1 T2 : Type} (v1 : T1) (v2 : T2) (vs : t).
End GallinaAndReifiedIdentList.

Module ScrapedData.
  Local Set Primitive Projections.
  Record t :=
    {
      base_type_list_named : GallinaIdentList.t
      ; all_ident_named_interped : GallinaIdentList.t
    }.

  Definition t_with_args {rewrite_rulesT} (rules_proofs : PrimitiveHList.hlist (@snd bool Prop) rewrite_rulesT) := t.
End ScrapedData.

Local Definition mymap {A B} := Eval cbv in @List.map A B.
Local Definition myapp {A} := Eval cbv in @List.app A.
Local Notation dont_do_again := (pair false) (only parsing).
Local Notation do_again := (pair true) (only parsing).

Definition rules_proofsT_with_args {T} (rules_proofs : T) :=
  { rules : _ & PrimitiveHList.hlist (@snd bool Prop) rules }.

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
  Notation "' x" := (ident.literal x).
  Notation dont_do_again := (pair false) (only parsing).
  Notation do_again := (pair true) (only parsing).
  Notation default_do_again := dont_do_again (only parsing).

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
End RewriteRuleNotations.
