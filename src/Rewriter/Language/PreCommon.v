(** Definitions used in rewrite rules and customizable tactics, which are invoked in the general rewriter framework. *)
Require Rewriter.Util.PrimitiveHList.
Require Rewriter.Util.InductiveHList.
Require Import Rewriter.Util.Notations.

Module Export Pre.
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

  Module ScrapedData.
    Local Set Primitive Projections.
    Record t :=
      {
        base_type_list_named : InductiveHList.hlist
        ; all_ident_named_interped : InductiveHList.hlist
      }.

    Definition t_with_args {rewrite_rulesT} (rules_proofs : PrimitiveHList.hlist (@snd bool Prop) rewrite_rulesT) {extraT} (extra : extraT) := t.
    Existing Class t_with_args.
  End ScrapedData.
End Pre.
