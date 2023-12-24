(** Definitions used in rewrite rules and customizable tactics, which are invoked in the general rewriter framework. *)
Require Import Ltac2.Init.
Require Rewriter.Util.PrimitiveHList.
Require Rewriter.Util.InductiveHList.
Require Import Rewriter.Util.Notations.

Module Export Pre.
  Module ident.
    Definition literal {T} (v : T) := v.
    Definition eagerly {T} (v : T) := v.
    Definition gets_inlined (real_val : bool) {T} (v : T) : bool := real_val.
  End ident.

  (** These tactics should operate even on terms with unbound de
      Bruijn indices.  Although we pass a list containing the types
      and natural names of all unbound de Bruijn indices, this list
      should ideally be unused, for performance reasons *)
  (** Modify this to get more match-to-elim conversion *)
  Ltac2 mutable reify_preprocess_extra (ctx_tys : binder list) (term : constr) := term.
  Ltac2 mutable reify_ident_preprocess_extra (ctx_tys : binder list) (term : constr) := term.
  (** Change this with [Ltac2 Set reify_debug_level ::= 1.] to get
      more debugging. *)
  Ltac2 mutable reify_debug_level : int := 0.
  Ltac2 mutable reify_profile_cbn : bool := false.

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
