Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.UnderLets.

Module Compilers.
  Import Language.Compilers.
  Import UnderLets.Compilers.

  Module UnderLets.
    Import UnderLets.Compilers.UnderLets.
    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).
      Local Notation UnderLets := (@UnderLets base_type ident).

      Section for_interp2.
        Context {base_interp : base_type -> Type}
                (ident_interp : forall t, ident t -> type.interp base_interp t).

        Section gen.
          Context {var : type -> Type}
                  {t T1}
                  (R' : forall t, @expr var t -> var t -> Prop)
                  (R : T1 -> type.interp base_interp t -> Prop)
                  (v2 : type.interp base_interp t)
                  (K : Prop).

          Fixpoint cached_interp_related_gen_implT (e : @UnderLets var T1) : Prop
            := match e with
               | Base v1 => R v1 v2 -> K
               | UnderLet t e f
                 => (* ask for the cached version of [e] *)
                   forall (v : var t) (pf : R' t e v),
                     cached_interp_related_gen_implT (f v)
               end.
        End gen.

        Section pf.
          Local Notation var := (type.interp base_interp) (only parsing).
          Definition cached_interp_related_implT {t} (e : @UnderLets var (@expr var t)) (v : type.interp base_interp t) : Prop
            := cached_interp_related_gen_implT
                 (fun t e v => expr.interp ident_interp e = v)
                 (fun e v => expr.interp ident_interp e = v)
                 v
                 (expr.interp ident_interp (UnderLets.to_expr_App e) = v)
                 e.

          Lemma cached_interp_related_impl {t} e v
            : @cached_interp_related_implT t e v.
          Proof using Type.
            cbv [cached_interp_related_implT].
            revert v; induction e; cbn; trivial; [].
            intros; subst; auto.
          Qed.
        End pf.
      End for_interp2.
    End with_ident.
  End UnderLets.
End Compilers.
