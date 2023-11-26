Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Inversion.
Require Import Rewriter.Util.Tactics.BreakMatch.
Require Import Rewriter.Util.Tactics.DestructHead.
Require Import Rewriter.Util.Tactics.UniquePose.
Require Import Rewriter.Util.Tactics.SplitInContext.
Require Import Rewriter.Util.Tactics.SpecializeBy.
Require Import Rewriter.Util.Tactics.SpecializeAllWays.
Require Import Rewriter.Util.Tactics.SetoidSubst.
Require Import Rewriter.Util.Option.
Require Import Rewriter.Util.NatUtil.
Require Import Rewriter.Util.Sigma.
Require Import Rewriter.Util.ListUtil.
Require Import Rewriter.Util.ListUtil.Forall.
Require Import Rewriter.Util.Bool.
Require Import Rewriter.Util.Bool.Reflect.
Require Import Rewriter.Util.Prod.
Require Import Rewriter.Util.Logic.ProdForall.
Require Import Rewriter.Util.Decidable.
Require Import Rewriter.Util.HProp.
Require Import Rewriter.Util.Equality.
Require Import Rewriter.Util.CPSNotations.
Require Import Rewriter.Util.Notations.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import expr.Notations.

  Create HintDb wf discriminated.
  Create HintDb interp discriminated.
  #[global] Hint Constants Opaque : wf interp.

  #[global] Hint Opaque expr.interp expr.Interp : interp rewrite.
  #[global] Hint Extern 2 => typeclasses eauto : wf.

  Module type.
    Section eqv.
      Context {base_type} {interp_base_type : base_type -> Type}.
      Local Notation eqv := (@type.related base_type interp_base_type (fun _ => eq)).

      Lemma eqv_iff_eq_of_funext
            (funext : forall A B (f g : type.interp interp_base_type A -> type.interp interp_base_type B),
                (forall x, f x = g x)
                -> f = g)
            {t f g}
        : @eqv t f g <-> f = g.
      Proof using Type.
        induction t as [|s IHs d IHd]; cbn [type.related]; cbv [respectful]; [ reflexivity | ].
        split; intro H.
        { apply funext; intro; apply IHd, H, IHs; reflexivity. }
        { intros; apply IHd; subst; f_equal; apply IHs; assumption. }
      Qed.

      Local Instance related_Symmetric {t} {R : forall t, relation (interp_base_type t)}
             {R_sym : forall t, Symmetric (R t)}
        : Symmetric (@type.related base_type interp_base_type R t) | 100.
      Proof using Type.
        cbv [Symmetric] in *;
          induction t; cbn [type.related type.interp] in *; repeat intro; eauto.
      Qed.

      Local Instance related_Transitive {t} {R : forall t, relation (interp_base_type t)}
            {R_sym : forall t, Symmetric (R t)}
            {R_trans : forall t, Transitive (R t)}
        : Transitive (@type.related base_type interp_base_type R t) | 100.
      Proof using Type.
        induction t; cbn [type.related]; [ exact _ | ].
        cbv [respectful]; cbn [type.interp].
        intros f g h Hfg Hgh x y Hxy.
        etransitivity; [ eapply Hfg; eassumption | eapply Hgh ].
        etransitivity; first [ eassumption | symmetry; eassumption ].
      Qed.

      Global Instance eqv_Transitive {t} : Transitive (@eqv t) | 10 := _.
      Global Instance eqv_Symmetric {t} : Symmetric (@eqv t) | 10 := _.

      Local Ltac t :=
        try split; repeat intro; subst;
        repeat first [ etransitivity; (idtac + symmetry); eassumption
                     | etransitivity; (idtac + symmetry); try eassumption; [] ].

      Section proper.
        Context {R : forall t, relation (interp_base_type t)}
                {R_sym : forall t, Symmetric (R t)}
                {R_trans : forall t, Transitive (R t)}.

        Global Instance related_Proper_related1_impl {t}
          : Proper (type.related R ==> eq ==> Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related2_impl {t}
          : Proper (eq ==> type.related R ==> Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related12_impl {t}
          : Proper (type.related R ==> type.related R ==> Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related1f_impl {t}
          : Proper (Basics.flip (type.related R) ==> eq ==> Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related2f_impl {t}
          : Proper (eq ==> Basics.flip (type.related R) ==> Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related1f2f_impl {t}
          : Proper (Basics.flip (type.related R) ==> Basics.flip (type.related R) ==> Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related12f_impl {t}
          : Proper (type.related R ==> Basics.flip (type.related R) ==> Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related1f2_impl {t}
          : Proper (Basics.flip (type.related R) ==> type.related R ==> Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.


        Global Instance related_Proper_related1_flip_impl {t}
          : Proper (type.related R ==> eq ==> Basics.flip Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related2_flip_impl {t}
          : Proper (eq ==> type.related R ==> Basics.flip Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related12_flip_impl {t}
          : Proper (type.related R ==> type.related R ==> Basics.flip Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related1f_flip_impl {t}
          : Proper (Basics.flip (type.related R) ==> eq ==> Basics.flip Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related2f_flip_impl {t}
          : Proper (eq ==> Basics.flip (type.related R) ==> Basics.flip Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related1f2f_flip_impl {t}
          : Proper (Basics.flip (type.related R) ==> Basics.flip (type.related R) ==> Basics.flip Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related12f_flip_impl {t}
          : Proper (type.related R ==> Basics.flip (type.related R) ==> Basics.flip Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related1f2_flip_impl {t}
          : Proper (Basics.flip (type.related R) ==> type.related R ==> Basics.flip Basics.impl)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.


        Global Instance related_Proper_related1_iff {t}
          : Proper (type.related R ==> eq ==> iff)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related2_iff {t}
          : Proper (eq ==> type.related R ==> iff)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related12_iff {t}
          : Proper (type.related R ==> type.related R ==> iff)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related1f_iff {t}
          : Proper (Basics.flip (type.related R) ==> eq ==> iff)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related2f_iff {t}
          : Proper (eq ==> Basics.flip (type.related R) ==> iff)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related1f2f_iff {t}
          : Proper (Basics.flip (type.related R) ==> Basics.flip (type.related R) ==> iff)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related12f_iff {t}
          : Proper (type.related R ==> Basics.flip (type.related R) ==> iff)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.

        Global Instance related_Proper_related1f2_iff {t}
          : Proper (Basics.flip (type.related R) ==> type.related R ==> iff)
                   (@type.related base_type interp_base_type R t) | 10.
        Proof using R_sym R_trans. t. Qed.
      End proper.
    End eqv.
    #[global] Hint Extern 100 (Symmetric (@type.related ?base_type ?interp_base_type ?R ?t))
    => (tryif has_evar R then fail else simple apply (@related_Symmetric base_type interp_base_type t R)) : typeclass_instances.
    #[global] Hint Extern 100 (Transitive (@type.related ?base_type ?interp_base_type ?R ?t))
    => (tryif has_evar R then fail else simple apply (@related_Transitive base_type interp_base_type t R)) : typeclass_instances.

    Section app_curried_instances.
      Context {base_type} {base_interp : base_type -> Type}.
      (* Might want to add the following to make [app_curried_Proper] usable by [setoid_rewrite]? *)
      (* See https://github.com/coq/coq/issues/8179
<<
Lemma PER_valid_l {A} {R : relation A} {HS : Symmetric R} {HT : Transitive R} x y (H : R x y) : Proper R x.
Proof. hnf; etransitivity; eassumption || symmetry; eassumption. Qed.
Lemma PER_valid_r {A} {R : relation A} {HS : Symmetric R} {HT : Transitive R} x y (H : R x y) : Proper R y.
Proof. hnf; etransitivity; eassumption || symmetry; eassumption. Qed.
#[global] Hint Extern 10 (Proper ?R ?x) => simple eapply (@PER_valid_l _ R); [ | | solve [ eauto with nocore ] ] : typeclass_instances.
#[global] Hint Extern 10 (Proper ?R ?x) => simple eapply (@PER_valid_r _ R); [ | | solve [ eauto with nocore ] ] : typeclass_instances.
>>
*)
      Global Instance app_curried_Proper_gen {R t}
        : Proper (@type.related base_type base_interp R t ==> type.and_for_each_lhs_of_arrow (@type.related base_type base_interp R)  ==> R (type.final_codomain t))
                 (@type.app_curried base_type base_interp t) | 1.
      Proof using Type.
        cbv [Proper respectful]; induction t; cbn [type.related type.app_curried]; cbv [Proper respectful]; [ intros; assumption | ].
        intros f g Hfg x y [Hxy ?]; eauto.
      Qed.
      Lemma app_curried_Proper {t}
        : Proper (@type.related base_type base_interp (fun _ => eq) t ==> type.and_for_each_lhs_of_arrow (@type.eqv) ==> eq)
                 (@type.app_curried base_type base_interp t).
      Proof using Type. exact _. Qed.
      Global Instance and_for_each_lhs_of_arrow_Reflexive {f} {R} {_ : forall t, Reflexive (R t)} {t}
        : Reflexive (@type.and_for_each_lhs_of_arrow base_type f f R t) | 1.
      Proof using Type. cbv [Reflexive] in *; induction t; cbn; repeat split; eauto. Qed.
      Global Instance and_for_each_lhs_of_arrow_Symmetric {f} {R} {_ : forall t, Symmetric (R t)} {t}
        : Symmetric (@type.and_for_each_lhs_of_arrow base_type f f R t) | 1.
      Proof using Type. cbv [Symmetric] in *; induction t; cbn; repeat split; intuition eauto. Qed.
      Global Instance and_for_each_lhs_of_arrow_Transitive {f} {R} {_ : forall t, Transitive (R t)} {t}
        : Transitive (@type.and_for_each_lhs_of_arrow base_type f f R t) | 1.
      Proof using Type. cbv [Transitive] in *; induction t; cbn; repeat split; intuition eauto. Qed.
    End app_curried_instances.

    Lemma and_eqv_for_each_lhs_of_arrow_not_higher_order {base_type base_interp t}
           (Ht : type.is_not_higher_order t = true)
           (v : @type.for_each_lhs_of_arrow base_type (type.interp base_interp) t)
      : Proper (type.and_for_each_lhs_of_arrow (@type.eqv) (t:=t)) v.
    Proof using Type.
      cbv [Proper]; induction t as [t|s IHs d IHd]; cbn in *; [ tauto | ].
      rewrite Bool.andb_true_iff in Ht; destruct Ht.
      destruct s; cbn in *; try discriminate.
      eauto.
    Qed.

    Lemma eq_and_map_for_each_lhs_of_arrow {base_type f1 g1 F1 f2 g2 F2 P t arg1 arg2}
      : type.and_for_each_lhs_of_arrow
          P
          (@type.map_for_each_lhs_of_arrow base_type f1 g1 F1 t arg1)
          (@type.map_for_each_lhs_of_arrow base_type f2 g2 F2 t arg2)
        = type.and_for_each_lhs_of_arrow (fun t x y => P t (F1 t x) (F2 t y)) arg1 arg2.
    Proof using Type.
      induction t; [ reflexivity | ].
      repeat first [ progress cbn in *
                   | progress destruct_head'_and
                   | progress destruct_head'_prod
                   | apply f_equal2; [ reflexivity | ]
                   | solve [ eauto ] ].
    Qed.

    Lemma and_map_for_each_lhs_of_arrow_iff {base_type f1 g1 F1 f2 g2 F2 P t arg1 arg2}
      : type.and_for_each_lhs_of_arrow
          P
          (@type.map_for_each_lhs_of_arrow base_type f1 g1 F1 t arg1)
          (@type.map_for_each_lhs_of_arrow base_type f2 g2 F2 t arg2)
        <-> type.and_for_each_lhs_of_arrow (fun t x y => P t (F1 t x) (F2 t y)) arg1 arg2.
    Proof using Type. rewrite eq_and_map_for_each_lhs_of_arrow; reflexivity. Qed.

    Global Hint Immediate and_eqv_for_each_lhs_of_arrow_not_higher_order : typeclass_instances.

    Global Instance andb_bool_for_each_lhs_of_arrow_Proper
           {base_type} {f g R1 R2 R3 t}
           (R_Proper : forall t, Proper (R1 t ==> R2 t ==> eq) (R3 t))
      : Proper (@type.and_for_each_lhs_of_arrow base_type g g R1 t ==> @type.and_for_each_lhs_of_arrow base_type f f R2 t ==> eq)
               (@type.andb_bool_for_each_lhs_of_arrow base_type _ _ R3 t).
    Proof.
      cbv [Proper respectful] in *; induction t; cbn [type.andb_bool_for_each_lhs_of_arrow type.and_for_each_lhs_of_arrow];
        [ reflexivity | ].
      intros; destruct_head'_and.
      apply f_equal2; eauto.
    Qed.

    Global Instance and_for_each_lhs_of_arrow_Proper
           {base_type} {f g R1 R2 R3 R4 t}
           (R4_True_Proper : Proper R4 True)
           (R4_Proper_and : Proper (R4 ==> R4 ==> R4) and)
           (R_Proper : forall t, Proper (R1 t ==> R2 t ==> R4) (R3 t))
      : Proper (@type.and_for_each_lhs_of_arrow base_type g g R1 t ==> @type.and_for_each_lhs_of_arrow base_type f f R2 t ==> R4)
               (@type.and_for_each_lhs_of_arrow base_type _ _ R3 t).
    Proof.
      cbv [Proper respectful] in *; induction t; cbn [type.andb_bool_for_each_lhs_of_arrow type.and_for_each_lhs_of_arrow];
        [ intros; assumption | intros; apply R4_Proper_and; destruct_head'_and ];
        auto.
    Qed.

    Lemma related_hetero_iff_app_curried {base_type base_interp1 base_interp2 R} t F G
      : (@type.related_hetero base_type base_interp1 base_interp2 R t F G)
        <-> (forall x y, type.and_for_each_lhs_of_arrow (@type.related_hetero base_type base_interp1 base_interp2 R) x y -> R (type.final_codomain t) (type.app_curried F x) (type.app_curried G y)).
    Proof using Type.
      induction t as [t|s IHs d IHd]; cbn; [ tauto | ].
      cbv [respectful_hetero].
      rewrite pull_prod_forall.
      lazymatch goal with
      | [ |- (forall x y, @?P x y) <-> (forall z w, @?Q z w) ]
        => cut (forall x y, (P x y <-> Q x y)); [ intro H'; setoid_rewrite H'; reflexivity | intros ??; cbn [fst snd] ]
      end.
      lazymatch goal with
      | [ |- (?P -> ?Q) <-> (forall z w, ?P' /\ @?R z w -> @?S z w) ]
        => unify P P'; cut (P' -> (Q <-> (forall z w, R z w -> S z w))); [ change P with P'; solve [ intuition ] | intro; cbn [fst snd] ]
      end.
      eauto.
    Qed.

    Lemma related_hetero_iff_related {base_type base_interp R} t F G
      : (@type.related_hetero base_type base_interp base_interp R t F G)
        <-> (@type.related base_type base_interp R t F G).
    Proof.
      induction t as [t|s IHs d IHd]; cbn; [ tauto | ].
      cbv [respectful respectful_hetero]; split_iff; intuition eauto.
    Qed.

    Global Instance and_for_each_lhs_of_arrow_Proper_iff {base_type f g}
      : Proper (forall_relation (fun t => pointwise_relation _ (pointwise_relation _ iff)) ==> forall_relation (fun t => eq ==> eq ==> iff))
               (@type.and_for_each_lhs_of_arrow base_type f g) | 10.
    Proof.
      cbv [forall_relation pointwise_relation respectful]; intros ? ? H t ? ? ? ? ? ?; subst.
      induction t; cbn [type.and_for_each_lhs_of_arrow]; split_iff; intuition eauto.
    Qed.

    Global Instance and_for_each_lhs_of_arrow_Proper_impl {base_type f g}
      : Proper (forall_relation (fun t => pointwise_relation _ (pointwise_relation _ Basics.impl)) ==> forall_relation (fun t => eq ==> eq ==> Basics.impl))
               (@type.and_for_each_lhs_of_arrow base_type f g) | 10.
    Proof.
      cbv [forall_relation pointwise_relation respectful Basics.impl]; intros ? ? H t ? ? ? ? ? ?; subst.
      induction t; cbn [type.and_for_each_lhs_of_arrow]; intuition eauto.
    Qed.

    Lemma related_iff_app_curried {base_type base_interp R} t F G
      : (@type.related base_type base_interp R t F G)
        <-> (forall x y, type.and_for_each_lhs_of_arrow (@type.related base_type base_interp R) x y -> R (type.final_codomain t) (type.app_curried F x) (type.app_curried G y)).
    Proof using Type.
      rewrite <- related_hetero_iff_related.
      change (@type.related base_type base_interp R) with (fun t x y => @type.related base_type base_interp R t x y).
      setoid_rewrite <- related_hetero_iff_related.
      apply related_hetero_iff_app_curried.
    Qed.

    Lemma andb_bool_impl_and_for_each_lhs_of_arrow {base_type} {f g : type base_type -> Type}
          (R : forall t, f t -> g t -> bool)
          (R' : forall t, f t -> g t -> Prop)
          (HR : forall t x y, R t x y = true -> R' t x y)
          {t} x y
      : @type.andb_bool_for_each_lhs_of_arrow base_type f g R t x y = true
        -> @type.and_for_each_lhs_of_arrow base_type f g R' t x y.
    Proof.
      induction t; cbn in *; rewrite ?Bool.andb_true_iff; destruct_head'_prod; cbn [fst snd]; intuition.
    Qed.

    Lemma and_impl_andb_bool_for_each_lhs_of_arrow {base_type} {f g : type base_type -> Type}
          (R : forall t, f t -> g t -> bool)
          (R' : forall t, f t -> g t -> Prop)
          (HR : forall t x y, R' t x y -> R t x y = true)
          {t} x y
      : @type.and_for_each_lhs_of_arrow base_type f g R' t x y
        -> @type.andb_bool_for_each_lhs_of_arrow base_type f g R t x y = true.
    Proof.
      induction t; cbn in *; rewrite ?Bool.andb_true_iff; destruct_head'_prod; cbn [fst snd]; intuition.
    Qed.

    Lemma andb_bool_iff_and_for_each_lhs_of_arrow {base_type} {f g : type base_type -> Type}
          (R : forall t, f t -> g t -> bool)
          (R' : forall t, f t -> g t -> Prop)
          (HR : forall t x y, R t x y = true <-> R' t x y)
          {t} x y
      : @type.andb_bool_for_each_lhs_of_arrow base_type f g R t x y = true
        <-> @type.and_for_each_lhs_of_arrow base_type f g R' t x y.
    Proof.
      induction t; cbn in *; rewrite ?Bool.andb_true_iff; destruct_head'_prod; cbn [fst snd]; split_iff; intuition.
    Qed.
  End type.

  Module expr.
    Section with_ty.
      Context {base_type}
              {ident : type.type base_type -> Type}.
      Section with_var.
        Context {var1 var2 : type.type base_type -> Type}.
        Local Notation wfvP := (fun t => (var1 t * var2 t)%type).
        Local Notation wfvT := (list (sigT wfvP)).
        Local Notation expr := (@expr.expr base_type ident). (* But can't use this to define other notations, see COQBUG(https://github.com/coq/coq/issues/8126) *)
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Inductive wf : wfvT -> forall {t}, expr1 t -> expr2 t -> Prop :=
        | WfIdent
          : forall G {t} (idc : ident t), wf G (expr.Ident idc) (expr.Ident idc)
        | WfVar
          : forall G {t} (v1 : var1 t) (v2 : var2 t), List.In (existT _ t (v1, v2)) G -> wf G (expr.Var v1) (expr.Var v2)
        | WfAbs
          : forall G {s d} (f1 : var1 s -> expr1 d) (f2 : var2 s -> expr2 d),
            (forall (v1 : var1 s) (v2 : var2 s), wf (existT _ s (v1, v2) :: G) (f1 v1) (f2 v2))
            -> wf G (expr.Abs f1) (expr.Abs f2)
        | WfApp
          : forall G {s d}
                   (f1 : expr1 (s -> d)) (f2 : expr2 (s -> d)) (wf_f : wf G f1 f2)
                   (x1 : expr1 s) (x2 : expr2 s) (wf_x : wf G x1 x2),
            wf G (expr.App f1 x1) (expr.App f2 x2)
        | WfLetIn
          : forall G {A B}
                   (x1 : expr1 A) (x2 : expr2 A) (wf_x : wf G x1 x2)
                   (f1 : var1 A -> expr1 B) (f2 : var2 A -> expr2 B),
            (forall (v1 : var1 A) (v2 : var2 A), wf (existT _ A (v1, v2) :: G) (f1 v1) (f2 v2))
            -> wf G (expr.LetIn x1 f1) (expr.LetIn x2 f2).

        Section inversion.
          Local Notation "x == y" := (existT wfvP _ (x, y)).

          Definition wf_code (G : wfvT) {t} (e1 : expr1 t) : forall (e2 : expr2 t), Prop
            := match e1 in expr.expr t return expr2 t -> Prop with
               | expr.Ident t idc1
                 => fun e2
                    => match invert_expr.invert_Ident e2 with
                       | Some idc2 => idc1 = idc2
                       | None => False
                       end
               | expr.Var t v1
                 => fun e2
                    => match invert_expr.invert_Var e2 with
                       | Some v2 => List.In (v1 == v2) G
                       | None => False
                       end
               | expr.Abs s d f1
                 => fun e2
                    => match invert_expr.invert_Abs e2 with
                       | Some f2 => forall v1 v2, wf (existT _ s (v1, v2) :: G) (f1 v1) (f2 v2)
                       | None => False
                       end
               | expr.App s1 d f1 x1
                 => fun e2
                    => match invert_expr.invert_App e2 with
                       | Some (existT s2 (f2, x2))
                         => { pf : s1 = s2
                            | wf G (rew [fun s => expr1 (s -> d)] pf in f1) f2 /\ wf G (rew [expr1] pf in x1) x2 }
                       | None => False
                       end
               | expr.LetIn s1 d x1 f1
                 => fun e2
                    => match invert_expr.invert_LetIn e2 with
                       | Some (existT s2 (x2, f2))
                         => { pf : s1 = s2
                            | wf G (rew [expr1] pf in x1) x2
                              /\ forall v1 v2, wf (existT _ s2 (rew [var1] pf in v1, v2) :: G) (f1 v1) (f2 v2) }
                       | None => False
                       end
               end.

          Local Ltac t :=
            repeat match goal with
                   | _ => progress cbn in *
                   | _ => progress subst
                   | _ => progress inversion_option
                   | _ => progress expr.invert_subst
                   | [ H : Some _ = _ |- _ ] => symmetry in H
                   | _ => assumption
                   | _ => reflexivity
                   | _ => constructor
                   | _ => progress destruct_head False
                   | _ => progress destruct_head and
                   | _ => progress destruct_head sig
                   | _ => progress break_match_hyps
                   | _ => progress break_match
                   | [ |- and _ _ ] => split
                   | _ => exists eq_refl
                   | _ => intro
                   end.

          Definition wf_encode {G t e1 e2} (v : @wf G t e1 e2) : @wf_code G t e1 e2.
          Proof. destruct v; t. Defined.

          Definition wf_decode {G t e1 e2} (v : @wf_code G t e1 e2) : @wf G t e1 e2.
          Proof. destruct e1; t. Defined.
        End inversion.
      End with_var.

      Section with_interp.
        Context {interp_base_type : base_type -> Type}
                {interp_ident : forall t, ident t -> type.interp interp_base_type t}
                {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.

        Lemma eqv_of_interp_related_gen {var R t e v1 v2}
              (HR_iff : forall t v1 v2, (exists v, R t v v1 /\ R t v v2) <-> v1 == v2)
          : expr.interp_related_gen interp_ident (var:=var) R e v1
            -> expr.interp_related_gen interp_ident (var:=var) R e v2
            -> @type.eqv t v1 v2.
        Proof using Type.
          split_iff.
          induction e; cbn;
            repeat first [ progress split_iff
                         | progress cbv beta in *
                         | match goal with
                           | [ H : forall x y z, ex _ -> _ |- _ ] => specialize (fun x y z a b => H x y z (ex_intro _ a b))
                           | [ H : ?x == ?y, H' : forall t v1 v2, v1 == v2 -> ex _ |- ?f ?x == ?g ?y ]
                             => specialize (H' _ _ _ H); destruct H'
                           | [ H1 : ?P ?x1, H2 : ?P ?x2, H : forall a b, ?P a -> ?P b -> _ == _ |- ?x1 _ == ?x2 _ ]
                             => specialize (H _ _ H1 H2)
                           | [ H1 : ?P ?x1, H2 : ?P ?x2, H : forall a b, ?P a -> ?P b -> _ == _ |- _ ?x1 == _ ?x2 ]
                             => specialize (H _ _ H1 H2)
                           end
                         | progress destruct_head'_and
                         | progress destruct_head'_ex
                         | progress subst
                         | solve [ eauto ]
                         | intros; etransitivity; (idtac + symmetry); eassumption
                         | intro
                         | match goal with
                           | [ H : _ == ?x |- _ ] => is_var x; setoid_subst x
                           end ].
        Qed.

        Lemma eqv_iff_interp_related_gen {var R}
              (HR_iff : forall t v1 v2, (exists v, R t v v1 /\ R t v v2) <-> v1 == v2)
          : forall t v1 v2,
            (exists e, expr.interp_related_gen interp_ident (var:=var) R e v1
                       /\ expr.interp_related_gen interp_ident (var:=var) R e v2)
            <-> @type.eqv t v1 v2.
        Proof using Type.
          intros t v1 v2; split; [ intros [? [? ?] ] | intros ].
          { eapply eqv_of_interp_related_gen; eassumption. }
          { destruct (proj2 (HR_iff t v1 v2) ltac:(eassumption)) as [v ?];
              exists (expr.Var v); cbn; assumption. }
        Qed.

        Lemma eqv_iff_interp_related_gen1 {var R}
              (HR_iff : forall t v1 v2, (exists v, R t v v1 /\ R t v v2) <-> v1 == v2)
          : forall t v,
            (exists e, expr.interp_related_gen interp_ident (var:=var) R e v)
            <-> @type.eqv t v v.
        Proof using Type.
          intros; erewrite <- eqv_iff_interp_related_gen by eassumption.
          split; intros; destruct_head'_ex; destruct_head'_and; eauto.
        Qed.

        Lemma interp_related_gen_Proper_eqv_impl {var R t}
              {R_Proper : forall t, Proper (eq ==> type.eqv ==> Basics.impl) (R t)}
              (HR_iff : forall t v1 v2, (exists v, R t v v1 /\ R t v v2) <-> v1 == v2)
          : Proper (eq ==> type.eqv ==> Basics.impl) (expr.interp_related_gen (var:=var) (t:=t) interp_ident R).
        Proof using Type.
          intros e e' ? x y H H'; subst e'.
          induction e; cbn [expr.interp_related_gen] in *.
          all: repeat first [ etransitivity; (idtac + symmetry); eassumption
                            | eapply R_Proper; try eassumption; reflexivity
                            | eexists; split; eassumption
                            | progress destruct_head'_ex
                            | progress destruct_head'_and
                            | intro
                            | (do 2 eexists; repeat apply conj; [ eassumption | eassumption | ])
                            | match goal with H : _ |- _ => cbn in H; eapply H; clear H end ].
        Qed.

        Local Hint Extern 5 => symmetry : sym.
        Lemma interp_related_gen_Proper_eqv_flip_impl {var R t}
              {R_Proper : forall t, Proper (eq ==> type.eqv ==> Basics.flip Basics.impl) (R t)}
              (HR_iff : forall t v1 v2, (exists v, R t v v1 /\ R t v v2) <-> v1 == v2)
          : Proper (eq ==> type.eqv ==> Basics.flip Basics.impl) (expr.interp_related_gen (var:=var) (t:=t) interp_ident R).
        Proof using Type.
          repeat intro; subst; eapply @interp_related_gen_Proper_eqv_impl;
            cbv [Proper respectful Basics.flip Basics.impl] in *;
            intros; subst; eauto with core sym.
        Qed.

        Lemma interp_related_gen_Proper_eqv_iff {var R t}
              {R_Proper : forall t, Proper (eq ==> type.eqv ==> iff) (R t)}
              (HR_iff : forall t v1 v2, (exists v, R t v v1 /\ R t v v2) <-> v1 == v2)
          : Proper (eq ==> type.eqv ==> iff) (expr.interp_related_gen (var:=var) (t:=t) interp_ident R).
        Proof using Type.
          repeat intro; subst; split; eapply @interp_related_gen_Proper_eqv_impl;
            cbv [Proper respectful Basics.flip Basics.impl] in *;
            split_iff; try split;
              intros; subst; eauto with core sym.
        Qed.

        Lemma eqv_iff_ex_eqv2 {t} {v1 v2 : type.interp interp_base_type t}
          : (exists v, v == v1 /\ v == v2) <-> v1 == v2.
        Proof using Type.
          clear.
          split; [ intros [v [? ?] ] | exists v1; split ];
            try assumption;
            try (etransitivity; (idtac + symmetry); eassumption).
        Qed.

        Local Hint Resolve eqv_iff_ex_eqv2 : core.

        Lemma eqv_of_interp_related2 {t e v1 v2}
          : expr.interp_related interp_ident e v1
            -> expr.interp_related interp_ident e v2
            -> @type.eqv t v1 v2.
        Proof using Type. now apply eqv_of_interp_related_gen. Qed.


        Lemma eqv_iff_interp_related
          : forall t v1 v2,
            (exists e, expr.interp_related interp_ident e v1
                       /\ expr.interp_related interp_ident e v2)
            <-> @type.eqv t v1 v2.
        Proof using Type. now apply eqv_iff_interp_related_gen. Qed.

        Lemma eqv_iff_interp_related1
          : forall t v,
            (exists e, expr.interp_related interp_ident e v)
            <-> @type.eqv t v v.
        Proof using Type. now apply eqv_iff_interp_related_gen1. Qed.

        Global Instance interp_related_Proper_eqv_impl {t}
          : Proper (eq ==> type.eqv ==> Basics.impl) (expr.interp_related (t:=t) interp_ident) | 20.
        Proof using Type. now apply interp_related_gen_Proper_eqv_impl. Qed.

        Global Instance interp_related_Proper_eqv_flip_impl {t}
          : Proper (eq ==> type.eqv ==> Basics.flip Basics.impl) (expr.interp_related (t:=t) interp_ident) | 30.
        Proof using Type. now apply interp_related_gen_Proper_eqv_flip_impl. Qed.

        Global Instance interp_related_Proper_eqv_iff {t}
          : Proper (eq ==> type.eqv ==> iff) (expr.interp_related (t:=t) interp_ident) | 10.
        Proof using Type. now apply interp_related_gen_Proper_eqv_iff. Qed.


        Lemma eqv_of_interp_related {t e v}
          : expr.interp_related interp_ident e v
            -> @type.eqv t (expr.interp interp_ident e) v.
        Proof using Type.
          cbv [expr.interp_related]; induction e; cbn [expr.interp_related_gen expr.interp type.related]; cbv [respectful LetIn.Let_In].
          all: repeat first [ progress intros
                            | assumption
                            | solve [ eauto ]
                            | progress destruct_head'_ex
                            | progress destruct_head'_and
                            | progress subst
                            | match goal with
                              | [ H : _ == ?x |- _ ] => is_var x; setoid_subst x
                              end
                            | match goal with H : _ |- _ => eapply H; clear H end
                            | match goal with H : _ |- _ => cbn in H; etransitivity; [ eapply H | ]; clear H end ].
        Qed.

        Lemma eqv_of_interp_related2_or {t e1 e2 v1 v2}
              (H : e1 = e2 \/ expr.interp interp_ident e1 == expr.interp interp_ident e2)
          : expr.interp_related interp_ident e1 v1
            -> expr.interp_related interp_ident e2 v2
            -> @type.eqv t v1 v2.
        Proof using Type.
          intros H1 H2.
          apply eqv_of_interp_related in H1.
          apply eqv_of_interp_related in H2.
          destruct H; subst;
            repeat first [ etransitivity; (idtac + symmetry); eassumption
                         | etransitivity; (idtac + symmetry); try eassumption; [] ].
        Qed.

        Lemma interp_related_gen_of_wf {var R G t e1 e2}
              (HR_iff : forall t v1 v2, (exists v, R t v v1 /\ R t v v2) <-> v1 == v2)
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> (R t v1 v2 : Prop))
              (Hwf : wf G e1 e2)
          : @expr.interp_related_gen _ _ _ interp_ident var R t e1 (expr.interp interp_ident e2).
        Proof using interp_ident_Proper.
          induction Hwf.
          all: repeat first [ progress cbn [expr.interp_related_gen expr.interp List.In eq_rect] in *
                            | progress cbv [LetIn.Let_In] in *
                            | reflexivity
                            | solve [ eauto ]
                            | progress intros
                            | progress destruct_head'_or
                            | progress inversion_sigma
                            | progress inversion_prod
                            | progress specialize_by_assumption
                            | progress subst
                            | apply interp_ident_Proper
                            | match goal with
                              | [ H : expr.interp_related_gen _ _ _ (expr.interp _ ?f) |- _ ]
                                => lazymatch goal with
                                   | [ |- expr.interp _ ?f _ == expr.interp _ ?f _ ] => idtac
                                   | [ |- expr.interp _ ?f == expr.interp _ ?f ] => idtac
                                   end;
                                   eapply eqv_of_interp_related_gen in H; [ | eassumption | eassumption ];
                                   try (cbn in H; apply H)
                              | [ H : forall v1 v2, _ -> expr.interp_related_gen _ _ _ (expr.interp _ (?f v2)),
                                    Hv : _ == ?v
                                    |- expr.interp _ (?f ?v) == expr.interp _ (?f ?v) ]
                                => let v1 := fresh "v" in
                                   destruct (proj2 (HR_iff _ _ _) Hv) as [v1 [? ?] ];
                                   let T := open_constr:(_) in
                                   let H' := fresh in
                                   unshelve (evar (H' : T);
                                             specialize (H v1 v H'); subst H')
                              | [ |- exists fv xv, _ /\ _ /\ _ ]
                                => eexists (expr.interp interp_ident (expr.Abs _)), _;
                                   cbn [expr.interp]; repeat apply conj; [ eassumption | | ]
                              | [ H : _ |- _ ] => tryif constr_eq H HR_iff then fail else (apply H; clear H)
                              end
                            | (do 2 eexists; repeat apply conj; [ eassumption | eassumption | ]) ].
        Qed.

        Lemma interp_related_of_wf {G t e1 e2}
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
              (Hwf : wf G e1 e2)
          : expr.interp_related interp_ident (t:=t) e1 (expr.interp interp_ident e2).
        Proof using interp_ident_Proper. now eapply interp_related_gen_of_wf; try eassumption. Qed.
      End with_interp.

      Section with_var3.
        Context {var1 var2 var3 : type.type base_type -> Type}.
        Local Notation wfvP := (fun t => (var1 t * var2 t * var3 t)%type).
        Local Notation wfvT := (list (sigT wfvP)).
        Local Notation expr := (@expr.expr base_type ident). (* But can't use this to define other notations, see COQBUG(https://github.com/coq/coq/issues/8126) *)
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Local Notation expr3 := (@expr.expr base_type ident var3).
        Inductive wf3 : wfvT -> forall {t}, expr1 t -> expr2 t -> expr3 t -> Prop :=
        | Wf3Ident
          : forall G {t} (idc : ident t), wf3 G (expr.Ident idc) (expr.Ident idc) (expr.Ident idc)
        | Wf3Var
          : forall G {t} (v1 : var1 t) (v2 : var2 t) (v3 : var3 t), List.In (existT _ t (v1, v2, v3)) G -> wf3 G (expr.Var v1) (expr.Var v2) (expr.Var v3)
        | Wf3Abs
          : forall G {s d} (f1 : var1 s -> expr1 d) (f2 : var2 s -> expr2 d) (f3 : var3 s -> expr3 d),
            (forall (v1 : var1 s) (v2 : var2 s) (v3 : var3 s), wf3 (existT _ s (v1, v2, v3) :: G) (f1 v1) (f2 v2) (f3 v3))
            -> wf3 G (expr.Abs f1) (expr.Abs f2) (expr.Abs f3)
        | Wf3App
          : forall G {s d}
                   (f1 : expr1 (s -> d)) (f2 : expr2 (s -> d)) (f3 : expr3 (s -> d)) (wf_f : wf3 G f1 f2 f3)
                   (x1 : expr1 s) (x2 : expr2 s) (x3 : expr3 s) (wf_x : wf3 G x1 x2 x3),
            wf3 G (expr.App f1 x1) (expr.App f2 x2) (expr.App f3 x3)
        | Wf3LetIn
          : forall G {A B}
                   (x1 : expr1 A) (x2 : expr2 A) (x3 : expr3 A) (wf_x : wf3 G x1 x2 x3)
                   (f1 : var1 A -> expr1 B) (f2 : var2 A -> expr2 B) (f3 : var3 A -> expr3 B),
            (forall (v1 : var1 A) (v2 : var2 A) (v3 : var3 A), wf3 (existT _ A (v1, v2, v3) :: G) (f1 v1) (f2 v2) (f3 v3))
            -> wf3 G (expr.LetIn x1 f1) (expr.LetIn x2 f2) (expr.LetIn x3 f3).
      End with_var3.

      Section with_var4.
        Context {var1 var2 var3 var4 : type.type base_type -> Type}.
        Local Notation wfvP := (fun t => (var1 t * var2 t * var3 t * var4 t)%type).
        Local Notation wfvT := (list (sigT wfvP)).
        Local Notation expr := (@expr.expr base_type ident). (* But can't use this to define other notations, see COQBUG(https://github.com/coq/coq/issues/8126) *)
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Local Notation expr3 := (@expr.expr base_type ident var3).
        Local Notation expr4 := (@expr.expr base_type ident var4).
        Inductive wf4 : wfvT -> forall {t}, expr1 t -> expr2 t -> expr3 t -> expr4 t -> Prop :=
        | Wf4Ident
          : forall G {t} (idc : ident t), wf4 G (expr.Ident idc) (expr.Ident idc) (expr.Ident idc) (expr.Ident idc)
        | Wf4Var
          : forall G {t} (v1 : var1 t) (v2 : var2 t) (v3 : var3 t) (v4 : var4 t), List.In (existT _ t (v1, v2, v3, v4)) G -> wf4 G (expr.Var v1) (expr.Var v2) (expr.Var v3) (expr.Var v4)
        | Wf4Abs
          : forall G {s d} (f1 : var1 s -> expr1 d) (f2 : var2 s -> expr2 d) (f3 : var3 s -> expr3 d) (f4 : var4 s -> expr4 d),
            (forall (v1 : var1 s) (v2 : var2 s) (v3 : var3 s) (v4 : var4 s), wf4 (existT _ s (v1, v2, v3, v4) :: G) (f1 v1) (f2 v2) (f3 v3) (f4 v4))
            -> wf4 G (expr.Abs f1) (expr.Abs f2) (expr.Abs f3) (expr.Abs f4)
        | Wf4App
          : forall G {s d}
                   (f1 : expr1 (s -> d)) (f2 : expr2 (s -> d)) (f3 : expr3 (s -> d)) (f4 : expr4 (s -> d)) (wf_f : wf4 G f1 f2 f3 f4)
                   (x1 : expr1 s) (x2 : expr2 s) (x3 : expr3 s) (x4 : expr4 s) (wf_x : wf4 G x1 x2 x3 x4),
            wf4 G (expr.App f1 x1) (expr.App f2 x2) (expr.App f3 x3) (expr.App f4 x4)
        | Wf4LetIn
          : forall G {A B}
                   (x1 : expr1 A) (x2 : expr2 A) (x3 : expr3 A) (x4 : expr4 A) (wf_x : wf4 G x1 x2 x3 x4)
                   (f1 : var1 A -> expr1 B) (f2 : var2 A -> expr2 B) (f3 : var3 A -> expr3 B) (f4 : var4 A -> expr4 B),
            (forall (v1 : var1 A) (v2 : var2 A) (v3 : var3 A) (v4 : var4 A), wf4 (existT _ A (v1, v2, v3, v4) :: G) (f1 v1) (f2 v2) (f3 v3) (f4 v4))
            -> wf4 G (expr.LetIn x1 f1) (expr.LetIn x2 f2) (expr.LetIn x3 f3) (expr.LetIn x4 f4).
      End with_var4.

      Definition Wf {t} (e : @expr.Expr base_type ident t) : Prop
        := forall var1 var2, @wf var1 var2 nil t (e var1) (e var2).

      Definition Wf3 {t} (e : @expr.Expr base_type ident t) : Prop
        := forall var1 var2 var3, @wf3 var1 var2 var3 nil t (e var1) (e var2) (e var3).

      Definition Wf4 {t} (e : @expr.Expr base_type ident t) : Prop
        := forall var1 var2 var3 var4, @wf4 var1 var2 var3 var4 nil t (e var1) (e var2) (e var3) (e var4).

      Local Hint Constructors wf : wf.
      Lemma Wf_APP {s d f x} : @Wf (s -> d) f -> @Wf s x -> @Wf d (expr.APP f x).
      Proof using Type. cbv [Wf expr.APP]; auto with wf. Qed.
    End with_ty.
    Global Hint Opaque Wf : wf interp rewrite.
    Global Hint Constructors wf : wf.
    Global Hint Resolve Wf_APP : wf.
    Global Hint Opaque expr.APP : wf interp rewrite.
    #[global] Hint Rewrite @expr.Interp_APP : interp.

    Ltac is_expr_constructor arg :=
      lazymatch arg with
      | expr.Ident _ => idtac
      | expr.Var _ => idtac
      | expr.App _ _ => idtac
      | expr.LetIn _ _ => idtac
      | expr.Abs _ => idtac
      end.

    Ltac inversion_wf_step_gen guard_tac :=
      let postprocess H :=
          (cbv [wf_code wf_code] in H;
           simpl in H;
           try match type of H with
               | True => clear H
               | False => exfalso; exact H
               end) in
      match goal with
      | [ H : wf _ ?x ?y |- _ ]
        => guard_tac x y;
          apply wf_encode in H; postprocess H
      | [ H : wf ?x ?y |- _ ]
        => guard_tac x y;
          apply wf_encode in H; postprocess H
      end.
    Ltac inversion_wf_step_constr :=
      inversion_wf_step_gen ltac:(fun x y => is_expr_constructor x; is_expr_constructor y).
    Ltac inversion_wf_step_one_constr :=
      inversion_wf_step_gen ltac:(fun x y => first [ is_expr_constructor x | is_expr_constructor y]).
    Ltac inversion_wf_step_var :=
      inversion_wf_step_gen ltac:(fun x y => first [ is_var x; is_var y; fail 1 | idtac ]).
    Ltac inversion_wf_step := first [ inversion_wf_step_constr | inversion_wf_step_var ].
    Ltac inversion_wf_constr := repeat inversion_wf_step_constr.
    Ltac inversion_wf_one_constr := repeat inversion_wf_step_one_constr.
    Ltac inversion_wf := repeat inversion_wf_step.

    Section wf_properties.
      Context {base_type}
              {ident : type.type base_type -> Type}.
      Local Notation wf := (@wf base_type ident).
      Lemma wf_sym {var1 var2} G1 G2
            (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v2, v1)) G2)
            t e1 e2
            (Hwf : @wf var1 var2 G1 t e1 e2)
        : @wf var2 var1 G2 t e2 e1.
      Proof using Type.
        revert dependent G2; induction Hwf; constructor;
          repeat first [ progress cbn in *
                       | solve [ eauto ]
                       | progress intros
                       | progress subst
                       | progress destruct_head'_or
                       | progress inversion_sigma
                       | progress inversion_prod
                       | match goal with H : _ |- _ => apply H; clear H end ].
      Qed.

      Lemma wf_Proper_list {var1 var2} G1 G2
            (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
            t e1 e2
            (Hwf : @wf var1 var2 G1 t e1 e2)
        : @wf var1 var2 G2 t e1 e2.
      Proof using Type.
        revert dependent G2; induction Hwf; constructor;
          repeat first [ progress cbn in *
                       | progress intros
                       | solve [ eauto ]
                       | progress subst
                       | progress destruct_head'_or
                       | progress inversion_sigma
                       | progress inversion_prod
                       | match goal with H : _ |- _ => apply H; clear H end ].
      Qed.

      Lemma wf_sym_map_iff {var1 var2} G
            t e1 e2
        : @wf var2 var1 (List.map (fun '(existT t (v1, v2)) => existT _ t (v2, v1)) G) t e2 e1
          <-> @wf var1 var2 G t e1 e2.
      Proof using Type.
        split; apply wf_sym; intros ???; rewrite in_map_iff;
          intros; destruct_head'_ex; destruct_head'_sigT; destruct_head_prod; destruct_head'_and; inversion_sigma; inversion_prod; subst.
        { assumption. }
        { refine (ex_intro _ (existT _ _ (_, _)) _); split; (reflexivity || eassumption). }
      Qed.

      Lemma wf_trans_map_iff {var1 var2 var3} G
            (G1 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v1, v2)) G)
            (G2 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v2, v3)) G)
            (G3 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v1, v3)) G)
            t e1 e2 e3
            (Hwf12 : @wf var1 var2 G1 t e1 e2)
            (Hwf23 : @wf var2 var3 G2 t e2 e3)
        : @wf var1 var3 G3 t e1 e3.
      Proof.
        remember G1 as G1' eqn:HG1 in *; subst G1 G2 G3.
        revert dependent e3; revert dependent G; induction Hwf12;
          repeat first [ progress cbn in *
                       | solve [ eauto ]
                       | progress intros
                       | progress subst
                       | progress destruct_head' False
                       | progress destruct_head'_ex
                       | progress destruct_head'_sig
                       | progress destruct_head'_and
                       | progress inversion_sigma
                       | progress inversion_prod
                       | progress inversion_wf
                       | progress destruct_head'_or
                       | break_innermost_match_hyps_step
                       | progress expr.invert_subst
                       | rewrite in_map_iff in *
                       | match goal with |- wf _ _ _ => constructor end
                       | match goal with
                         | [ H : _ |- wf _ _ _ ]
                           => solve [ eapply (fun v1 v2 G => H v1 v2 ((existT _ _ (_, _, _)) :: G)); cbn; eauto ]
                         | [ |- exists x, _ ] => refine (ex_intro _ (existT _ _ (_, _, _)) _); cbn; split; [ reflexivity | ]
                         end ].
        (** This lemma is false.  Consider [var2 := λ _, unit].  Then
            [e2] does not enforce any constraint about variable
            ordering, and so [e1] and [e2] need not match on which
            variables they use. *)
      Abort.

      (* Speeds up Qed by a couple seconds *)
      Local Strategy -100 [invert_expr.invert_Var invert_expr.invert_LetIn invert_expr.invert_App invert_expr.invert_LetIn invert_expr.invert_Ident invert_expr.invert_Abs invert_expr.invert_App_cps projT1 projT2 fst snd eq_rect].
      Lemma wf3_of_wf {var1 var2 var3} G1 G2 G3 G {t}
            (HG1 : G1 = List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v1, (v1, v2, v3))) G)
            (HG2 : G2 = List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v2, (v1, v2, v3))) G)
            (HG3 : G3 = List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v3, (v1, v2, v3))) G)
            e1 e2 e3 e123
            (Hwf1 : @wf var1 _ G1 t e1 e123)
            (Hwf2 : @wf var2 _ G2 t e2 e123)
            (Hwf3 : @wf var3 _ G3 t e3 e123)
        : @wf3 base_type ident var1 var2 var3 G t e1 e2 e3.
      Proof using Type.
        subst G2 G3; revert dependent e3; revert dependent e2; revert dependent G; induction Hwf1; intros.
        Time all: repeat first [ progress subst
                               | progress cbn [projT1 projT2 fst snd eq_rect] in *
                               | progress destruct_head' False
                               | progress destruct_head'_sig
                               | progress destruct_head'_and
                               | progress destruct_head'_ex
                               | progress destruct_head'_sigT
                               | progress destruct_head'_prod
                               | progress inversion_sigma
                               | progress inversion_prod
                               | progress expr.simpl_invert_expr_in_all
                               | progress intros
                               | assumption
                               | progress inversion_wf_one_constr
                               | progress expr.inversion_expr
                               | progress expr.invert_match
                               | progress expr.invert_subst
                               | solve [ eauto ]
                               | rewrite in_map_iff in *
                               | match goal with
                                 | [ H : forall x y G, _ :: _ = map _ G -> _ |- _ ]
                                   => specialize (fun x y t a b c G => H x y (existT _ t (a, b, c) :: G)); cbn [map] in H
                                 end
                               | match goal with
                                 | [ |- wf3 _ _ _ _ ] => constructor
                                 end ].
      Time Qed.

      Lemma wf_of_wf3_default {var1 var2 var3} G {t}
            (G12 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v1, v2)) G)
            (G23 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v2, v3)) G)
            (G13 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v1, v3)) G)
            e1 e2 e3
            (Hwf : @wf3 base_type ident var1 var2 var3 G t e1 e2 e3)
        : ((forall t, var1 t -> var2 t -> var3 t) -> @wf _ _ G12 t e1 e2)
          /\ ((forall t, var1 t -> var3 t -> var2 t) -> @wf _ _ G13 t e1 e3)
          /\ ((forall t, var2 t -> var3 t -> var1 t) -> @wf _ _ G23 t e2 e3).
      Proof using Type.
        subst G12 G13 G23.
        induction Hwf; cbn [map] in *; repeat apply conj; intros; constructor; rewrite ?in_map_iff; intros;
          try eexists (existT (fun t => _ * _ * _)%type _ (_, _, _));
          split_and;
          repeat apply conj; try reflexivity; try eassumption;
            eauto.
      Qed.

      Lemma wf_of_wf3 {var1 var2} G {t}
            (G1 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v1, v2)) G)
            (G2 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v2, v3)) G)
            e1 e2 e3
            (Hwf : @wf3 base_type ident var1 var2 var2 G t e1 e2 e3)
        : @wf _ _ G1 t e1 e2.
      Proof using Type. eapply wf_of_wf3_default; eauto. Qed.

      Lemma wf4_of_wf {var1 var2 var3 var4} G1 G2 G3 G4 G {t}
            (HG1 : G1 = List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v1, (v1, v2, v3, v4))) G)
            (HG2 : G2 = List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v2, (v1, v2, v3, v4))) G)
            (HG3 : G3 = List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v3, (v1, v2, v3, v4))) G)
            (HG4 : G4 = List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v4, (v1, v2, v3, v4))) G)
            e1 e2 e3 e4 e1234
            (Hwf1 : @wf var1 _ G1 t e1 e1234)
            (Hwf2 : @wf var2 _ G2 t e2 e1234)
            (Hwf3 : @wf var3 _ G3 t e3 e1234)
            (Hwf4 : @wf var4 _ G4 t e4 e1234)
        : @wf4 base_type ident var1 var2 var3 var4 G t e1 e2 e3 e4.
      Proof using Type.
        subst G2 G3 G4; revert dependent e4; revert dependent e3; revert dependent e2; revert dependent G; induction Hwf1; intros.
        Time all: repeat first [ progress subst
                               | progress cbn [projT1 projT2 fst snd eq_rect] in *
                               | progress destruct_head' False
                               | progress destruct_head'_sig
                               | progress destruct_head'_and
                               | progress destruct_head'_ex
                               | progress destruct_head'_sigT
                               | progress destruct_head'_prod
                               | progress inversion_sigma
                               | progress inversion_prod
                               | progress expr.simpl_invert_expr_in_all
                               | progress intros
                               | assumption
                               | progress inversion_wf_one_constr
                               | progress expr.inversion_expr
                               | progress expr.invert_match
                               | progress expr.invert_subst
                               | solve [ eauto ]
                               | rewrite in_map_iff in *
                               | match goal with
                                 | [ H : forall x y G, _ :: _ = map _ G -> _ |- _ ]
                                   => specialize (fun x y t a b c G => H x y (existT _ t (a, b, c) :: G)); cbn [map] in H
                                 end
                               | match goal with
                                 | [ |- wf4 _ _ _ _ _ ] => constructor
                                 end ].
      Time Qed.

      Lemma wf3_of_wf4_default {var1 var2 var3 var4} G {t}
            (G123 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v1, v2, v3)) G)
            (G124 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v1, v2, v4)) G)
            (G134 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v1, v3, v4)) G)
            (G234 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v2, v3, v4)) G)
            e1 e2 e3 e4
            (Hwf : @wf4 base_type ident var1 var2 var3 var4 G t e1 e2 e3 e4)
        : ((forall t, var1 t -> var2 t -> var3 t -> var4 t) -> @wf3 _ _ _ _ _ G123 t e1 e2 e3)
          /\ ((forall t, var1 t -> var2 t -> var4 t -> var3 t) -> @wf3 _ _ _ _ _ G124 t e1 e2 e4)
          /\ ((forall t, var1 t -> var3 t -> var4 t -> var2 t) -> @wf3 _ _ _ _ _ G134 t e1 e3 e4)
          /\ ((forall t, var2 t -> var3 t -> var4 t -> var1 t) -> @wf3 _ _ _ _ _ G234 t e2 e3 e4).
      Proof using Type.
        subst G123 G124 G134 G234.
        induction Hwf; cbn [map] in *; repeat apply conj; intros; constructor; rewrite ?in_map_iff; intros;
          try eexists (existT (fun t => _ * _ * _ * _)%type _ (_, _, _, _));
          split_and;
          repeat apply conj; try reflexivity; try eassumption;
            eauto.
      Qed.

      Lemma wf3_of_wf4 {var1 var2 var3} G {t}
            (G1 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v1, v2, v3)) G)
            e1 e2 e3 e4
            (Hwf : @wf4 base_type ident var1 var2 var3 var3 G t e1 e2 e3 e4)
        : @wf3 _ _ _ _ _ G1 t e1 e2 e3.
      Proof using Type. eapply wf3_of_wf4_default; eauto. Qed.

      Lemma wf_of_wf4_default {var1 var2 var3 var4} G {t}
            (G12 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v1, v2)) G)
            (G13 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v1, v3)) G)
            (G14 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v1, v4)) G)
            (G23 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v2, v3)) G)
            (G24 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v2, v4)) G)
            (G34 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v3, v4)) G)
            e1 e2 e3 e4
            (Hwf : @wf4 base_type ident var1 var2 var3 var4 G t e1 e2 e3 e4)
        : ((forall t, var1 t -> var2 t -> var3 t * var4 t)%type -> @wf _ _ G12 t e1 e2)
          /\ ((forall t, var1 t -> var3 t -> var2 t * var4 t)%type -> @wf _ _ G13 t e1 e3)
          /\ ((forall t, var1 t -> var4 t -> var2 t * var3 t)%type -> @wf _ _ G14 t e1 e4)
          /\ ((forall t, var2 t -> var3 t -> var1 t * var4 t)%type -> @wf _ _ G23 t e2 e3)
          /\ ((forall t, var2 t -> var4 t -> var1 t * var3 t)%type -> @wf _ _ G24 t e2 e4)
          /\ ((forall t, var3 t -> var4 t -> var1 t * var2 t)%type -> @wf _ _ G34 t e3 e4).
      Proof using Type.
        apply wf3_of_wf4_default in Hwf; destruct_head'_and.
        repeat apply conj; intros; split_prod.
        all: repeat first [ match goal with
                            | [ H : wf3 _ _ _ _ |- _ ] => apply wf_of_wf3_default in H; destruct_head'_and
                            | [ H : wf ?G ?e1 ?e2 |- wf ?G' ?e1 ?e2 ] => replace G' with G; [ exact H | ]
                            | [ H := _ |- _ = _ ] => subst H
                            end
                          | progress specialize_by eauto
                          | rewrite List.map_map
                          | match goal with
                            | [ |- List.map _ ?x = List.map _ ?x ] => apply map_ext; intro; break_innermost_match
                            end
                          | reflexivity ].
      Qed.

      Lemma wf_of_wf4 {var1 var2} G {t}
            (G1 := List.map (fun '(existT t (v1, v2, v3, v4)) => existT _ t (v1, v2)) G)
            e1 e2 e3 e4
            (Hwf : @wf4 base_type ident var1 var2 var2 var2 G t e1 e2 e3 e4)
        : @wf _ _ G1 t e1 e2.
      Proof using Type. eapply wf_of_wf4_default; eauto. Qed.

      Lemma Wf_of_Wf3 {t} (e : expr.Expr t) : @Wf3 base_type ident t e -> @Wf base_type ident t e.
      Proof using Type. intros Hwf var1 var2; eapply wf_of_wf3 with (G:=nil), Hwf. Qed.

      Lemma Wf3_of_Wf {t} (e : expr.Expr t) : @Wf base_type ident t e -> @Wf3 base_type ident t e.
      Proof using Type. intros Hwf var1 var2 var3; eapply wf3_of_wf with (G:=nil); try eapply Hwf; reflexivity. Qed.

      Lemma Wf_iff_Wf3 {t} (e : expr.Expr t) : @Wf base_type ident t e <-> @Wf3 base_type ident t e.
      Proof using Type. split; (apply Wf_of_Wf3 + apply Wf3_of_Wf). Qed.

      Lemma Wf_of_Wf4 {t} (e : expr.Expr t) : @Wf4 base_type ident t e -> @Wf base_type ident t e.
      Proof using Type. intros Hwf var1 var2; eapply wf_of_wf4 with (G:=nil), Hwf. Qed.

      Lemma Wf4_of_Wf {t} (e : expr.Expr t) : @Wf base_type ident t e -> @Wf4 base_type ident t e.
      Proof using Type. intros Hwf var1 var2 var3 var4; eapply wf4_of_wf with (G:=nil); try eapply Hwf; reflexivity. Qed.

      Lemma Wf_iff_Wf4 {t} (e : expr.Expr t) : @Wf base_type ident t e <-> @Wf4 base_type ident t e.
      Proof using Type. split; (apply Wf_of_Wf4 + apply Wf4_of_Wf). Qed.

      Lemma Wf4_of_Wf3 {t} (e : expr.Expr t) : @Wf3 base_type ident t e -> @Wf4 base_type ident t e.
      Proof using Type. intro Hwf; apply Wf4_of_Wf, Wf_of_Wf3, Hwf. Qed.

      Lemma Wf3_of_Wf4 {t} (e : expr.Expr t) : @Wf4 base_type ident t e -> @Wf3 base_type ident t e.
      Proof using Type. intro Hwf; apply Wf3_of_Wf, Wf_of_Wf4, Hwf. Qed.

      Lemma Wf3_iff_Wf4 {t} (e : expr.Expr t) : @Wf3 base_type ident t e <-> @Wf4 base_type ident t e.
      Proof using Type. rewrite <- Wf_iff_Wf4, <- Wf_iff_Wf3; reflexivity. Qed.
    End wf_properties.
    Global Hint Immediate Wf_of_Wf3 Wf_of_Wf4 : wf.
    Global Hint Resolve Wf3_of_Wf Wf4_of_Wf : wf.
    Global Hint Opaque Wf3 Wf4 : wf interp rewrite.

    Section interp_gen.
      Context {base_type}
              {ident : type base_type -> Type}
              {base_interp : base_type -> Type}
              {R : forall t, relation (base_interp t)}.
      Section with_2.
        Context {ident_interp1 ident_interp2 : forall t, ident t -> type.interp base_interp t}
                {ident_interp_Proper : forall t, (eq ==> type.related R)%signature (ident_interp1 t) (ident_interp2 t)}.

        Lemma wf_interp_Proper_gen2
              G {t} e1 e2
              (Hwf : @wf _ _ _ _ G t e1 e2)
              (HG : forall t v1 v2, In (existT _ t (v1, v2)) G -> type.related R v1 v2)
          : type.related R (expr.interp ident_interp1 e1) (expr.interp ident_interp2 e2).
        Proof using ident_interp_Proper.
          induction Hwf;
            repeat first [ reflexivity
                         | assumption
                         | progress destruct_head' False
                         | progress destruct_head'_sig
                         | progress inversion_sigma
                         | progress inversion_prod
                         | progress destruct_head'_or
                         | progress intros
                         | progress subst
                         | inversion_wf_step
                         | progress expr.invert_subst
                         | break_innermost_match_hyps_step
                         | progress cbn [expr.interp fst snd projT1 projT2 List.In eq_rect type.eqv] in *
                         | progress cbn [type.app_curried]
                         | progress cbv [LetIn.Let_In respectful Proper] in *
                         | progress destruct_head'_and
                         | solve [ eauto with nocore ]
                         | match goal with
                           | [ |- type.related R (ident_interp1 _ ?x) (ident_interp2 _ ?y) ] => apply ident_interp_Proper
                           | [ H : context[?R (expr.interp _ _) (expr.interp _ _)] |- ?R (expr.interp _ _) (expr.interp _ _) ] => eapply H; eauto with nocore
                           end ].
        Qed.
      End with_2.

      Section with_1.
        Context {ident_interp : forall t, ident t -> type.interp base_interp t}
                {ident_interp_Proper : forall t, Proper (eq ==> type.related R) (ident_interp t)}.

        Lemma wf_interp_Proper_gen1 G {t}
              (HG : forall t v1 v2, In (existT _ t (v1, v2)) G -> type.related R v1 v2)
          : Proper (@wf _ _ _ _ G t ==> type.related R) (expr.interp ident_interp).
        Proof using ident_interp_Proper. intros ? ? Hwf; eapply @wf_interp_Proper_gen2; eassumption. Qed.

        Lemma wf_interp_Proper_gen {t}
          : Proper (@wf _ _ _ _ nil t ==> type.related R) (expr.interp ident_interp).
        Proof using ident_interp_Proper. apply wf_interp_Proper_gen1; cbn [In]; tauto. Qed.

        Lemma Wf_Interp_Proper_gen {t} (e : expr.Expr t) : Wf e -> Proper (type.related R) (expr.Interp ident_interp e).
        Proof using ident_interp_Proper. intro Hwf; apply wf_interp_Proper_gen, Hwf. Qed.
      End with_1.
    End interp_gen.

    Section invert_gen.
      Import invert_expr.
      Context {base_type : Type}.
      Local Notation type := (@type.type base_type).
      Context {ident : type -> Type}.
      Section with_var2.
        Context {var1 var2 : type -> Type}.
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).

        Lemma wf_App_curried {t e1 args1 e2 args2 G}
              (Hwfe : expr.wf G (t:=t) e1 e2)
              (Hwfargs : type.and_for_each_lhs_of_arrow (fun t => expr.wf G) args1 args2)
          : expr.wf G (ident:=ident) (var1:=var1) (var2:=var2) (App_curried e1 args1) (App_curried e2 args2).
        Proof using Type.
          induction t; cbn [type.and_for_each_lhs_of_arrow type.for_each_lhs_of_arrow App_curried] in *; [ assumption | ].
          destruct_head'_and.
          apply IHt2; try constructor; try assumption.
        Qed.

        Lemma wf_smart_App_curried {t e1 args1 e2 args2 G}
              (Hwfe : expr.wf G (t:=t) e1 e2)
              (Hwfargs : type.and_for_each_lhs_of_arrow (fun t v1 v2 => List.In (existT _ t (v1, v2)) G) args1 args2)
          : expr.wf G (ident:=ident) (var1:=var1) (var2:=var2) (smart_App_curried e1 args1) (smart_App_curried e2 args2).
        Proof using Type.
          induction Hwfe; cbn [smart_App_curried]; try apply wf_App_curried; repeat constructor.
          all: repeat first [ assumption
                            | rewrite type.eq_and_map_for_each_lhs_of_arrow
                            | progress cbn [List.In eq_rect fst snd type.and_for_each_lhs_of_arrow] in *
                            | progress intros
                            | progress subst
                            | progress destruct_head'_and
                            | progress inversion_sigma
                            | progress inversion_prod
                            | progress destruct_head'_or
                            | solve [ eapply @type.and_for_each_lhs_of_arrow_Proper_impl; [ .. | eassumption ]; try reflexivity;
                                      repeat intro; constructor; assumption ]
                            | match goal with
                              | [ H : context[wf (_ :: ?G) _ _] |- wf ?G _ _ ]
                                => eapply wf_Proper_list; [ | eapply H ]
                              end ].
        Qed.

        Lemma wf_invert_App_curried {t e1 args1 e2 args2 G}
              (He : expr.wf G (t:=t) (ident:=ident) (var1:=var1) (var2:=var2) e1 e2)
              (Hargs : type.and_for_each_lhs_of_arrow (fun t => expr.wf G) args1 args2)
          : { pf : _ = _
            | let e1' := invert_App_curried e1 args1 in
              let e2' := invert_App_curried e2 args2 in
              expr.wf G (fst (projT2 e1')) (rew [expr] pf in (fst (projT2 e2')))
              /\ type.and_for_each_lhs_of_arrow (fun t => expr.wf G) (snd (projT2 e1')) (rew [type.for_each_lhs_of_arrow _] pf in (snd (projT2 e2'))) }.
        Proof using Type.
          induction He.
          all: repeat first [ progress cbn [type.and_for_each_lhs_of_arrow invert_App_curried fst snd projT1 projT2 eq_rect] in *
                            | (exists eq_refl)
                            | solve [ eauto with wf ] ].
        Qed.

        Lemma wf_invert_AppIdent_curried {t e1 e2 G}
              (He : expr.wf G (t:=t) (ident:=ident) (var1:=var1) (var2:=var2) e1 e2)
          : option_eq
              (fun e1' e2'
               => { pf : _ = _
                  | fst (projT2 e1') = rew [ident] pf in (fst (projT2 e2'))
                    /\ type.and_for_each_lhs_of_arrow (fun t => expr.wf G) (snd (projT2 e1')) (rew [type.for_each_lhs_of_arrow _] pf in (snd (projT2 e2'))) })
              (invert_AppIdent_curried e1)
              (invert_AppIdent_curried e2).
        Proof using Type.
          destruct t; cbv [invert_AppIdent_curried option_eq]; [ | reflexivity ].
          pose proof (wf_invert_App_curried (t:=type.base _) (args1:=tt) (args2:=tt) He I).
          repeat first [ progress cbv [Option.bind] in *
                       | progress break_innermost_match
                       | progress break_innermost_match_hyps
                       | progress cbn [projT1 projT2 fst snd type.final_codomain eq_rect App_curried invert_Ident] in *
                       | progress destruct_head'_sig
                       | progress destruct_head'_and
                       | progress subst
                       | (exists eq_refl)
                       | progress expr.invert_subst
                       | progress inversion_wf_constr
                       | apply conj
                       | reflexivity
                       | assumption
                       | congruence
                       | exfalso; assumption
                       | progress inversion_option
                       | progress inversion_wf_one_constr ].
        Qed.

        Lemma invert_wf_App_curried {t1 t2 e1 args1 e2 args2 G}
              (pf : type.final_codomain t2 = type.final_codomain t1)
              (Hwf : expr.wf G (ident:=ident) (var1:=var1) (var2:=var2) (App_curried (t:=t1) e1 args1) (rew [fun t => expr (type.base t)] pf in App_curried (t:=t2) e2 args2))
          : { pf : _ = _
            | let e1' := invert_App_curried e1 args1 in
              let e2' := invert_App_curried e2 args2 in
              expr.wf G (fst (projT2 e1')) (rew [expr] pf in (fst (projT2 e2')))
              /\ type.and_for_each_lhs_of_arrow (fun t => expr.wf G) (snd (projT2 e1')) (rew [type.for_each_lhs_of_arrow _] pf in (snd (projT2 e2'))) }.
        Proof using Type.
          apply @wf_invert_App_curried with (args1:=tt) (args2:=tt) in Hwf; [ | exact I ].
          rewrite ap_transport with (f:=fun t v => invert_App_curried (t:=type.base t) v tt), rew_const in Hwf.
          rewrite !expr.invert_App_curried_App_curried in Hwf.
          exact Hwf.
        Qed.

        Lemma invert_wf_App_curried_eq_base {t1 t2 e1 args1 e2 args2 G}
              (pf : type.base (type.final_codomain t2) = type.base (type.final_codomain t1))
              (Hwf : expr.wf G (ident:=ident) (var1:=var1) (var2:=var2) (App_curried (t:=t1) e1 args1) (rew [expr] pf in App_curried (t:=t2) e2 args2))
          : { pf : _ = _
            | let e1' := invert_App_curried e1 args1 in
              let e2' := invert_App_curried e2 args2 in
              expr.wf G (fst (projT2 e1')) (rew [expr] pf in (fst (projT2 e2')))
              /\ type.and_for_each_lhs_of_arrow (fun t => expr.wf G) (snd (projT2 e1')) (rew [type.for_each_lhs_of_arrow _] pf in (snd (projT2 e2'))) }.
        Proof using Type.
          inversion_type.
          eapply invert_wf_App_curried.
          rewrite rew_map; eassumption.
        Qed.

        Lemma invert_wf_App_curried_not_app {t1 t2 e1 args1 e2 args2 G}
              (pf : type.final_codomain t2 = type.final_codomain t1)
              (Hwf : expr.wf G (ident:=ident) (var1:=var1) (var2:=var2) (App_curried (t:=t1) e1 args1) (rew [fun t => expr (type.base t)] pf in App_curried (t:=t2) e2 args2))
              (He1 : forall s f x, e1 <> expr.App (s:=s) f x)
              (He2 : forall s f x, e2 <> expr.App (s:=s) f x)
          : { pft : t2 = t1
            | expr.wf G e1 (rew [expr] pft in e2)
              /\ type.and_for_each_lhs_of_arrow (fun t => expr.wf G) args1 (rew pft in args2) }.
        Proof using Type.
          pose proof (invert_wf_App_curried pf Hwf) as Hwf'.
          rewrite !expr.invert_App_curried_not_App in Hwf' by assumption.
          cbn [projT1 projT2 fst snd] in *.
          assumption.
        Qed.

        Lemma invert_wf_App_curried_or {t1 t2 e1 args1 e2 args2 G}
              (pf : type.final_codomain t2 = type.final_codomain t1)
              (Hwf : expr.wf G (ident:=ident) (var1:=var1) (var2:=var2) (App_curried (t:=t1) e1 args1) (rew [fun t => expr (type.base t)] pf in App_curried (t:=t2) e2 args2))
              (H_at_base
               : type.count_args t1 = type.count_args t2
                 \/ ((forall s f x, e1 <> expr.App (s:=s) f x)
                     /\ (forall s f x, e2 <> expr.App (s:=s) f x)))
          : { pft : t2 = t1
            | expr.wf G e1 (rew [expr] pft in e2)
              /\ type.and_for_each_lhs_of_arrow (fun t => expr.wf G) args1 (rew pft in args2) }.
        Proof using Type.
          destruct H_at_base; [ | destruct_head'_and; now unshelve eapply invert_wf_App_curried_not_app ].
          revert dependent t2; induction t1, t2; intros.
          all: repeat first [ progress cbn [type.count_args App_curried eq_rect type.final_codomain type.and_for_each_lhs_of_arrow] in *
                            | progress subst
                            | progress destruct_head'_and
                            | progress destruct_head'_sig
                            | assumption
                            | exact I
                            | congruence
                            | (exists eq_refl)
                            | apply conj
                            | match goal with
                              | [ IH : forall e1 args1 t2 e2 args2 pf, expr.wf _ (App_curried _ _) _ -> _, Hwf : expr.wf _ (App_curried _ _) _ |- _]
                                => specialize (IH _ _ _ _ _ _ Hwf);
                                   destruct IH
                              end
                            | progress inversion_wf_constr ].
        Qed.

        Lemma invert_wf_App_curried_or_eq_base {t1 t2 e1 args1 e2 args2 G}
              (pf : type.base (type.final_codomain t2) = type.base (type.final_codomain t1))
              (Hwf : expr.wf G (ident:=ident) (var1:=var1) (var2:=var2) (App_curried (t:=t1) e1 args1) (rew [expr] pf in App_curried (t:=t2) e2 args2))
              (H_at_base
               : type.count_args t1 = type.count_args t2
                 \/ ((forall s f x, e1 <> expr.App (s:=s) f x)
                     /\ (forall s f x, e2 <> expr.App (s:=s) f x)))
          : { pft : t2 = t1
            | expr.wf G e1 (rew [expr] pft in e2)
              /\ type.and_for_each_lhs_of_arrow (fun t => expr.wf G) args1 (rew pft in args2) }.
        Proof using Type.
          inversion_type.
          eapply invert_wf_App_curried_or; [ | assumption ].
          rewrite rew_map; eassumption.
        Qed.
      End with_var2.
    End invert_gen.

    Section invert.
      Import invert_expr.
      Context {base : Type}
              {base_interp : base -> Type}
              {try_make_transport_base_cps : @type.try_make_transport_cpsT base}
              {base_beq : base -> base -> bool}.
      Local Notation base_type := (@base.type base).
      Local Notation type := (@type.type base_type).
      Context {ident : type -> Type}.
      Context {invertIdent : @InvertIdentT base base_interp ident}.
      Context {buildIdent : @ident.BuildIdentT base base_interp ident}.
      Context {reflect_base_beq : reflect_rel (@eq base) base_beq}
              {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}
              {buildInvertIdentCorrect : BuildInvertIdentCorrectT}.
      Section with_var2.
        Context {var1 var2 : type -> Type}.
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).

        Lemma wf_reify_list G {t} e1 e2
          : @wf _ _ var1 var2 G _ (reify_list (t:=t) e1) (reify_list (t:=t) e2)
            <-> List.Forall2 (wf G) e1 e2.
        Proof using reflect_base_beq.
          revert e2; induction e1 as [|e1 e1s IHe1s], e2 as [|e2 e2s];
            rewrite ?expr.reify_list_cons, ?expr.reify_list_nil;
            repeat first [ progress apply conj
                         | progress intros
                         | progress destruct_head'_and
                         | progress destruct_head'_sig
                         | progress inversion_type
                         | congruence
                         | tauto
                         | progress cbn [In] in *
                         | match goal with |- wf _ _ _ => constructor end
                         | progress inversion_wf_constr
                         | rewrite IHe1s in *
                         | progress destruct_head'_or
                         | match goal with
                           | [ H : Forall2 _ ?xs ?ys |- _ ]
                             => match xs with nil => idtac | _::_ => idtac end;
                                match ys with nil => idtac | _::_ => idtac end;
                                inversion H; clear H
                           end
                         | solve [ eauto ] ].
        Qed.

        Lemma wf_reflect_list G {t} e1 e2
           : @wf _ _ var1 var2 G (type.base (base.type.list t)) e1 e2
            -> (invert_expr.reflect_list e1 = None <-> invert_expr.reflect_list e2 = None).
        Proof using buildInvertIdentCorrect try_make_transport_base_cps_correct.
          destruct (invert_expr.reflect_list e1) eqn:H1, (invert_expr.reflect_list e2) eqn:H2;
            try (split; congruence); expr.invert_subst;
              try revert dependent e2; try revert dependent e1;
                match goal with
                | [ |- context[Some ?l = None] ]
                  => induction l as [|x xs IHxs]
                end;
                rewrite ?expr.reify_list_cons, ?expr.reify_list_nil;
                intro; rewrite expr.reflect_list_step; cbv [option_map];
                  break_innermost_match; try congruence; intros;
                    lazymatch goal with
                    | [ |- Some (?x :: ?xs) = None <-> ?P ]
                      => cut (Some xs = None <-> P); [ intuition congruence | ]
                    | [ |- ?P <-> Some (?x :: ?xs) = None ]
                      => cut (P <-> Some xs = None); [ intuition congruence | ]
                    | _ => idtac
                    end.
          all: repeat first [ progress cbn [fst snd projT1 projT2 eq_rect] in *
                            | progress destruct_head'_False
                            | progress inversion_option
                            | progress inversion_sigma
                            | progress inversion_prod
                            | discriminate
                            | progress destruct_head'_sig
                            | progress destruct_head'_and
                            | progress expr.invert_subst
                            | progress inversion_wf_constr
                            | solve [ eauto ]
                            | progress inversion_type
                            | break_innermost_match_hyps_step
                            | progress expr.invert_match
                            | progress expr.inversion_expr
                            | progress inversion_wf_one_constr ].
        Qed.

        Lemma wf_reify_option G {t} e1 e2
          : @wf _ _ var1 var2 G _ (reify_option (t:=t) e1) (reify_option (t:=t) e2)
            <-> option_eq (wf G) e1 e2.
        Proof using reflect_base_beq.
          destruct_head' option; cbn in *; split; intros.
          all: repeat first [ assumption
                            | progress inversion_option
                            | exfalso; assumption
                            | progress inversion_wf_constr
                            | progress destruct_head'_sig
                            | progress destruct_head'_and
                            | progress inversion_type
                            | constructor ].
        Qed.

        Lemma wf_reflect_option G {t} e1 e2
           : @wf _ _ var1 var2 G (type.base (base.type.option t)) e1 e2
            -> (invert_expr.reflect_option e1 = None <-> invert_expr.reflect_option e2 = None).
        Proof using buildInvertIdentCorrect try_make_transport_base_cps_correct.
          destruct (invert_expr.reflect_option e1) eqn:H1, (invert_expr.reflect_option e2) eqn:H2;
            try (split; congruence); expr.invert_subst;
              try (revert dependent e2; intro); try (revert dependent e1; intro);
                match goal with
                | [ |- context[Some ?l = None] ]
                  => destruct l
                end;
                rewrite ?expr.reify_option_Some, ?expr.reify_option_None;
                cbv [invert_expr.reflect_option];
                break_innermost_match; try congruence; intros.
          all: repeat first [ congruence
                            | progress inversion_wf_constr
                            | progress subst
                            | progress cbv [option_map] in *
                            | progress cbn [fst snd projT1 projT2 eq_rect] in *
                            | progress destruct_head' False
                            | progress destruct_head'_sig
                            | progress destruct_head'_and
                            | progress inversion_option
                            | progress inversion_sigma
                            | progress inversion_prod
                            | progress inversion_type
                            | progress break_match_hyps
                            | progress expr.invert_subst
                            | solve [ eauto ]
                            | progress inversion_wf_one_constr
                            | progress expr.invert_match
                            | progress expr.inversion_expr ].
        Qed.

        Lemma wf_smart_Literal {t v G}
          : expr.wf G (ident.smart_Literal (var:=var1) (t:=t) v) (ident.smart_Literal (var:=var2) (t:=t) v).
        Proof using reflect_base_beq.
          induction t; cbn; cbv [option_map]; break_innermost_match; repeat constructor; auto; [].
          rewrite wf_reify_list, Forall2_map_map_iff, Forall2_Forall, Forall_forall; cbv [Proper]; auto.
        Qed.

        Lemma wf_base_reify {t} v G : expr.wf G (GallinaReify.base.reify (var:=var1) (t:=t) v) (GallinaReify.base.reify (var:=var2) (t:=t) v).
        Proof using reflect_base_beq. exact wf_smart_Literal. Qed.

        Lemma wf_reify {t} v G : expr.wf G (GallinaReify.reify (var:=var1) (t:=type.base t) v) (GallinaReify.base.reify (var:=var2) (t:=t) v).
        Proof using reflect_base_beq. exact wf_smart_Literal. Qed.

        Lemma wf_smart_Literal_eq {t v1 v2 G}
          : v1 = v2 -> expr.wf G (ident.smart_Literal (var:=var1) (t:=t) v1) (ident.smart_Literal (var:=var2) (t:=t) v2).
        Proof using reflect_base_beq. intro; subst; apply wf_smart_Literal. Qed.
      End with_var2.

      Lemma Wf_base_Reify_as {t} v : expr.Wf (GallinaReify.base.Reify_as t v).
      Proof using reflect_base_beq. repeat intro; apply wf_reify. Qed.

      Lemma Wf_Reify_as {t} (v : base.interp base_interp t) : expr.Wf (GallinaReify.Reify_as (type.base t) (fun _ => v)).
      Proof using reflect_base_beq. repeat intro; apply wf_reify. Qed.

      Lemma Wf_base_reify {t} v : expr.Wf (fun var => GallinaReify.base.reify (t:=t) v).
      Proof using reflect_base_beq. repeat intro; apply wf_reify. Qed.

      Lemma Wf_reify {t} (v : base.interp base_interp t) : expr.Wf (fun var => GallinaReify.reify (t:=type.base t) v).
      Proof using reflect_base_beq. repeat intro; apply wf_reify. Qed.

      Section interp.
        Context {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}.
        Context {buildInterpIdentCorrect : ident.BuildInterpIdentCorrectT ident_interp}.

        Local Notation interp := (expr.interp ident_interp).
        Local Notation expr_interp_related := (@expr.interp_related _ _ _ (@ident_interp)).

        Lemma interp_reify_list {t} ls : interp (reify_list (t:=t) ls) = List.map interp ls.
        Proof using buildInterpIdentCorrect.
          cbv [reify_list]; induction ls as [|l ls IHls];
            cbn [list_rect map expr.interp];
            [ now rewrite ident.interp_ident_nil
            | now rewrite ident.interp_ident_cons, IHls ].
        Qed.

        Lemma interp_reify_option {t} v : interp (reify_option (t:=t) v) = Option.map interp v.
        Proof using buildInterpIdentCorrect.
          destruct v;
            rewrite ?expr.reify_option_None, ?expr.reify_option_Some; cbn [expr.interp];
              now (rewrite ident.interp_ident_None + rewrite ident.interp_ident_Some).
        Qed.

        Lemma smart_Literal_interp_related {t} v
          : expr.interp_related (@ident_interp) (ident.smart_Literal (t:=t) v) v.
        Proof using buildInterpIdentCorrect.
          induction t;
            repeat first [ progress cbn [ident.smart_Literal expr.interp_related_gen type.related base.interp] in *
                         | progress cbv [reify_option option_map option_rect expr.interp_related] in *
                         | rewrite ident.interp_ident_Literal
                         | rewrite ident.interp_ident_pair
                         | rewrite ident.interp_ident_Some
                         | rewrite ident.interp_ident_None
                         | break_innermost_match_step
                         | reflexivity
                         | do 2 eexists; repeat apply conj; [ | | reflexivity ]
                         | solve [ eauto ]
                         | apply (proj2 expr.reify_list_interp_related_iff)
                         | rewrite Forall2_map_l_iff, Forall2_Forall, Forall_forall; cbv [Proper]; intros
                         | match goal with
                           | [ |- ?x = ?y :> unit ] => now destruct x, y
                           end ].
        Qed.

        Lemma interp_smart_Literal {t} v : interp (ident.smart_Literal (t:=t) v) = v.
        Proof using buildInterpIdentCorrect.
          pose proof (@smart_Literal_interp_related t v) as H.
          eapply eqv_of_interp_related in H; assumption.
        Qed.

        Lemma reify_interp_related {t} v
          : expr_interp_related (GallinaReify.base.reify (t:=t) v) v.
        Proof using buildInterpIdentCorrect. apply smart_Literal_interp_related. Qed.

        Lemma interp_reify {t} v : interp (GallinaReify.base.reify (t:=t) v) = v.
        Proof using buildInterpIdentCorrect.
          pose proof (@reify_interp_related t v) as H.
          eapply eqv_of_interp_related in H; assumption.
        Qed.

        Lemma interp_reify_as_interp {t} v1 v2
          : v1 == v2 -> interp (GallinaReify.reify_as_interp (t:=t) v1) == v2.
        Proof using buildInterpIdentCorrect.
          induction t as [|s IHs d IHd]; cbn [GallinaReify.reify_as_interp type.related interp]; cbv [respectful]; eauto.
          intro; subst; apply interp_reify.
        Qed.

        Lemma Reify_as_interp_related {t} v
          : expr_interp_related (GallinaReify.base.Reify_as t v _) v.
        Proof using buildInterpIdentCorrect. apply reify_interp_related. Qed.

        Lemma Interp_Reify_as {t} v : expr.Interp ident_interp (GallinaReify.base.Reify_as t v) = v.
        Proof using buildInterpIdentCorrect. apply interp_reify. Qed.

        Lemma Interp_reify {t} v : expr.Interp ident_interp (fun var => GallinaReify.base.reify (t:=t) v) = v.
        Proof using buildInterpIdentCorrect. apply interp_reify. Qed.
      End interp.
    End invert.

    (** [Reify] is a notation for [Reify_as] + better type inference, so we make [Wf_Reify] available for ease of memory / lookup *)
    Notation Wf_base_Reify := Wf_base_Reify_as.
    Notation Wf_Reify := Wf_Reify_as.
    Notation Interp_Reify := Interp_Reify_as.
  End expr.

  #[global] Hint Constructors expr.wf : wf.
  #[global] Hint Resolve expr.Wf_APP expr.Wf_Reify expr.Wf_reify expr.Wf_base_Reify expr.Wf_base_reify : wf.
  (** Work around COQBUG(https://github.com/coq/coq/issues/11536) *)
  #[global] Hint Extern 1 (expr.Wf (GallinaReify.base.Reify_as _ _)) => simple apply (@expr.Wf_base_Reify) : wf.
  #[global] Hint Extern 1 (expr.Wf (GallinaReify.Reify_as _ _)) => simple apply (@expr.Wf_Reify) : wf.
  (** Work around COQBUG(https://github.com/coq/coq/issues/11536) *)
  #[global] Hint Extern 1 (expr.Wf (fun var => GallinaReify.base.reify _)) => simple apply (@expr.Wf_base_reify) : wf.
  #[global] Hint Extern 1 (expr.Wf (fun var => GallinaReify.reify _)) => simple apply (@expr.Wf_reify) : wf.
  #[global] Hint Opaque expr.APP GallinaReify.Reify_as GallinaReify.base.reify : wf interp rewrite.
  #[global] Hint Rewrite @expr.Interp_Reify @expr.interp_reify @expr.interp_reify_list @expr.interp_reify_option @expr.Interp_reify @expr.Interp_APP : interp.

  Notation Wf := expr.Wf.

  Local Ltac destructure_step :=
    first [ progress subst
          | progress inversion_option
          | progress inversion_prod
          | progress inversion_sigma
          | progress destruct_head'_sigT
          | progress destruct_head'_ex
          | progress destruct_head'_and
          | progress split_andb
          | progress type_beq_to_eq
          | progress eliminate_hprop_eq
          | match goal with
            | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
            | [ H : ?x = Some _, H' : ?x = Some _ |- _ ]
              => lazymatch x with
                 | Some _ => fail
                 | _ => rewrite H in H'
                 end
            end ].

  Local Ltac destructure_destruct_step :=
    first [ progress destruct_head'_or
          | break_innermost_match_hyps_step
          | break_innermost_match_step
          | match goal with
            | [ H : None = option_map _ _ |- _ ] => cbv [option_map] in H
            | [ H : Some _ = option_map _ _ |- _ ] => cbv [option_map] in H
            | [ |- context[andb _ _ = true] ] => rewrite Bool.andb_true_iff
            end ].
  Local Ltac destructure_split_step :=
    first [ destructure_destruct_step
          | apply conj ].

  Local Ltac saturate_pos :=
    cbv [PositiveMap.key] in *;
    repeat match goal with
           | [ H : forall p : BinNums.positive, _ -> BinPos.Pos.lt p ?q, p' : BinNums.positive |- _ ]
             => lazymatch goal with
                | [ H' : context[BinPos.Pos.lt p' q] |- _ ] => fail
                | _ => pose proof (H p')
                end
           | [ H : forall p : BinNums.positive, _ -> BinPos.Pos.lt p ?q |- context[BinPos.Pos.succ ?p'] ]
             => is_var p';
                lazymatch goal with
                | [ H' : context[BinPos.Pos.lt (BinPos.Pos.succ p') q] |- _ ] => fail
                | _ => pose proof (H (BinPos.Pos.succ p'))
                end
           | [ H : forall p : BinNums.positive, _ -> BinPos.Pos.lt p ?q, H' : context[BinPos.Pos.succ ?p'] |- _ ]
             => is_var p';
                lazymatch goal with
                | [ H' : context[BinPos.Pos.lt (BinPos.Pos.succ p') q] |- _ ] => fail
                | _ => pose proof (H (BinPos.Pos.succ p'))
                end
           end.
  Local Ltac saturate_pos_fast :=
    cbv [PositiveMap.key] in *;
    repeat match goal with
           | [ H : forall p : BinNums.positive, _ -> BinPos.Pos.lt p ?q |- _ ]
             => lazymatch goal with
                | [ H' : context[BinPos.Pos.lt q q] |- _ ] => fail
                | _ => pose proof (H q)
                end
           end.

  Local Ltac rewrite_find_add :=
    repeat match goal with
           | [ |- context[PositiveMap.find _ (PositiveMap.add _ _ _)] ] => rewrite PositiveMapAdditionalFacts.gsspec
           | [ H : context[PositiveMap.find _ (PositiveMap.add _ _ _)] |- _ ] => rewrite PositiveMapAdditionalFacts.gsspec in H
           end.

  Ltac wf_safe_t_step :=
    first [ progress intros
          | progress subst
          | progress inversion_sigma
          | progress inversion_prod
          | progress destruct_head'_sig
          | progress destruct_head'_and
          | progress destruct_head' False
          | progress cbn [List.In eq_rect] in *
          | match goal with
            | [ |- expr.wf _ _ _ ] => constructor
            end
          | solve [ eauto using conj, eq_refl, or_introl, or_intror with nocore ]
          | progress destruct_head'_or
          | match goal with
            | [ |- context[List.In _ (_ ++ _)%list] ] => rewrite in_app_iff
            | [ H : context[List.In _ (_ ++ _)%list] |- _ ] => rewrite in_app_iff in H
            | [ H : context[expr.wf _ _ _] |- expr.wf _ _ _ ]
              => eapply H; clear H; eauto with nocore; solve [ repeat wf_safe_t_step ]
            end
          | match goal with
            | [ |- _ \/ _ ] => constructor; solve [ repeat wf_safe_t_step ]
            end ].
  Ltac wf_unsafe_t_step :=
    first [ solve [ eauto with nocore ]
          | match goal with
            | [ H : context[expr.wf _ _ _] |- expr.wf _ _ _ ]
              => eapply H; eauto with nocore; match goal with |- ?G => tryif has_evar G then fail else idtac end
            | [ |- expr.wf _ _ _ ]
              => eapply expr.wf_Proper_list; [ | solve [ eauto with nocore ] ]
            end ].
  Ltac wf_safe_t := repeat wf_safe_t_step.
  Ltac wf_unsafe_t := repeat wf_unsafe_t_step.
  Ltac wf_t_step := first [ wf_safe_t_step | wf_unsafe_t_step ].
  Ltac wf_t := repeat wf_t_step.

  Ltac interp_safe_t_step :=
    first [ progress intros
          | progress subst
          | progress inversion_sigma
          | progress inversion_prod
          | progress cbn [List.In eq_rect expr.interp (*ident.interp*) type.interp base.interp (*base.base_interp*) type.eqv] in *
          | progress cbv [respectful LetIn.Let_In] in *
          | solve [ eauto using conj, eq_refl, or_introl, or_intror with nocore ]
          | progress destruct_head'_or
          | match goal with
            (*| [ |- ident.interp ?x == ident.interp ?x ] => apply ident.eqv_Reflexive*)
            (*| [ |- Proper (fun x y => ident.interp x == ident.interp y) _ ] => apply ident.eqv_Reflexive_Proper*)
            | [ H : context[expr.interp _ _ == expr.interp _ _] |- expr.interp _ _ == expr.interp _ _ ]
              => eapply H; eauto with nocore; solve [ repeat interp_safe_t_step ]
            end ].
  Ltac interp_unsafe_t_step :=
    first [ solve [ eauto with nocore ]
          | match goal with
            | [ H : context[expr.interp _ _ == expr.interp _ _] |- expr.interp _ _ == expr.interp _ _ ]
              => eapply H; eauto with nocore; match goal with |- ?G => tryif has_evar G then fail else idtac end
            end ].
  Ltac interp_safe_t := repeat interp_safe_t_step.
  Ltac interp_unsafe_t := repeat interp_unsafe_t_step.
  Ltac interp_t_step := first [ interp_safe_t_step | interp_unsafe_t_step ].
  Ltac interp_t := repeat interp_t_step.


  Module DefaultValue.
    Import Language.Compilers.DefaultValue.
    Module expr.
      Class ExprDefault_wfT {base_type ident} {d : forall var, @type.base.DefaultT _ (@expr base_type ident var)}
        := ExprDefault_wf : forall var1 var2 G t, expr.wf G (d var1 t) (d var2 t).
      Class ExprDefault_WfT {base_type ident} {d : @type.base.DefaultT _ (@Expr base_type ident)}
        := ExprDefault_Wf : forall t, expr.Wf (d t).
      Global Arguments ExprDefault_wfT {_ _} _.
      Global Arguments ExprDefault_WfT {_ _} _.
      Module base.
        Section with_base.
          Context {base : Type}
                  {base_interp : base -> Type}.
          Local Notation base_type := (@base.type base).
          Local Notation type := (@type.type base_type).
          Local Notation base_type_interp := (@base.interp base base_interp).
          Context {ident : type -> Type}.
          Context {baseDefault : @type.base.DefaultT base base_interp}
                  {buildIdent : @ident.BuildIdentT base base_interp ident}.

          Section with_var2.
            Context {var1 var2 : type -> Type}.

            Lemma wf_default G {t : base_type} : expr.wf (var1:=var1) (var2:=var2) (t:=type.base t) G expr.base.default expr.base.default.
            Proof using Type.
              induction t; wf_t.
            Qed.
          End with_var2.

          Lemma Wf_Default {t : base_type} : Wf (t:=type.base t) expr.base.Default.
          Proof using Type. repeat intro; apply @wf_default. Qed.
        End with_base.
      End base.

      Section with_base.
        Context {base : Type}
                {base_interp : base -> Type}.
        Local Notation base_type := (@base.type base).
        Local Notation type := (@type.type base_type).
        Local Notation base_type_interp := (@base.interp base base_interp).
        Context {ident : type -> Type}.
        Context {baseDefault : @type.base.DefaultT base base_interp}
                {buildIdent : @ident.BuildIdentT base base_interp ident}.

        Global Instance wf_default : @ExprDefault_wfT base_type ident _.
        Proof using Type. intros var1 var2 G t; revert G; induction t; intros; wf_t; apply base.wf_default. Qed.
        Global Instance Wf_Default : @ExprDefault_WfT base_type ident _.
        Proof using Type. repeat intro; apply @wf_default. Qed.
      End with_base.
    End expr.
  End DefaultValue.

  Module GeneralizeVar.
    Import Language.Compilers.GeneralizeVar.
    Local Open Scope etype_scope.
    Module Flat.
      Section with_base_type.
        Context {base_type : Type}
                {ident : type base_type -> Type}
                {base_type_beq : base_type -> base_type -> bool}.
        Local Notation type := (@type.type base_type).

        Fixpoint wf (G : PositiveMap.t type) {t} (e : @Flat.expr base_type ident t) : bool
          := match e with
             | Flat.Ident t idc => true
             | Flat.Var t n
               => match PositiveMap.find n G with
                  | Some t' => type.type_beq _ base_type_beq t t'
                  | None => false
                  end
             | Flat.Abs s n d f
               => match PositiveMap.find n G with
                  | None => @wf (PositiveMap.add n s G) _ f
                  | Some _ => false
                  end
             | Flat.App s d f x
               => andb (@wf G _ f) (@wf G _ x)
             | Flat.LetIn A B n ex eC
               => match PositiveMap.find n G with
                  | None => andb (@wf G _ ex) (@wf (PositiveMap.add n A G) _ eC)
                  | Some _ => false
                  end
             end.
      End with_base_type.
    End Flat.

    Section with_base_type.
      Context {base_type : Type}
              {ident : type base_type -> Type}
              {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base_type}
              {base_type_beq : base_type -> base_type -> bool}
              {reflect_base_type_beq : reflect_rel (@eq base_type) base_type_beq}
              {try_make_transport_base_type_cps_correct : @type.try_make_transport_cps_correctT base_type base_type_beq _ _}.
      Local Notation type := (@type.type base_type).
      Local Notation Flat_expr := (@Flat.expr base_type ident).
      Context {exprDefault : forall var, @DefaultValue.type.base.DefaultT type (@expr base_type ident var)}
              {wf_exprDefault : DefaultValue.expr.ExprDefault_wfT exprDefault}.

      Section with_var.
        Import BinPos.
        Context {var1 var2 : type -> Type}.

        Lemma wf_from_flat_gen
              {t}
              (e : Flat_expr t)
          : forall (G1 : PositiveMap.t type) (G2 : list { t : _ & var1 t * var2 t }%type)
                   (ctx1 : PositiveMap.t { t : type & var1 t })
                   (ctx2 : PositiveMap.t { t : type & var2 t })
                   (H_G1_ctx1 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx1))
                   (H_G1_ctx2 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx2))
                   (H_ctx_G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G2
                                               <-> (exists p, PositiveMap.find p ctx1 = Some (existT _ t v1) /\ PositiveMap.find p ctx2 = Some (existT _ t v2))),
            Flat.wf (base_type_beq:=base_type_beq) G1 e = true -> expr.wf G2 (from_flat e var1 ctx1) (from_flat e var2 ctx2).
        Proof using try_make_transport_base_type_cps_correct.
          induction e;
            repeat first [ progress cbn [Flat.wf from_flat option_map projT1 projT2 List.In fst snd] in *
                         | progress intros
                         | destructure_step
                         | progress cbv [Option.bind cpsreturn cpsbind cpscall cps_option_bind eq_rect id] in *
                         | match goal with |- expr.wf _ _ _ => constructor end
                         | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                         | congruence
                         | destructure_split_step
                         | progress rewrite_type_transport_correct
                         | match goal with
                           | [ H : context[expr.wf _ _ _] |- expr.wf _ _ _ ] => eapply H; clear H; eauto with nocore
                           | [ |- context[PositiveMap.find _ (PositiveMap.add _ _ _)] ] => rewrite PositiveMapAdditionalFacts.gsspec
                           | [ H : context[PositiveMap.find _ (PositiveMap.add _ _ _)] |- _ ] => rewrite PositiveMapAdditionalFacts.gsspec in H
                           | [ H : forall t v1 v2, In _ ?G2 <-> _ |- context[In _ ?G2] ] => rewrite H
                           | [ H : In _ ?G2, H' : forall t v1 v2, In _ ?G2 <-> _ |- _ ] => rewrite H' in H
                           | [ |- exists p, PositiveMap.find p (PositiveMap.add ?n (existT _ ?t ?v) _) = Some (existT _ ?t _) /\ _ ]
                             => exists n
                           | [ H : PositiveMap.find ?n ?ctx = ?v |- exists p, PositiveMap.find p (PositiveMap.add _ _ ?ctx) = ?v /\ _ ]
                             => exists n
                           | [ |- _ \/ exists p, PositiveMap.find p (PositiveMap.add ?n (existT _ ?t ?v) _) = Some (existT _ ?t _) /\ _ ]
                             => right; exists n
                           | [ H : PositiveMap.find ?n ?ctx = ?v |- _ \/ exists p, PositiveMap.find p (PositiveMap.add _ _ ?ctx) = ?v /\ _ ]
                             => right; exists n
                           | [ H : PositiveMap.find ?n ?G = ?a, H' : PositiveMap.find ?n ?G' = ?b, H'' : forall p, PositiveMap.find p ?G = option_map _ (PositiveMap.find p ?G') |- _ ]
                             => (tryif assert (a = option_map (@projT1 _ _) b) by (cbn [projT1 option_map]; (reflexivity || congruence))
                                  then fail
                                  else let H1 := fresh in
                                       pose proof (H'' n) as H1;
                                       rewrite H, H' in H1;
                                       cbn [option_map projT1] in H1)
                           end ].
        Qed.

        Lemma wf_from_flat
              {t}
              (e : Flat_expr t)
          : Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) e = true -> expr.wf nil (from_flat e var1 (PositiveMap.empty _)) (from_flat e var2 (PositiveMap.empty _)).
        Proof using try_make_transport_base_type_cps_correct.
          apply wf_from_flat_gen; intros *;
            repeat setoid_rewrite PositiveMap.gempty;
            cbn [In option_map];
            intuition (destruct_head'_ex; intuition (congruence || auto)).
        Qed.

        Lemma wf_from_flat_to_flat_gen
              offset G1 G2 ctx
              {t} (e1 e2 : expr t)
              (Hwf : expr.wf G1 e1 e2)
              (HG1G2 : forall t v1 v2,
                  List.In (existT _ t (v1, v2)) G1
                  -> exists v1', PositiveMap.find v1 ctx = Some (existT _ t v1')
                                 /\ List.In (existT _ t (v1', v2)) G2)
              (Hoffset : forall p, PositiveMap.find p ctx <> None -> (p < offset)%positive)
          : expr.wf G2 (var2:=var2) (from_flat (to_flat' (t:=t) e1 offset) var1 ctx) e2.
        Proof using try_make_transport_base_type_cps_correct.
          revert dependent offset; revert dependent G2; revert dependent ctx; induction Hwf; intros.
          all: repeat first [ progress cbn [from_flat to_flat' List.In projT1 projT2 fst snd] in *
                            | progress intros
                            | destructure_step
                            | progress cbv [Option.bind cpsreturn cpsbind cpscall cps_option_bind eq_rect id] in *
                            | match goal with |- expr.wf _ _ _ => constructor end
                            | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                            | congruence
                            | destructure_split_step
                            | progress rewrite_type_transport_correct
                            | match goal with
                              | [ H : List.In (existT _ ?t (?v1, ?v2)) ?G, H' : forall t' v1' v2', List.In _ ?G -> _ |- _ ]
                                => specialize (H' _ _ _ H)
                              | [ H : _ |- expr.wf _ _ _ ] => apply H; clear H
                              | [ v' : var1 ?t |- exists v : var1 ?t, _ ] => exists v'
                              | [ |- context[PositiveMap.find _ (PositiveMap.add _ _ _)] ] => rewrite PositiveMapAdditionalFacts.gsspec
                              | [ H : context[PositiveMap.find _ (PositiveMap.add _ _ _)] |- _ ] => rewrite PositiveMapAdditionalFacts.gsspec in H
                              | [ H : forall p, _ <> None -> (_ < _)%positive, H' : _ <> None |- _ ]
                                => unique pose proof (H _ H')
                              | [ H : forall p, PositiveMap.find p ?ctx <> None -> (p < ?offset)%positive,
                                    H' : PositiveMap.find ?p' ?ctx = Some _ |- _]
                                => unique assert ((p' < offset)%positive) by (apply H; rewrite H'; congruence)
                              | [ H : (?x < ?x)%positive |- _ ] => exfalso; clear -H; lia
                              | [ |- (_ < _)%positive ] => lia
                              end ].
        Qed.

        Lemma wf_from_flat_to_flat
              {t} (e1 e2 : expr t)
              (Hwf : expr.wf nil e1 e2)
          : expr.wf nil (var2:=var2) (from_flat (to_flat (t:=t) e1) var1 (PositiveMap.empty _)) e2.
        Proof using try_make_transport_base_type_cps_correct.
          eapply wf_from_flat_to_flat_gen; eauto; cbn [List.In]; try tauto; intros *;
            rewrite PositiveMap.gempty; congruence.
        Qed.
      End with_var.

      Lemma Wf_FromFlat {t} (e : Flat_expr t) : Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) e = true -> expr.Wf (FromFlat e).
      Proof using try_make_transport_base_type_cps_correct. intros H ??; apply wf_from_flat, H. Qed.

      Lemma Wf_via_flat {t} (e : Expr t)
        : (e = GeneralizeVar (e _) /\ Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) (to_flat (e _)) = true)
          -> expr.Wf e.
      Proof using try_make_transport_base_type_cps_correct. intros [H0 H1]; rewrite H0; cbv [GeneralizeVar]; apply Wf_FromFlat, H1. Qed.

      Lemma wf_to_flat'_gen
            {t}
            (e1 e2 : expr t)
            G
            (Hwf : expr.wf G e1 e2)
        : forall (ctx1 ctx2 : PositiveMap.t type)
                 (H_G_ctx : forall t v1 v2, List.In (existT _ t (v1, v2)) G
                                            -> (PositiveMap.find v1 ctx1 = Some t /\ PositiveMap.find v2 ctx2 = Some t))
                 cur_idx1 cur_idx2
                 (Hidx1 : forall p, PositiveMap.mem p ctx1 = true -> BinPos.Pos.lt p cur_idx1)
                 (Hidx2 : forall p, PositiveMap.mem p ctx2 = true -> BinPos.Pos.lt p cur_idx2),
          Flat.wf (ident:=ident) (base_type_beq:=base_type_beq) ctx1 (to_flat' e1 cur_idx1) = true
          /\ Flat.wf (base_type_beq:=base_type_beq) ctx2 (to_flat' e2 cur_idx2) = true.
      Proof using try_make_transport_base_type_cps_correct.
        setoid_rewrite PositiveMap.mem_find; induction Hwf;
          repeat first [ progress cbn [Flat.wf to_flat' option_map projT1 projT2 List.In fst snd eq_rect] in *
                       | progress intros
                       | destructure_step
                       | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                       | congruence
                       | lazymatch goal with
                         | [ H : BinPos.Pos.lt ?x ?x |- _ ] => exfalso; clear -H; lia
                         | [ H : BinPos.Pos.lt (BinPos.Pos.succ ?x) ?x |- _ ] => exfalso; clear -H; lia
                         | [ H : BinPos.Pos.lt ?x ?y, H' : BinPos.Pos.lt ?y ?x |- _ ] => exfalso; clear -H H'; lia
                         | [ H : BinPos.Pos.lt ?x ?y |- BinPos.Pos.lt ?x (Pos.succ ?y) ] => clear -H; lia
                         | [ |- BinPos.Pos.lt _ _ ] => progress saturate_pos
                         end
                       | match goal with
                         | [ H : ?x = Some _ |- context[?x] ] => rewrite H
                         | [ H : ?x = None |- context[?x] ] => rewrite H
                         | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                         | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
                         | [ H : In _ ?G2, H' : forall t v1 v2, In _ ?G2 -> _ |- _ ] => apply H' in H
                         | [ H : match ?x with Some _ => true | None => false end = true |- _ ]
                           => destruct x eqn:?; try discriminate
                         | [ H : match ?x with Some _ => false | None => true end = true |- _ ]
                           => destruct x eqn:?; try discriminate
                         | [ H : context[PositiveMap.E.eq_dec ?x ?y] |- (?x < Pos.succ ?y)%positive ]
                           => destruct (PositiveMap.E.eq_dec x y); [ subst; clear; lia | ]
                         end
                       | progress rewrite_find_add
                       | destructure_destruct_step
                       | progress saturate_pos_fast
                       | match goal with
                         | [ H : context[Flat.wf _ _ = true /\ Flat.wf _ _ = true] |- Flat.wf _ _ = true /\ Flat.wf _ _ = true ]
                           => eapply H; clear H; eauto with nocore
                         | [ |- (?f = true /\ ?x = true) /\ (?f' = true /\ ?x' = true) ]
                           => cut ((f = true /\ f' = true) /\ (x = true /\ x' = true));
                              [ tauto | split ]
                         | [ |- BinPos.Pos.lt _ _ ]
                           => repeat match goal with
                                     | [ H : ?T, H' : ?T |- _ ] => clear H'
                                     | [ H : BinPos.Pos.lt _ _ |- _ ] => revert H
                                     | [ H : _ |- _ ] => clear H
                                     end;
                              lia
                         end
                       | apply conj ].
      Qed.

      Lemma wf_to_flat
            {t}
            (e1 e2 : expr t)
        : expr.wf (ident:=ident) nil e1 e2 -> Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) (to_flat e1) = true /\ Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) (to_flat e2) = true.
      Proof using try_make_transport_base_type_cps_correct.
        intro; apply wf_to_flat'_gen with (G:=nil); eauto; intros *; cbn [In];
          rewrite ?PositiveMap.mem_find, ?PositiveMap.gempty; intuition congruence.
      Qed.

      Lemma Wf_ToFlat {t} (e : Expr (ident:=ident) t) (Hwf : expr.Wf e) : Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) (ToFlat e) = true.
      Proof using try_make_transport_base_type_cps_correct. eapply wf_to_flat, Hwf. Qed.

      Lemma Wf_FromFlat_to_flat {t} (e : expr t) : expr.wf (ident:=ident) nil e e -> expr.Wf (FromFlat (to_flat e)).
      Proof using try_make_transport_base_type_cps_correct. intro Hwf; eapply Wf_FromFlat, wf_to_flat, Hwf. Qed.
      Lemma Wf_FromFlat_ToFlat {t} (e : Expr t) : expr.Wf (ident:=ident) e -> expr.Wf (FromFlat (ToFlat e)).
      Proof using try_make_transport_base_type_cps_correct. intro H; apply Wf_FromFlat_to_flat, H. Qed.
      Lemma Wf_GeneralizeVar {t} (e : Expr t) : expr.Wf (ident:=ident) e -> expr.Wf (GeneralizeVar (e _)).
      Proof using try_make_transport_base_type_cps_correct. apply Wf_FromFlat_ToFlat. Qed.

      Local Ltac t :=
        repeat first [ reflexivity
                     | progress saturate_pos
                     | progress cbn [from_flat to_flat' projT1 projT2 fst snd eq_rect expr.interp List.In type.eqv] in *
                     | progress fold @type.interp
                     | progress cbv [Option.bind LetIn.Let_In respectful] in *
                     | destructure_step
                     | progress rewrite_type_transport_correct
                     | progress intros
                     | congruence
                     | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                     | progress cbn [type.app_curried type.for_each_lhs_of_arrow] in *
                     | destructure_split_step
                     | match goal with
                       (*| [ |- ident.interp _ == ident.interp _ ] => apply ident.eqv_Reflexive*)
                       | [ H : forall x : prod _ _, _ |- _ ] => specialize (fun a b => H (a, b))
                       | [ H : In _ ?G2, H' : forall t v1 v2, In _ ?G2 <-> _ |- _ ] => rewrite H' in H
                       | [ H : In _ ?G2, H' : forall t v1 v2, In _ ?G2 -> _ |- _ ] => apply H' in H
                       | [ H' : forall t v1 v2, In _ ?G2 <-> _ |- context[In _ ?G2] ] => rewrite H'
                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ] => assert (a = b) by congruence; clear H'
                       | [ H : BinPos.Pos.lt ?x ?x |- _ ] => exfalso; lia
                       | [ H : BinPos.Pos.lt (BinPos.Pos.succ ?x) ?x |- _ ] => exfalso; lia
                       | [ |- BinPos.Pos.lt _ _ ] => lia
                       | [ |- context[PositiveMap.find _ (PositiveMap.add _ _ _)] ] => rewrite PositiveMapAdditionalFacts.gsspec
                       | [ H : context[PositiveMap.find _ (PositiveMap.add _ _ _)] |- _ ] => rewrite PositiveMapAdditionalFacts.gsspec in H
                       | [ |- _ \/ None = Some _ ] => left
                       | [ |- Some _ = Some _ ] => apply f_equal
                       | [ |- existT _ ?x _ = existT _ ?x _ ] => apply f_equal
                       | [ |- pair _ _ = pair _ _ ] => apply f_equal2
                       | [ H : context[type.related _ (expr.interp _ _) (expr.interp _ _)] |- type.related _ (expr.interp _ _) (expr.interp _ _) ] => eapply H; clear H; solve [ t ]
                       end ].
      Section gen2.
        Context {base_interp : base_type -> Type}
                {ident_interp1 ident_interp2 : forall t, ident t -> type.interp base_interp t}
                {R : forall t, relation (base_interp t)}
                {ident_interp_Proper : forall t, (eq ==> type.related R)%signature (ident_interp1 t) (ident_interp2 t)}.

        Lemma interp_gen2_from_flat_to_flat'
              {t} (e1 : expr t) (e2 : expr t) G ctx
              (H_ctx_G : forall t v1 v2, List.In (existT _ t (v1, v2)) G
                                         -> (exists v2', PositiveMap.find v1 ctx = Some (existT _ t v2') /\ type.related R v2' v2))
              (Hwf : expr.wf G e1 e2)
              cur_idx
              (Hidx : forall p, PositiveMap.mem p ctx = true -> BinPos.Pos.lt p cur_idx)
          : type.related R (expr.interp ident_interp1 (from_flat (to_flat' e1 cur_idx) _ ctx)) (expr.interp ident_interp2 e2).
        Proof using try_make_transport_base_type_cps_correct ident_interp_Proper.
          setoid_rewrite PositiveMap.mem_find in Hidx.
          revert dependent cur_idx; revert dependent ctx; induction Hwf; intros;
            t.
        Qed.

        Lemma Interp_gen2_FromFlat_ToFlat {t} (e : Expr t) (Hwf : expr.Wf e)
          : type.related R (expr.Interp ident_interp1 (FromFlat (ToFlat e))) (expr.Interp ident_interp2 e).
        Proof using try_make_transport_base_type_cps_correct ident_interp_Proper.
          cbv [expr.Interp FromFlat ToFlat to_flat].
          apply interp_gen2_from_flat_to_flat' with (G:=nil); eauto; intros *; cbn [List.In]; rewrite ?PositiveMap.mem_find, ?PositiveMap.gempty;
            intuition congruence.
        Qed.

        Lemma Interp_gen2_GeneralizeVar {t} (e : Expr t) (Hwf : expr.Wf e)
          : type.related R (expr.Interp ident_interp1 (GeneralizeVar (e _))) (expr.Interp ident_interp2 e).
        Proof using ident_interp_Proper try_make_transport_base_type_cps_correct. apply Interp_gen2_FromFlat_ToFlat, Hwf. Qed.
      End gen2.
      Section gen1.
        Context {base_interp : base_type -> Type}
                {ident_interp : forall t, ident t -> type.interp base_interp t}
                {R : forall t, relation (base_interp t)}
                {ident_interp_Proper : forall t, Proper (eq ==> type.related R) (ident_interp t)}.

        Lemma interp_gen1_from_flat_to_flat'
              {t} (e1 : expr t) (e2 : expr t) G ctx
              (H_ctx_G : forall t v1 v2, List.In (existT _ t (v1, v2)) G
                                         -> (exists v2', PositiveMap.find v1 ctx = Some (existT _ t v2') /\ type.related R v2' v2))
              (Hwf : expr.wf G e1 e2)
              cur_idx
              (Hidx : forall p, PositiveMap.mem p ctx = true -> BinPos.Pos.lt p cur_idx)
          : type.related R (expr.interp ident_interp (from_flat (to_flat' e1 cur_idx) _ ctx)) (expr.interp ident_interp e2).
        Proof using ident_interp_Proper try_make_transport_base_type_cps_correct. apply @interp_gen2_from_flat_to_flat' with (G:=G); eassumption. Qed.

        Lemma Interp_gen1_FromFlat_ToFlat {t} (e : Expr t) (Hwf : expr.Wf e)
          : type.related R (expr.Interp ident_interp (FromFlat (ToFlat e))) (expr.Interp ident_interp e).
        Proof using ident_interp_Proper try_make_transport_base_type_cps_correct. apply @Interp_gen2_FromFlat_ToFlat; eassumption. Qed.

        Lemma Interp_gen1_GeneralizeVar {t} (e : Expr t) (Hwf : expr.Wf e)
          : type.related R (expr.Interp ident_interp (GeneralizeVar (e _))) (expr.Interp ident_interp e).
        Proof using ident_interp_Proper try_make_transport_base_type_cps_correct. apply @Interp_gen2_GeneralizeVar; eassumption. Qed.
      End gen1.
    End with_base_type.
  End GeneralizeVar.

  Ltac prove_Wf_with extra_tac :=
    lazymatch goal with
    | [ |- @expr.Wf ?base_type ?ident ?t ?e ]
      => refine (@GeneralizeVar.Wf_via_flat base_type ident _ _ _ _ _ t e _);
         [ solve [ assumption | auto with nocore | typeclasses eauto | extra_tac ()
                   | let G := match goal with |- ?G => G end in
                     fail 1 "Could not automatically solve" G ]..
         | vm_cast_no_check (conj (eq_refl e) (eq_refl true)) ]
    end.

  Ltac prove_Wf _ := prove_Wf_with ltac:(fun _ => idtac).

  Ltac prove_Wf3_with extra_tac := apply expr.Wf3_of_Wf; prove_Wf_with extra_tac.
  Ltac prove_Wf3 _ := prove_Wf3_with ltac:(fun _ => idtac).

  Ltac prove_Wf4_with extra_tac := apply expr.Wf4_of_Wf; prove_Wf_with extra_tac.
  Ltac prove_Wf4 _ := prove_Wf4_with ltac:(fun _ => idtac).

  Global Hint Extern 0 (?x == ?x) => apply expr.Wf_Interp_Proper_gen : wf interp.
  #[global] Hint Resolve GeneralizeVar.Wf_FromFlat_ToFlat GeneralizeVar.Wf_GeneralizeVar : wf.
  #[global] Hint Opaque GeneralizeVar.FromFlat GeneralizeVar.ToFlat GeneralizeVar.GeneralizeVar : wf interp rewrite.
  #[global] Hint Rewrite @GeneralizeVar.Interp_gen1_GeneralizeVar @GeneralizeVar.Interp_gen1_FromFlat_ToFlat : interp.
End Compilers.
