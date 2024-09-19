From Coq Require Import List.
Require Import Rewriter.Language.Pre.
Require Import Rewriter.Util.Bool.
Require Import Rewriter.Util.NatUtil.
Require Import Rewriter.Util.ListUtil.
Require Import Rewriter.Util.Prod.
Require Import Rewriter.Util.Option.
Import ListNotations.

Import Pre.RewriteRuleNotations.

Lemma eval_nat_rect_arrow
  : forall A B O_case S_case n v,
    @nat_rect_arrow_nodep A B O_case S_case ('n) v
    = ident.eagerly (@nat_rect_arrow_nodep) _ _ O_case S_case ('n) v.
Proof. reflexivity. Qed.

Lemma eval_nat_rect
  : forall P O_case S_case n,
    @Thunked.nat_rect P O_case S_case ('n)
    = ident.eagerly (@Thunked.nat_rect) _ O_case S_case ('n).
Proof. reflexivity. Qed.

Lemma eval_list_rect_arrow
  : forall A P Q N C ls v,
    @list_rect_arrow_nodep A P Q N C ls v
    = ident.eagerly (@list_rect_arrow_nodep) A P Q N C ls v.
Proof. reflexivity. Qed.

Lemma eval_list_rect
  : forall A P N C ls,
    @Thunked.list_rect A P N C ls
    = ident.eagerly (@Thunked.list_rect) A P N C ls.
Proof. reflexivity. Qed.

Lemma eval_list_case_nil
  : forall A P N C, @Thunked.list_case A P N C nil = N tt.
Proof. reflexivity. Qed.
Lemma eval_list_case_cons
  : forall A P N C x xs, @Thunked.list_case A P N C (x :: xs) = C x xs.
Proof. reflexivity. Qed.

Lemma eval_list_nth_default
  : forall A default ls n,
    @List.nth_default A default ls ('n)
    = ident.eagerly (@List.nth_default) A default ls ('n).
Proof. reflexivity. Qed.

Lemma eval_prod_rect
  : forall A B P f x y, @prod_rect_nodep A B P f (x, y) = f x y.
Proof. reflexivity. Qed.

Lemma eval_option_rect_Some
  : forall A P S N x, @Thunked.option_rect A P S N (Some x) = S x.
Proof. reflexivity. Qed.
Lemma eval_option_rect_None
  : forall A P S N, @Thunked.option_rect A P S N None = N tt.
Proof. reflexivity. Qed.

Lemma eval_bool_rect_true : forall T t f, @Thunked.bool_rect T t f true = t tt.
Proof. reflexivity. Qed.
Lemma eval_bool_rect_false : forall T t f, @Thunked.bool_rect T t f false = f tt.
Proof. reflexivity. Qed.

Import PrimitiveProd.
Import Pre.RewriteRuleNotations.

Module Export Instances.
  Global Instance eval_rect_nat_rules : rules_proofs_for_eager_type nat
    := existT (PrimitiveHList.hlist (@Datatypes.snd bool Prop))
              [Types.dont_do_again _; Types.dont_do_again _]
              (@eval_nat_rect_arrow, (@eval_nat_rect, tt))%primproj.

  Global Instance eval_rect_list_rules : rules_proofs_for_eager_type list
    := existT (PrimitiveHList.hlist (@Datatypes.snd bool Prop))
              [Types.dont_do_again _; Types.dont_do_again _; Types.dont_do_again _; Types.dont_do_again _; Types.dont_do_again _]
              (@eval_list_rect_arrow, (@eval_list_rect, (@eval_list_case_nil, (@eval_list_case_cons, (@eval_list_nth_default, tt)))))%primproj.

  Global Instance eval_rect_prod_rules : rules_proofs_for_eager_type prod
    := existT (PrimitiveHList.hlist (@Datatypes.snd bool Prop))
              [Types.dont_do_again _]
              (@eval_prod_rect, tt)%primproj.

  Global Instance eval_rect_option_rules : rules_proofs_for_eager_type option
    := existT (PrimitiveHList.hlist (@Datatypes.snd bool Prop))
              [Types.dont_do_again _; Types.dont_do_again _]
              (@eval_option_rect_Some, (@eval_option_rect_None, tt))%primproj.

  Global Instance eval_rect_bool_rules : rules_proofs_for_eager_type bool
    := existT (PrimitiveHList.hlist (@Datatypes.snd bool Prop))
              [Types.dont_do_again _; Types.dont_do_again _]
              (@eval_bool_rect_true, (@eval_bool_rect_false, tt))%primproj.
End Instances.
