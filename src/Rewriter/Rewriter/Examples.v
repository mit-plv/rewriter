(** * Examples of Using the Rewriter *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Rewriter.Util.ListUtil.
Require Import Rewriter.Util.LetIn.
Require Import Rewriter.Util.Notations.
Require Import Rewriter.Util.plugins.RewriterBuild.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Time Make norules := Rewriter For ().

(** Now we show some simple examples. *)

Example ex1 : forall x : nat, x = x.
Proof.
  Rewrite_for norules.
  lazymatch goal with
  | |- ?x = ?x => is_var x; reflexivity
  end.
Qed.

Example ex2 : forall x : nat, id x = id x.
Proof.
  Rewrite_for norules.
  lazymatch goal with
  | |- ?x = ?x => is_var x; reflexivity
  end.
Qed.

(** ==== *)

Local Ltac t :=
  repeat constructor; cbn [snd]; cbv [ident.eagerly]; intros;
  try solve [ lia
            | now apply ListUtil.eq_app_list_rect ].

Lemma map_eagerly_rect
  : forall A B f ls, @List.map A B f ls
                     = (ident.eagerly (@list_rect) _ _)
                         []
                         (fun x xs map_f_xs => f x :: map_f_xs)
                         ls.
Proof. t. Qed.

Lemma app_eagerly_rect
  : forall A xs ys, @List.app A xs ys
                    = (ident.eagerly (@list_rect) _ _)
                        ys (fun x xs app_xs_ys => x :: app_xs_ys) xs.
Proof. t. Qed.

Lemma flat_map_rect
  : forall A B f xs,
    @List.flat_map A B f xs
    = (list_rect (fun _ => _))
        nil
        (fun x _ flat_map_tl => f x ++ flat_map_tl)%list
        xs.
Proof. t. Qed.

Module ForDebugging.
  Definition rules_proofs :=
    Eval cbv [projT2] in
      projT2
        (ltac:(RewriterBuildRegistry.make_rules_proofs_with_args)
          : Pre.rules_proofsT_with_args
              (Z.add_0_r
                , (@Prod.fst_pair)
                , (@Prod.snd_pair)
                , map_eagerly_rect
                , app_eagerly_rect
                , eval_rect list
                , do_again flat_map_rect)).

  Definition scraped_data :=
    (ltac:(cbv [projT1]; RewriterBuildRegistry.make_scraped_data_with_args)
      : PreCommon.Pre.ScrapedData.t_with_args
          rules_proofs
          (* extra, can be anything whose subterms get added *) false).

  Rewriter Emit Inductives From Scraped scraped_data As base ident raw_ident pattern_ident.

  Definition myrules :=
    (ltac:(RewriterBuildRegistry.make_verified_rewriter_with_args)
      : ProofsCommon.Compilers.RewriteRules.GoalType.VerifiedRewriter_with_ind_args
          scraped_data InductiveHList.nil base ident raw_ident pattern_ident (* inlcude_interp: *) false (* skip_early_reduction: *) false (* skip_early_reduction_no_dtree: *) true rules_proofs).
End ForDebugging.

Time Make myrules
  := Rewriter For (Z.add_0_r
                   , (@Prod.fst_pair)
                   , (@Prod.snd_pair)
                   , map_eagerly_rect
                   , app_eagerly_rect
                   , eval_rect list
                   , do_again flat_map_rect).

(** Now we show some simple examples. *)

Example ex3 : forall x, x + 0 = x.
Proof.
  Rewrite_for myrules.
  lazymatch goal with
  | |- ?x = ?x => is_var x; reflexivity
  end.
Qed.

Ltac test_rewrite :=
  Rewrite_for myrules;
  lazymatch goal with
  | [ |- ?x = ?y ] => first [ constr_eq x y; idtac "Success:" x; reflexivity
                            | fail 1 x "≢" y ]
  end.

Example ex4 : forall y e1 e2,
    map (fun x => y + x) (dlet z := e1 + e2 in [0; 1; 2; z; z+1])
    = dlet z := e1 + e2 in [y; y + 1; y + 2; y + z; y + (z + 1)].
Proof. test_rewrite. Qed.

Example ex5 : forall (x1 x2 x3 : Z),
    flat_map (fun a => [a; a; a]) [x1;x2;x3]
    = [x1; x1; x1; x2; x2; x2; x3; x3; x3].
Proof. test_rewrite. Qed.
