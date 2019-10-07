(* -*- coq-prog-args: ("-debug") -*- *)
Require Import Crypto.Language.IdentifiersBasicLibrary.
Require Import Crypto.Language.IdentifiersBasicGenerate.
Require Import Crypto.Language.Pre.
Require Import Crypto.Rewriter.ProofsCommon.
Require Import Crypto.Rewriter.AllTactics.
Require Import Crypto.Util.Notations.
Import IdentifiersBasicLibrary.Compilers.
Import IdentifiersBasicGenerate.Compilers.
Import ProofsCommon.Compilers.
Import AllTactics.Compilers.

Register Basic.GoalType.package_with_args as rewriter.basic_package_with_args.type.
Register Basic.GoalType.base_elim_with_args as rewriter.base_elim_with_args.type.
Register Basic.GoalType.ident_elim_with_args as rewriter.ident_elim_with_args.type.
Register Basic.GoalType.ident_elim_with_args as rewriter.pattern_ident_elim_with_args.type.
Register Basic.GoalType.ident_elim_with_args as rewriter.raw_ident_elim_with_args.type.
Register ScrapedData.t_with_args as rewriter.scraped_data_with_args.type.
Register rules_proofsT_with_args as rewriter.rules_proofs_with_args.type.
Register GallinaIdentList.nil as rewriter.ident_list.nil.
Register RewriteRules.GoalType.VerifiedRewriter_with_ind_args as rewriter.verified_rewriter_with_args.type.

Ltac make_base_elim_with_args := Basic.PrintBase.make_base_elim.
Ltac make_ident_elim_with_args := Basic.PrintIdent.make_ident_elim.
Ltac make_pattern_ident_elim_with_args := Basic.PrintIdent.make_pattern_ident_elim.
Ltac make_raw_ident_elim_with_args := Basic.PrintIdent.make_raw_ident_elim.
Ltac make_basic_package_with_args := Basic.Tactic.make_package.
Ltac make_scraped_data_with_args := Basic.ScrapeTactics.make_scrape_data.
Ltac make_verified_rewriter_with_args := RewriteRules.Tactic.make_rewriter_all.
Ltac make_rules_proofs_with_args := Basic.ScrapeTactics.make_rules_proofsT_with_args.

Declare ML Module "rewriter_build_plugin".

Ltac Rewrite_lhs_for verified_rewriter_package := RewriteRules.Tactic.Rewrite_lhs_for verified_rewriter_package.
Ltac Rewrite_rhs_for verified_rewriter_package := RewriteRules.Tactic.Rewrite_rhs_for verified_rewriter_package.
Ltac Rewrite_for verified_rewriter_package := RewriteRules.Tactic.Rewrite_for verified_rewriter_package.

Export Pre.RewriteRuleNotations.
Export IdentifiersGenerateProofs.Compilers.pattern.ProofTactic.Settings.

(*
Definition myruletypes : list (bool * Prop)
  := ((all_dont_do_again
         [(forall x, x + 0 = x)
          ; (forall A B x y, @fst A B (x, y) = x)
          ; (forall A B x y, @snd A B (x, y) = y)
          ; (forall A B f ls, @List.map A B f ls
                              = (ident.eagerly (@list_rect) _ _)
                                  []
                                  (fun x xs map_f_xs => f x :: map_f_xs)
                                  ls)
          ; (forall A xs ys, @List.app A xs ys
                             = (ident.eagerly (@list_rect) _ _)
                                 ys (fun x xs app_xs_ys => x :: app_xs_ys) xs)
          ; (forall A P N C ls,
                @ident.Thunked.list_rect A P N C ls
                = ident.eagerly (@ident.Thunked.list_rect) A P N C ls)
          ; (forall A P Q N C ls v,
                @list_rect A (fun _ => P -> Q) N C ls v
                = ident.eagerly (@list_rect) A (fun _ => P -> Q) N C ls v)])
        ++ (all_do_again
              [(forall A B f xs,
                   @List.flat_map A B f xs
                   = (list_rect _)
                       nil
                       (fun x _ flat_map_tl => f x ++ flat_map_tl)
                       xs)]))%rew_rules%list.

(** Now we prove every theorem statement in the above list. *)

Lemma myruleproofs
  : PrimitiveHList.hlist (@snd bool Prop) myruletypes.
Proof.
  repeat constructor; cbn [snd]; cbv [ident.eagerly]; intros;
    try solve [ Lia.lia
              | now apply ListUtil.eq_app_list_rect ].
Qed.

Definition noruletypes : list (bool * Prop)
  := []%rew_rules.

(** Now we prove every theorem statement in the above list. *)

Lemma noruleproofs
  : PrimitiveHList.hlist (@snd bool Prop) noruletypes.
Proof. repeat constructor. Qed.

Time Make norew := Rewriter For (plus_n_O, plus_O_n).
Time Time Make myrew := Rewriter For myruleproofs.
*)
