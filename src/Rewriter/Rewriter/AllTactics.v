Require Import Coq.Classes.Morphisms.
Require Import Rewriter.Language.Pre.
Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Inversion.
Require Import Rewriter.Language.Wf.
Require Import Rewriter.Language.UnderLetsProofs.
Require Import Rewriter.Language.IdentifiersLibrary.
Require Import Rewriter.Language.IdentifiersLibraryProofs.
Require Import Rewriter.Language.IdentifiersGenerate.
Require Import Rewriter.Language.IdentifiersGenerateProofs.
Require Import Rewriter.Language.IdentifiersBasicLibrary.
Require Import Rewriter.Language.IdentifiersBasicGenerate.
Require Import Rewriter.Rewriter.Rewriter.
Require Import Rewriter.Rewriter.Reify.
Require Import Rewriter.Rewriter.ProofsCommon.
Require Import Rewriter.Rewriter.ProofsCommonTactics.
Require Import Rewriter.Rewriter.Wf.
Require Import Rewriter.Rewriter.InterpProofs.
Require Import Rewriter.Util.Tactics.Head.
Require Import Rewriter.Util.Tactics.CacheTerm.
Require Import Rewriter.Util.Tactics.ConstrFail.

Module Compilers.
  Import Language.Wf.Compilers.
  Import IdentifiersLibrary.Compilers.
  Import IdentifiersBasicLibrary.Compilers.
  Import IdentifiersBasicGenerate.Compilers.
  Import IdentifiersGenerate.Compilers.
  Import IdentifiersGenerateProofs.Compilers.
  Import IdentifiersLibraryProofs.Compilers.
  Import Rewriter.Compilers.RewriteRules.
  Import Rewriter.Reify.Compilers.RewriteRules.
  Import Rewriter.ProofsCommon.Compilers.
  Import Rewriter.ProofsCommon.Compilers.RewriteRules.
  Import Rewriter.ProofsCommonTactics.Compilers.RewriteRules.
  Import Rewriter.Wf.Compilers.RewriteRules.
  Import Rewriter.InterpProofs.Compilers.RewriteRules.
  Import Rewriter.Compilers.RewriteRules.GoalType.
  Import Rewriter.ProofsCommon.Compilers.RewriteRules.GoalType.
  Import Rewriter.ProofsCommon.Compilers.RewriteRules.WfTactics.GoalType.
  Import Rewriter.ProofsCommon.Compilers.RewriteRules.InterpTactics.GoalType.
  Import Rewriter.ProofsCommonTactics.Compilers.RewriteRules.WfTactics.Tactic.
  Import Rewriter.ProofsCommonTactics.Compilers.RewriteRules.InterpTactics.Tactic.

  Module Import RewriteRules.
    Import Compilers.Basic.GoalType.
    Import Compilers.pattern.ident.GoalType.
    Import Compilers.pattern.ProofGoalType.
    Import Compilers.Classes.

    (* TODO: Move me? *)
    Local Ltac fuse_if b tf :=
      lazymatch (eval cbv beta in tf) with
      | (?x, ?x) => x
      | ((fun x : ?ty => @?T x), (fun y : ?ty' => @?F y))
        => let x' := fresh in
           constr:(fun x' : ty
                   => ltac:(let res := fuse_if b (T x', F x') in
                            exact res))
      | (?F ?X, ?G ?Y)
        => let TF := type of F in
           let TG := type of G in
           let eq_ty := match goal with
                        | _ => let __ := match goal with _ => unify TF TG end in
                               true
                        | _ => false
                        end in
           lazymatch eq_ty with
           | true
             => let f := fuse_if b (F, G) in
                let x := fuse_if b (X, Y) in
                constr:(f x)
           | false
             => constr:(if b then F X else G Y)
           end
      | (?T, ?F) => constr:(if b then T else F)
      end.
    Local Ltac do_fuse_if :=
      repeat match goal with
             | [ |- context[match ?b with true => ?T | false => ?F end] ]
               => let v := fuse_if b (T, F) in
                  progress replace (if b then T else F) with v by (now case b)
             end.

    Definition VerifiedRewriter_of_Rewriter
               {exprInfo : ExprInfoT}
               {exprExtraInfo : ExprExtraInfoT}
               {exprReifyInfo : ExprReifyInfoT}
               {pkg : package}
               {pkg_proofs : package_proofs}
               (R : RewriterT)
               (RWf : Wf_GoalT R)
               (RInterp : Interp_GoalT R)
               (RProofs : PrimitiveHList.hlist
                            (@snd bool Prop)
                            (List.skipn (dummy_count (Rewriter_data R)) (rewrite_rules_specs (Rewriter_data R))))
      : VerifiedRewriter.
    Proof.
      simple refine
             (let HWf := _ in
              let HInterp_gen := _ in
              @Build_VerifiedRewriter exprInfo exprReifyInfo RewriterOptions default_rewriter_options (fun opts => @Rewriter.Compilers.RewriteRules.GoalType.Rewrite exprInfo exprExtraInfo pkg R (use_decision_tree opts) (use_precomputed_functions opts)) HWf HInterp_gen _ _ (@GeneralizeVar.Wf_via_flat _ ident _ _ _ _ _));
        [ | clear HWf ]; intros.
      all: abstract (
               rewrite Rewrite_eq; cbv [Make.Rewrite rewrite_head_gen];
               rewrite rewrite_head_eq, rewrite_head_no_dtree_eq;
               cbv [rewrite_head0 rewrite_head_no_dtree0];
               rewrite Bool.if_const;
               do_fuse_if;
               rewrite all_rewrite_rules_eq, ?eq_invert_bind_args_unknown, ?eq_unify_unknown;
               first [ apply (Compile.Wf_Rewrite _); [ | assumption ];
                       let wf_do_again := fresh "wf_do_again" in
                       (intros ? ? ? ? wf_do_again ? ?);
                       eapply @Compile.wf_assemble_identifier_rewriters;
                       eauto using
                             pattern.Raw.ident.to_typed_invert_bind_args, pattern.ident.eta_ident_cps_correct,
                       eq_refl
                         with nocore typeclass_instances
                     | apply (Compile.InterpRewrite _); [ | assumption ];
                       intros; eapply Compile.interp_assemble_identifier_rewriters with (pident_to_typed:=@to_typed);
                       eauto using
                             (pattern.ident.unify_to_typed (pkg:=pkg)), pattern.Raw.ident.to_typed_invert_bind_args, pattern.ident.eta_ident_cps_correct,
                       eq_refl
                         with nocore ]
             ).
    Defined.

    Ltac make_VerifiedRewriter exprInfo exprExtraInfo exprReifyInfo pkg pkg_proofs R RWf RInterp RProofs :=
      let res := (eval hnf in (@VerifiedRewriter_of_Rewriter exprInfo exprExtraInfo exprReifyInfo pkg pkg_proofs R RWf RInterp RProofs)) in
      let res := lazymatch res with
                 | context Res[@Build_VerifiedRewriter ?exprInfo ?exprReifyInfo ?optsT ?default_opts ?R]
                   => let t := fresh "t" in
                      let R' := fresh in
                      let R' := constr:(fun t
                                        => match R t return _ with
                                           | R' => ltac:(let v := (eval hnf in R') in exact v)
                                           end) in
                      context Res[@Build_VerifiedRewriter exprInfo exprReifyInfo optsT default_opts R']
                 end in
      res.

    Ltac Build_Rewriter basic_package pkg_proofs include_interp skip_early_reduction skip_early_reduction_no_dtree specs_proofs :=
      let basic_package := (eval hnf in basic_package) in
      let exprInfo := (eval hnf in (Basic.GoalType.exprInfo basic_package)) in
      let exprExtraInfo := (eval hnf in (Basic.GoalType.exprExtraInfo basic_package)) in
      let exprReifyInfo := (eval hnf in (Basic.GoalType.exprReifyInfo basic_package)) in
      let ident_is_var_like := lazymatch basic_package with {| Basic.GoalType.ident_is_var_like := ?ident_is_var_like |} => ident_is_var_like end in
      let reify_package := Basic.Tactic.reify_package_of_package basic_package in
      let reify_base := Basic.Tactic.reify_base_via_reify_package reify_package in
      let reify_ident := Basic.Tactic.reify_ident_via_reify_package reify_package in
      let pkg_proofs_type := type of pkg_proofs in
      let pkg := lazymatch (eval hnf in pkg_proofs_type) with @package_proofs ?base ?ident ?pkg => pkg end in
      let specs := lazymatch type of specs_proofs with
                   | PrimitiveHList.hlist (@snd bool Prop) ?specs => specs
                   | ?T
                     => let expected_type := uconstr:(PrimitiveHList.hlist (@snd bool Prop) ?[specs]) in
                        constr_fail_with ltac:(fun _ => fail 1 "Invalid type for specs_proofs:" T "Expected:" expected_type)
                   end in
      let R_name := fresh "Rewriter_data" in
      let R := Build_RewriterT reify_base reify_ident exprInfo exprExtraInfo pkg ident_is_var_like include_interp skip_early_reduction skip_early_reduction_no_dtree specs in
      let R := cache_term R R_name in
      let __ := Make.debug1 ltac:(fun _ => idtac "Proving Rewriter_Wf...") in
      let Rwf := fresh "Rewriter_Wf" in
      let Rwf := cache_proof_with_type_by (@Wf_GoalT exprInfo exprExtraInfo pkg R) ltac:(idtac; prove_good ()) Rwf in
      let __ := Make.debug1 ltac:(fun _ => idtac "Proving Rewriter_Interp...") in
      let RInterp := fresh "Rewriter_Interp" in
      let RInterp := cache_proof_with_type_by (@Interp_GoalT exprInfo exprExtraInfo pkg R) ltac:(idtac; prove_interp_good ()) RInterp in
      let __ := Make.debug1 ltac:(fun _ => idtac "Assembling verified rewriter...") in
      make_VerifiedRewriter exprInfo exprExtraInfo exprReifyInfo pkg pkg_proofs R Rwf RInterp specs_proofs.

    Module Import FinalTacticHelpers.
      Lemma generalize_to_eqv {base_type base_interp} {A B f g}
            (H : @type.related base_type base_interp (fun _ => eq) (type.arrow A B) f g)
        : forall x, Proper (@type.eqv A) x -> f x == g x.
      Proof. intro; apply H. Qed.

      Lemma eq_trans_eqv {base_type base_interp T x y z}
            (H1 : x = y)
            (H2 : @type.related base_type base_interp (fun _ => eq) T y z)
        : x == z.
      Proof. subst; assumption. Qed.

      Lemma eq_trans_eqv_Interp {base_type base_interp ident ident_interp T x y z}
            (H2 : @type.related base_type base_interp (fun _ => eq) T (@expr.Interp base_type ident base_interp ident_interp T y) z)
            (H1 : x = y)
        : (@expr.Interp base_type ident base_interp ident_interp T x) == z.
      Proof. subst; assumption. Qed.

      Inductive mark := mkmark.

      Ltac generalize_hyps_for_rewriting_step base reify_type base_interp base_type base_type_interp do_again :=
        lazymatch goal with
        | [ |- @eq ?T ?x ?y ] => let t := reify_type T in
                                 change (@type.related _ base_type_interp (fun _ => eq) t x y)
        | [ H := _ |- _ ] => clear H || revert H || move H at top (* if H is a section variable which is used in the goal *)
        | [ H : ?T |- @type.related _ base_type_interp (fun _ => eq) ?B _ _ ]
          => lazymatch goal with
             | [ |- context[H] ]
               => let t := reify_type T in
                  generalize (_ : Proper (@type.related _ base_type_interp (fun _ => eq) t) H);
                  revert H;
                  refine (@generalize_to_eqv _ base_type_interp t B _ _ _)
             | _ => lazymatch T with
                    | mark => (* now we're done *) idtac
                    | _ => (clear H || move H at top);
                           do_again ()
                    end
             end
        | [ |- _ ] => (* now we're done *) idtac
        end.

      Ltac generalize_hyps_for_rewriting base reify_type base_interp :=
        let base_type := constr:(base.type base) in
        let base_type_interp := constr:(base.interp base_interp) in
        let step := generalize_hyps_for_rewriting_step base reify_type base_interp base_type base_type_interp in
        let just_step _ := step ltac:(fun _ => idtac) in
        let rec repeat_step _ := step repeat_step in
        (*let reify_base_type T := base.reify base reify_base T in
        let reify_type T := type.reify reify_base_type (base.type base) T in*)
        intros;
        let H := fresh in
        pose proof mkmark as H;
        move H at top;
        (* use [repeat] first so we don't blow the stack *)
        repeat just_step ();
        (* use recursion to get nice error messages *)
        repeat_step ().

      Ltac etransitivity_for_sides do_lhs do_rhs :=
        intros;
        lazymatch goal with
        | [ |- _ = _ ] => idtac
        | [ |- ?G ] => fail "The goal" G "is not an equality"
        end;
        (* we keep the original goal at the beginning of the goals list *)
        (* there's only one goal at this point, but we use branching
           with [..] to be more symmetric between treating lhs and
           rhs *)
        [ lazymatch do_lhs with
          | true => etransitivity; revgoals; [ | symmetry ]
          | false => idtac
          end | .. ];
        [ lazymatch do_rhs with
          | true => etransitivity
          | false => idtac
          end | .. ];
        [ shelve (* shelve the original goal *) | .. ].

      Ltac check_perf_level_then_tac tac arg :=
        let lvl := rewrite_perf_level in
        lazymatch type of lvl with
        | nat => tac arg
        | ?T => let natT := constr:(nat) in
                fail 0 "Error: rewrite_perf_level should have type" natT "but instead has type" T
        end.

      Ltac time_if_perf1 time_tac tac arg :=
        let lvl := rewrite_perf_level in
        lazymatch lvl with
        | S _ => time_tac tac arg
        | _ => check_perf_level_then_tac tac arg
        end.

      Ltac time_if_perf2 time_tac tac arg :=
        let lvl := rewrite_perf_level in
        lazymatch lvl with
        | S (S _) => time_tac tac arg
        | _ => check_perf_level_then_tac tac arg
        end.

      Ltac time_if_perf3 time_tac tac arg :=
        let lvl := rewrite_perf_level in
        lazymatch lvl with
        | S (S (S _)) => time_tac tac arg
        | _ => check_perf_level_then_tac tac arg
        end.

      Ltac do_reify_rhs_with verified_rewriter_package :=
        idtac;
        let time_ntcrefine := fun tac arg => time "do_reify_rhs_with:notypeclasses_refine" tac arg in
        let time_reify := fun tac arg => time "do_reify_rhs_with:reify_hint" tac arg in
        let exprInfo := (eval hnf in (RewriteRules.GoalType.exprInfo verified_rewriter_package)) in
        let exprReifyInfo := (eval hnf in (RewriteRules.GoalType.exprReifyInfo verified_rewriter_package)) in
        lazymatch exprInfo with
        | {| Classes.ident := ?ident
             ; Classes.ident_interp := ?ident_interp |}
          => time_if_perf3 time_ntcrefine ltac:(fun _ => notypeclasses refine (@expr.Reify_rhs _ ident _ ident_interp _ _ _ _ _ _)) ();
             [ time_if_perf3 time_reify Basic.Tactic.expr_reified_hint_via_reify_package exprReifyInfo | ]
        end.

      Ltac prove_Wf_with verified_rewriter_package :=
        let time_refine := fun tac arg => time "prove_Wf_with:refine" tac arg in
        let time_vm_compute := fun tac arg => time "prove_Wf_with:vm_compute" tac arg in
        let time_split := fun tac arg => time "prove_Wf_with:split" tac arg in
        let time_reflexivity := fun tac arg => time "prove_Wf_with:reflexivity" tac arg in
        time_if_perf3 time_refine ltac:(fun _ => refine (@prove_Wf verified_rewriter_package _ _ _)) ();
        time_if_perf3 time_vm_compute ltac:(fun _ => rewrite_default_red_tactic) ();
        time_if_perf3 time_split ltac:(fun _ => split) ();
        time_if_perf3 time_reflexivity ltac:(fun _ => reflexivity) ().

      Ltac do_rewrite_with verified_rewriter_package :=
        let time_trans := fun tac arg => time "do_rewrite_with:refine_trans" tac arg in
        let time_refine_interp_rewrite := fun tac arg => time "do_rewrite_with:refine_interp_rewrite" tac arg in
        let time_prove_Wf := fun tac arg => time "prove_Wf" tac arg in
        let time_vm_unif := fun tac arg => time "vm_compute_and_unify_in_rewrite" tac arg in
        let time_vm_cast_no_check := fun tac arg => time "do_rewrite_with:vm_cast_no_check" tac arg in
        time_if_perf3 time_trans ltac:(fun _ => refine (eq_trans_eqv_Interp _ _)) ();
        [ time_if_perf3 time_refine_interp_rewrite ltac:(fun _ => refine (@Interp_Rewrite verified_rewriter_package (@default_opts verified_rewriter_package) _ _ _)) ();
          [ .. | time_if_perf2 time_prove_Wf prove_Wf_with verified_rewriter_package ]
        | lazymatch goal with
          | [ |- ?ev = ?RHS ]
            => time_if_perf2
                 time_vm_unif
                 ltac:(fun _ =>
                         let RHS' := rewrite_default_eval_red RHS in
                         unify ev RHS') ();
               time_if_perf3 time_vm_cast_no_check ltac:(fun _ => rewrite_default_cast_no_check (eq_refl RHS)) ()
          end ].

      Ltac do_final_cbv verified_rewriter_package base_interp ident_interp :=
        idtac;
        let base_interp_head := head base_interp in
        let ident_interp_head := head ident_interp in
        let verified_rewriter_package_head := head verified_rewriter_package in
        cbv [expr.Interp expr.interp Classes.ident_interp Classes.base GoalType.exprInfo type.interp base.interp base_interp_head ident_interp_head verified_rewriter_package_head ident.literal ident.eagerly].

      Ltac Rewrite_for_gen verified_rewriter_package skip_cbv do_lhs do_rhs :=
        once
          (idtac;
           let time_all := lazymatch skip_cbv with
                           | false => fun tac arg => time "Rewrite_for_gen" tac arg
                           | true => fun tac arg => time "Rewrite_for_gen_skip_cbv" tac arg
                           end in
           let time_etrans := fun tac arg => time "Rewrite_for_gen:etransitivity_for_sides" tac arg in
           let time_generalize := fun tac arg => time "Rewrite_for_gen:generalize_hyps_for_rewriting" tac arg in
           let time_reify := fun tac arg => time "reification" tac arg in
           let time_do_rewrite := fun tac arg => time "rewriting" tac arg in
           let time_cbv := fun tac arg => time "final_cbv" tac arg in
           time_if_perf1
             time_all
             ltac:(fun _ =>
                     lazymatch (eval hnf in (RewriteRules.GoalType.exprInfo verified_rewriter_package)) with
                     | {| base := ?base
                          ; ident := ?ident
                          ; base_interp := ?base_interp
                          ; ident_interp := ?ident_interp
                       |}
                       => let base_type := constr:(base.type base) in
                          let base_type_interp := constr:(base.interp base_interp) in
                          let reify_type := Basic.Tactic.reify_type_via_reify_package (RewriteRules.GoalType.exprReifyInfo verified_rewriter_package) in
                          unshelve (
                              time_if_perf3 time_etrans ltac:(fun _ => etransitivity_for_sides do_lhs do_rhs) ();
                              time_if_perf3 time_generalize ltac:(fun _ => generalize_hyps_for_rewriting base reify_type base_interp) ();
                              time_if_perf1 time_reify do_reify_rhs_with verified_rewriter_package;
                              time_if_perf1 time_do_rewrite do_rewrite_with verified_rewriter_package;
                              let n := numgoals in
                              guard n = 0 (* assert that all goals are solved; we don't use [solve] because it eats error messages of inner tactics *));
                          lazymatch skip_cbv with
                          | true => idtac
                          | false => time_if_perf2 time_cbv ltac:(fun _ => do_final_cbv verified_rewriter_package base_interp ident_interp) ()
                          end
                     end) ()).
    End FinalTacticHelpers.

    Module Export GoalType.
      Export Rewriter.ProofsCommon.Compilers.RewriteRules.GoalType.
    End GoalType.

    Module Export Tactic.
      Module Export Settings.
        Export Rewriter.Reify.Compilers.RewriteRules.Tactic.Settings.
      End Settings.

      Ltac make_rewriter_via basic_package pkg_proofs include_interp skip_early_reduction skip_early_reduction_no_dtree specs_proofs :=
        let res := Build_Rewriter basic_package pkg_proofs include_interp skip_early_reduction skip_early_reduction_no_dtree specs_proofs in
        let __ := Make.debug1 ltac:(fun _ => idtac "Refining with verified rewriter...") in
        refine res.

      Ltac make_rewriter :=
        idtac;
        lazymatch goal with
        | [ |- GoalType.VerifiedRewriter_with_args ?basic_package ?pkg_proofs ?include_interp ?skip_early_reduction ?skip_early_reduction_no_dtree ?specs_proofs ]
          => cbv [GoalType.VerifiedRewriter_with_args];
             make_rewriter_via basic_package pkg_proofs include_interp skip_early_reduction skip_early_reduction_no_dtree specs_proofs
        end.

      Tactic Notation "make_rewriter_via" constr(basic_package) constr(pkg_proofs) constr(include_interp) constr(skip_early_reduction) constr(skip_early_reduction_no_dtree) constr(specs_proofs) :=
        make_rewriter_via basic_package pkg_proofs include_interp skip_early_reduction skip_early_reduction_no_dtree specs_proofs.

      Ltac make_rewriter_from_scraped scraped_data var_like_idents base ident raw_ident pattern_ident include_interp skip_early_reduction skip_early_reduction_no_dtree specs_proofs :=
        let basic_package := Basic.Tactic.cache_build_package_of_scraped scraped_data var_like_idents base ident in
        let pattern_package := Compilers.pattern.ident.Tactic.cache_build_package basic_package raw_ident pattern_ident in
        let pkg_proofs := Compilers.pattern.ProofTactic.cache_build_package_proofs basic_package pattern_package in
        make_rewriter_via basic_package pkg_proofs include_interp skip_early_reduction skip_early_reduction_no_dtree specs_proofs.

      Ltac make_rewriter_all :=
        idtac;
        lazymatch goal with
        | [ |- GoalType.VerifiedRewriter_with_ind_args ?scraped_data ?var_like_idents ?base ?ident ?raw_ident ?pattern_ident ?include_interp ?skip_early_reduction ?skip_early_reduction_no_dtree ?specs_proofs ]
          => cbv [GoalType.VerifiedRewriter_with_ind_args];
             make_rewriter_from_scraped scraped_data var_like_idents base ident raw_ident pattern_ident include_interp skip_early_reduction skip_early_reduction_no_dtree specs_proofs
        end.

      Module Export Hints.
        Global Hint Extern 0 (GoalType.VerifiedRewriter_with_ind_args _ _ _ _ _ _ _ _ _ _) => make_rewriter_all : typeclass_instances.
      End Hints.

      Ltac Rewrite_lhs_for verified_rewriter_package := Rewrite_for_gen verified_rewriter_package false true false.
      Ltac Rewrite_rhs_for verified_rewriter_package := Rewrite_for_gen verified_rewriter_package false false true.
      Ltac Rewrite_for verified_rewriter_package := Rewrite_for_gen verified_rewriter_package false true true.
      Ltac Rewrite_lhs_for_skip_cbv verified_rewriter_package := Rewrite_for_gen verified_rewriter_package true true false.
      Ltac Rewrite_rhs_for_skip_cbv verified_rewriter_package := Rewrite_for_gen verified_rewriter_package true false true.
      Ltac Rewrite_for_skip_cbv verified_rewriter_package := Rewrite_for_gen verified_rewriter_package true true true.
    End Tactic.
  End RewriteRules.
End Compilers.
