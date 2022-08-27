Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Require Import Rewriter.Language.PreCommon.
Require Import Rewriter.Language.Language.
Require Import Rewriter.Util.LetIn.
Require Import Rewriter.Util.ListUtil.
Require Import Rewriter.Util.Option.
Require Import Rewriter.Util.OptionList.
Require Import Rewriter.Util.Prod.
Require Import Rewriter.Util.NatUtil.
Require Import Rewriter.Util.CPSNotations.
Require Import Rewriter.Util.Bool.Reflect.
Require Import Rewriter.Util.Bool.
Require Import Rewriter.Util.ListUtil.
Require Import Rewriter.Util.Prod.
Require Import Rewriter.Util.Notations.
Require Import Rewriter.Util.Tactics.RunTacticAsConstr.
Require Import Rewriter.Util.Tactics.DebugPrint.
Require Import Rewriter.Util.Tactics.ConstrFail.
Import Coq.Lists.List ListNotations.
Export Language.PreCommon.

Local Set Primitive Projections.

Import EqNotations.
Module Compilers.
  Export Language.PreCommon.
  Export Language.Compilers.
  Module Export Exports.
    Ltac2 Type exn ::= [ Reification_failure (message) ].
    Ltac2 Type exn ::= [ Reification_panic (message) ].
  End Exports.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.

  Module Ltac1.
    (* TODO: remove or move to util *)
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac2 get_to_constr v := Option.get (Ltac1.to_constr v).
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac2 apply_c (f : Ltac1.t) (args : constr list) : constr :=
      '(ltac2:(Ltac1.apply f (List.map Ltac1.of_constr args) (fun v => Control.refine (fun () => get_to_constr v)))).
  End Ltac1.

  Module Reify.
    Ltac2 debug_level := Pre.reify_debug_level.

    Ltac2 mutable should_debug_enter_reify () := Int.le 2 debug_level.
    Ltac2 mutable should_debug_enter_reify_preprocess () := Int.le 2 debug_level.
    Ltac2 mutable should_debug_enter_reify_ident_preprocess () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_enter_reify_after_preprocess () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_leave_reify_success () := Int.le 5 debug_level.
    Ltac2 mutable should_debug_leave_reify_failure () := Int.le 0 debug_level.
    Ltac2 mutable should_debug_enter_reify_ident_after_preprocess () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_enter_lookup_ident () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_success () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_failure_verbose () := Int.le 5 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_failure () := Int.le 4 debug_level.

    Ltac2 debug_if (cond : unit -> bool) (tac : unit -> 'a) (default : 'a) :=
      if cond ()
      then tac ()
      else default.

    Ltac2 debug_enter_reify (funname : string) (e : constr)
      := debug_if should_debug_enter_reify (fun () => printf "%s: Attempting to reify: %t" funname e) ().
    Ltac2 debug_enter_reify_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_preprocess (fun () => printf "%s: Attempting to preprocess: %t" funname e) ().
    (*Ltac2 debug_enter_reify_ident_idtac (funname : string) (e : constr)
      := printf "%s: Attempting to reify (as ident): %t" funname e.*)
    Ltac2 debug_enter_reify_after_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_after_preprocess (fun () => printf "%s: Attempting to reify (post-preprocessing): %t" funname e) ().
    Ltac2 debug_enter_reify_ident_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_ident_preprocess (fun () => printf "%s: Attempting to (ident) preprocess: %t" funname e) ().
    Ltac2 debug_enter_reify_ident_after_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_ident_after_preprocess (fun () => printf "%s: Attempting to reify ident (post-preprocessing): %t" funname e) ().
    Ltac2 debug_leave_reify_success (funname : string) (e : constr) (ret : constr)
      := debug_if should_debug_leave_reify_success (fun () => printf "%s: Success in reifying: %t as %t" funname e ret) ().
    Ltac2 debug_leave_reify_failure (funname : string) (e : constr)
      := debug_if should_debug_leave_reify_failure (fun () => printf "%s: Failure in reifying: %t" funname e) ().
    Ltac2 debug_enter_lookup_ident (funname : string) (e : constr)
      := debug_if should_debug_enter_lookup_ident (fun () => printf "%s: Attempting to lookup ident: %t" funname e) ().
    Ltac2 debug_leave_lookup_ident_success (funname : string) (e : constr) (ret : constr)
      := debug_if should_debug_leave_lookup_ident_success (fun () => printf "%s: Success in looking up ident: %t as %t" funname e ret) ().
    Ltac2 debug_leave_lookup_ident_failure (funname : string) (e : constr) (ls : constr)
      := if should_debug_leave_lookup_ident_failure_verbose ()
         then printf "%s: Failure in looking up: %t (in %t)" funname e ls
         else if should_debug_leave_lookup_ident_failure ()
              then printf "%s: Failure in looking up: %t" funname e
              else ().

    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_type ty :=
      let f := ltac2:(ty |- debug_enter_reify "type.reify" (Ltac1.get_to_constr ty)) in
      f ty.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_base_type ty :=
      let f := ltac2:(ty |- debug_enter_reify "base.reify" (Ltac1.get_to_constr ty)) in
      f ty.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_pattern_base_type ty :=
      let f := ltac2:(ty |- debug_enter_reify "pattern.base.reify" (Ltac1.get_to_constr ty)) in
      f ty.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_preprocess term :=
      let f := ltac2:(term |- debug_enter_reify_preprocess "expr.reify_preprocess" (Ltac1.get_to_constr term)) in
      f term.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_ident_preprocess term :=
      let f := ltac2:(term |- debug_enter_reify_ident_preprocess "expr.reify_ident_preprocess" (Ltac1.get_to_constr term)) in
      f term.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_in_context term :=
      let f := ltac2:(term |- debug_enter_reify "expr.reify_in_context" (Ltac1.get_to_constr term)) in
      f term.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_in_context_after_preprocess term :=
      let f := ltac2:(term |- debug_enter_reify_after_preprocess "expr.reify_in_context" (Ltac1.get_to_constr term)) in
      f term.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_ident_after_preprocess term :=
      let f := ltac2:(term |- debug_enter_reify_ident_after_preprocess "expr.reify_in_context" (Ltac1.get_to_constr term)) in
      f term.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_leave_reify_in_context_success term res :=
      let f := ltac2:(term res |- debug_leave_reify_success "expr.reify_in_context" (Ltac1.get_to_constr term) (Ltac1.get_to_constr res)) in
      f term res.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_lookup_ident term :=
      let f := ltac2:(term |- debug_enter_lookup_ident "reify_ident_via_list" (Ltac1.get_to_constr term)) in
      f term.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_leave_lookup_ident_in_failure idc all_ident_and_interp :=
      let f := ltac2:(idc all_ident_and_interp |- debug_leave_lookup_ident_failure "reify_ident_via_list" (Ltac1.get_to_constr idc) (Ltac1.get_to_constr all_ident_and_interp)) in
      f idc all_ident_and_interp.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_leave_lookup_ident_success idc ret :=
      let f := ltac2:(idc ret |- debug_leave_lookup_ident_success "reify_ident_via_list" (Ltac1.get_to_constr idc) (Ltac1.get_to_constr ret)) in
      f idc ret.
  End Reify.

  Local Ltac wrap tac arg :=
    constr:(ltac:(let v := tac arg in refine v)).

  Module type.
    Import Language.Compilers.type.
    Ltac reify_internal base_reify base_type ty :=
      let __ := Reify.debug_enter_reify_type ty in
      let reify_rec t := reify_internal base_reify base_type t in
      lazymatch eval cbv beta in ty with
      | ?A -> ?B
        => let rA := reify_rec A in
           let rB := reify_rec B in
           constr:(@arrow base_type rA rB)
      | @interp _ _ ?T => T
      | _ => let rt := base_reify ty in
             constr:(@base base_type rt)
      end.
    Ltac reify base_reify base_type ty := wrap ltac:(reify_internal ltac:(wrap base_reify) base_type) ty.

    Class reified_of {base_type} {interp_base_type : base_type -> Type} (v : Type) (rv : type base_type)
      := reified_ok : @interp base_type interp_base_type rv = v.

    Ltac reify_via_tc base_type interp_base_type ty :=
      let rv := constr:(_ : @reified_of base_type interp_base_type ty _) in
      lazymatch type of rv with
      | @reified_of _ _ _ ?rv => rv
      end.
  End type.
  Module base.
    Import Language.Compilers.base.
    Local Notation einterp := type.interp.

    Ltac reify_internal base reify_base ty :=
      let reify_rec ty := reify_internal base reify_base ty in
      let __ := Reify.debug_enter_reify_base_type ty in
      lazymatch eval cbv beta in ty with
      | Datatypes.unit => constr:(@type.unit base)
      | Datatypes.prod ?A ?B
        => let rA := reify_rec A in
          let rB := reify_rec B in
          constr:(@type.prod base rA rB)
      | Datatypes.list ?T
        => let rT := reify_rec T in
          constr:(@type.list base rT)
      | Datatypes.option ?T
        => let rT := reify_rec T in
          constr:(@type.option base rT)
      | @interp base ?base_interp ?T => T
      | @einterp (@type base) (@interp base ?base_interp) (@Compilers.type.base (@type base) ?T) => T
      | ?ty => let rT := reify_base ty in
              constr:(@type.type_base base rT)
      end.
    Ltac reify base reify_base ty := wrap ltac:(reify_internal base ltac:(wrap reify_base)) ty.
    (*Notation reify t := (ltac:(let rt := reify t in exact rt)) (only parsing).
    Notation reify_norm t := (ltac:(let t' := eval cbv in t in let rt := reify t' in exact rt)) (only parsing).*)
    (*Notation reify_type_of e := (reify ((fun t (_ : t) => t) _ e)) (only parsing).*)
    (*Notation reify_norm_type_of e := (reify_norm ((fun t (_ : t) => t) _ e)) (only parsing).*)
  End base.

  Module pattern.
    Import Language.Compilers.pattern.
    Module base.
      Import Language.Compilers.pattern.base.
      Local Notation einterp := type.interp.

      Ltac reify_internal base reify_base ty :=
        let reify_rec ty := reify_internal base reify_base ty in
        let __ := Reify.debug_enter_reify_pattern_base_type ty in
        lazymatch eval cbv beta in ty with
        | Datatypes.unit => constr:(@type.unit base)
        | Datatypes.prod ?A ?B
          => let rA := reify_rec A in
             let rB := reify_rec B in
             constr:(@type.prod base rA rB)
        | Datatypes.list ?T
          => let rT := reify_rec T in
             constr:(@type.list base rT)
        | Datatypes.option ?T
          => let rT := reify_rec T in
             constr:(@type.option base rT)
        | @interp base ?base_interp ?lookup ?T => T
        | @einterp (@type base) (@interp base ?base_interp ?lookup) (@Compilers.type.base (@type base) ?T) => T
        | ?ty => let rT := reify_base ty in
                 constr:(@type.type_base base rT)
        end.
      Ltac reify base reify_base ty := wrap ltac:(reify_internal base ltac:(wrap reify_base)) ty.
    End base.
  End pattern.

  Module expr.
    Import Language.Compilers.expr.

    Module var_context.
      Inductive list {base_type} {var : type base_type -> Type} :=
      | nil
      | cons {T t} (gallina_v : T) (v : var t) (ctx : list).
    End var_context.

    (* cf COQBUG(https://github.com/coq/coq/issues/5448) , COQBUG(https://github.com/coq/coq/issues/6315) , COQBUG(https://github.com/coq/coq/issues/6559) , COQBUG(https://github.com/coq/coq/issues/6534) , https://github.com/mit-plv/fiat-crypto/issues/320 *)
    Ltac require_same_var n1 n2 :=
      (*idtac n1 n2;*)
      let c1 := constr:(fun n1 n2 : Set => ltac:(exact n1)) in
      let c2 := constr:(fun n1 n2 : Set => ltac:(exact n2)) in
      (*idtac c1 c2;*)
      first [ constr_eq c1 c2 | fail 1 "Not the same var:" n1 "and" n2 "(via constr_eq" c1 c2 ")" ].
    Ltac is_same_var n1 n2 :=
      match goal with
      | _ => let check := match goal with _ => require_same_var n1 n2 end in
             true
      | _ => false
      end.
    Ltac is_underscore v :=
      let v' := fresh v in
      let v' := fresh v' in
      is_same_var v v'.
    Ltac refresh n fresh_tac :=
      let n_is_underscore := is_underscore n in
      let n' := lazymatch n_is_underscore with
                | true => fresh
                | false => fresh_tac n
                end in
      let n' := fresh_tac n' in
      n'.

    Ltac type_of_first_argument_of f :=
      let f_ty := type of f in
      lazymatch eval hnf in f_ty with
      | forall x : ?T, _ => T
      end.

    (** Forms of abstraction in Gallina that our reflective language
        cannot handle get handled by specializing the code "template"
        to each particular application of that abstraction. In
        particular, type arguments (nat, Z, (λ _, nat), etc) get
        substituted into lambdas and treated as a integral part of
        primitive operations (such as [@List.app T], [@list_rect (λ _,
        nat)]).  During reification, we accumulate them in a
        right-associated tuple, using [tt] as the "nil" base case.
        When we hit a λ or an identifier, we plug in the template
        parameters as necessary. *)
    Ltac require_template_parameter parameter_type :=
      first [ unify parameter_type Prop
            | unify parameter_type Set
            | unify parameter_type Type
            | lazymatch eval hnf in parameter_type with
              | forall x : ?T, @?P x
                => let check := constr:(fun x : T
                                        => ltac:(require_template_parameter (P x);
                                                 exact I)) in
                   idtac
              end ].
    Ltac is_template_parameter parameter_type :=
      is_success_run_tactic ltac:(fun _ => require_template_parameter parameter_type).
    Ltac plug_template_ctx f template_ctx :=
      lazymatch template_ctx with
      | tt => f
      | (?arg, ?template_ctx')
        =>
        let T := type_of_first_argument_of f in
        let x_is_template_parameter := is_template_parameter T in
        lazymatch x_is_template_parameter with
        | true
          => plug_template_ctx (f arg) template_ctx'
        | false
          => constr:(fun x : T
                     => ltac:(let v := plug_template_ctx (f x) template_ctx in
                              exact v))
        end
      end.

    Ltac reify_preprocess term :=
      let __ := Reify.debug_enter_reify_preprocess term in
      lazymatch term with
      | match ?b with true => ?t | false => ?f end
        => let T := type of term in
           reify_preprocess (@Thunked.bool_rect T (fun _ => t) (fun _ => f) b)
      | match ?x with Datatypes.pair a b => @?f a b end
        => let T := type of term in
           reify_preprocess (@prod_rect_nodep _ _ T f x)
      | match ?x with nil => ?N | cons a b => @?C a b end
        => let T := type of term in
           reify_preprocess (@Thunked.list_case _ T (fun _ => N) C x)
      | match ?x with None => ?N | Some a => @?S a end
        => let T := type of term in
           reify_preprocess (@Thunked.option_rect _ T S (fun _ => N) x)
      | let x := ?a in ?b
        => let A := type of a in
           let T := type of term in
           let rec_val := match constr:(Set) with
                          | _ => let v := constr:((fun x : A => b) a) in
                                 let __ := type of v in (* ensure that the abstraction is well-typed, i.e., that we're not relying on the value of the let to well-type the body *)
                                 v
                          | _ => constr:(match a return T with x => b end) (* if we do rely on the body of [x] to well-type [b], then just inline it *)
                          end in
           (*let B := lazymatch type of b with forall x, @?B x => B end in*)
           reify_preprocess rec_val (*(@Let_In A B a b)*)
      | ?term => constr:(ltac:(let f := ltac2:(term |- Control.refine (fun () => reify_preprocess_extra [] (Ltac1.get_to_constr term))) in
                               f term))
      end.

    Ltac reify_ident_preprocess term :=
      let __ := Reify.debug_enter_reify_ident_preprocess term in
      let reify_ident_preprocess_extra term := constr:(ltac:(let f := ltac2:(term |- Control.refine (fun () => reify_ident_preprocess_extra [] (Ltac1.get_to_constr term))) in
                                                             f term)) in
      lazymatch term with
      | Datatypes.S => reify_ident_preprocess Nat.succ
      | @Datatypes.prod_rect ?A ?B ?T0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_ident_preprocess (@prod_rect_nodep A B T)
           | T0 => reify_ident_preprocess_extra term
           | ?T' => reify_ident_preprocess (@Datatypes.prod_rect A B T')
           end
      | @Datatypes.bool_rect ?T0 ?Ptrue ?Pfalse
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_ident_preprocess (@Thunked.bool_rect T (fun _ => Ptrue) (fun _ => Pfalse))
           | T0 => reify_ident_preprocess_extra term
           | ?T' => reify_ident_preprocess (@Datatypes.bool_rect T' Ptrue Pfalse)
           end
      | @Datatypes.nat_rect ?T0 ?P0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?A -> ?B => reify_ident_preprocess (@nat_rect_arrow_nodep A B P0)
           | fun _ => ?T => reify_ident_preprocess (@Thunked.nat_rect T (fun _ => P0))
           | T0 => reify_ident_preprocess_extra term
           | ?T' => reify_ident_preprocess (@Datatypes.nat_rect T' P0)
           end
      | ident.eagerly (@Datatypes.nat_rect) ?T0 ?P0
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?A -> ?B => reify_ident_preprocess (ident.eagerly (@nat_rect_arrow_nodep) A B P0)
           | fun _ => ?T => reify_ident_preprocess (ident.eagerly (@Thunked.nat_rect) T (fun _ => P0))
           | T0 => reify_ident_preprocess_extra term
           | ?T' => reify_ident_preprocess (ident.eagerly (@Datatypes.nat_rect) T' P0)
           end
      | @Datatypes.list_rect ?A ?T0 ?Pnil
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?P -> ?Q => reify_ident_preprocess (@list_rect_arrow_nodep A P Q Pnil)
           | fun _ => ?T => reify_ident_preprocess (@Thunked.list_rect A T (fun _ => Pnil))
           | T0 => reify_ident_preprocess_extra term
           | ?T' => reify_ident_preprocess (@Datatypes.list_rect A T' Pnil)
           end
      | ident.eagerly (@Datatypes.list_rect) ?A ?T0 ?Pnil
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?P -> ?Q => reify_ident_preprocess (ident.eagerly (@list_rect_arrow_nodep) A P Q Pnil)
           | fun _ => ?T => reify_ident_preprocess (ident.eagerly (@Thunked.list_rect) A T (fun _ => Pnil))
           | T0 => reify_ident_preprocess_extra term
           | ?T' => reify_ident_preprocess (ident.eagerly (@Datatypes.list_rect) A T' Pnil)
           end
      | @ListUtil.list_case ?A ?T0 ?Pnil
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_ident_preprocess (@Thunked.list_case A T (fun _ => Pnil))
           | T0 => reify_ident_preprocess_extra term
           | ?T' => reify_ident_preprocess (@ListUtil.list_case A T' Pnil)
           end
      | @Datatypes.option_rect ?A ?T0 ?PSome ?PNone
        => lazymatch (eval cbv beta in T0) with
           | fun _ => ?T => reify_ident_preprocess (@Thunked.option_rect A T PSome (fun _ => PNone))
           | T0 => reify_ident_preprocess_extra term
           | ?T' => reify_ident_preprocess (@Datatypes.option_rect A T' PSome PNone)
           end
      | ident.eagerly (?f ?x)
        => reify_ident_preprocess (ident.eagerly f x)
      | ?term => reify_ident_preprocess_extra term
      end.


    Ltac reify_in_context base_type ident reify_base_type reify_ident var term value_ctx template_ctx :=
      let reify_rec_gen term value_ctx template_ctx := reify_in_context base_type ident reify_base_type reify_ident var term value_ctx template_ctx in
      let reify_rec term := reify_rec_gen term value_ctx template_ctx in
      let reify_rec_not_head term := reify_rec_gen term value_ctx tt in
      let do_reify_ident term else_tac
          := reify_ident
               term
               ltac:(fun idc => constr:(@Ident base_type ident var _ idc))
                      else_tac in
      let __ := Reify.debug_enter_reify_in_context term in
      let
        res :=
        lazymatch value_ctx with
        | context[@var_context.cons _ _ ?T ?rT term ?v _]
          => constr:(@Var base_type ident var rT v)
        | _
          =>
          let term := reify_preprocess term in
          let __ := Reify.debug_enter_reify_in_context_after_preprocess term in
          lazymatch term with
          | @Let_In ?A ?B ?a ?b
            => let ra := reify_rec a in
               let rb := reify_rec b in
               lazymatch rb with
               | @Abs _ _ _ ?s ?d ?f
                 => constr:(@LetIn base_type ident var s d ra f)
               | ?rb => constr_fail_with ltac:(fun _ => fail 1 "Invalid non-Abs function reification of" b "to" rb)
               end
          | (fun x : ?T => ?f)
            =>
            let x_is_template_parameter := is_template_parameter T in
            lazymatch x_is_template_parameter with
            | true
              =>
              lazymatch template_ctx with
              | (?arg, ?template_ctx)
                => (* we pull a trick with [match] to plug in [arg] without running cbv β *)
                lazymatch type of term with
                | forall y, ?P
                  => reify_rec_gen (match arg as y return P with x => f end) value_ctx template_ctx
                end
              end
            | false
              =>
              let rT := type.reify reify_base_type base_type T in
              let not_x := fresh (* could be [refresh x ltac:(fun n => fresh n)] in 8.8; c.f. https://github.com/mit-plv/fiat-crypto/issues/320 and probably COQBUG(https://github.com/coq/coq/issues/6534) *) in
              let not_x2 := fresh (* could be [refresh not_x ltac:(fun n => fresh n)] in 8.8; c.f. https://github.com/mit-plv/fiat-crypto/issues/320 and probably COQBUG(https://github.com/coq/coq/issues/6534) *) in
              let not_x3 := fresh (* could be [refresh not_x2 ltac:(fun n => fresh n)] in 8.8; c.f. https://github.com/mit-plv/fiat-crypto/issues/320 and probably COQBUG(https://github.com/coq/coq/issues/6534) *) in
              (*let __ := match goal with _ => idtac "reify_in_context: λ case:" term "using vars:" not_x not_x2 not_x3 end in*)
              let rf0 :=
                  constr:(
                    fun (x : T) (not_x : var rT)
                    => match f, @var_context.cons base_type var T rT x not_x value_ctx return _ with (* c.f. COQBUG(https://github.com/coq/coq/issues/6252#issuecomment-347041995) for [return _] *)
                       | not_x2, not_x3
                         => ltac:(
                              let f := (eval cbv delta [not_x2] in not_x2) in
                              let var_ctx := (eval cbv delta [not_x3] in not_x3) in
                              (*idtac "rec call" f "was" term;*)
                              let rf := reify_rec_gen f var_ctx template_ctx in
                              exact rf)
                       end) in
              lazymatch rf0 with
              | (fun _ => ?rf)
                => constr:(@Abs base_type ident var rT _ rf)
              | _
                => (* This will happen if the reified term still
                    mentions the non-var variable.  By chance, [cbv
                    delta] strips type casts, which are only places
                    that I can think of where such dependency might
                    remain.  However, if this does come up, having a
                    distinctive error message is much more useful for
                    debugging than the generic "no matching clause" *)
                constr_fail_with ltac:(fun _ => fail 1 "Failure to eliminate functional dependencies of" rf0)
              end
            end
          | _
            =>
            let term := reify_ident_preprocess term in
            let __ := Reify.debug_enter_reify_ident_after_preprocess term in
            do_reify_ident
              term
              ltac:(
              fun _
              =>
                lazymatch term with
                | ?f ?x
                  =>
                  let ty := type_of_first_argument_of f in
                  let x_is_template_parameter := is_template_parameter ty in
                  lazymatch x_is_template_parameter with
                  | true
                    => (* we can't reify things of type [Type], so we save it for later to plug in *)
                    reify_rec_gen f value_ctx (x, template_ctx)
                  | false
                    => let rx := reify_rec_gen x value_ctx tt in
                       let rf := reify_rec_gen f value_ctx template_ctx in
                       constr:(App (base_type:=base_type) (ident:=ident) (var:=var) rf rx)
                  end
                | _
                  => let term' := plug_template_ctx term template_ctx in
                     do_reify_ident
                       term'
                       ltac:(fun _
                             =>
                               (*let __ := match goal with _ => idtac "Attempting to unfold" term end in*)
                               let term
                                   := match constr:(Set) with
                                      | _ => (eval cbv delta [term] in term) (* might fail, so we wrap it in a match to give better error messages *)
                                      | _
                                        => let __ := match goal with
                                                     | _ => fail 2 "Unrecognized term:" term'
                                                     end in
                                           constr_fail
                                      end in
                               match constr:(Set) with
                               | _ => reify_rec term
                               | _ => let __ := match goal with
                                                | _ => idtac "Error: Failed to reify" term' "via unfolding";
                                                       fail 2 "Failed to reify" term' "via unfolding"
                                                end in
                                      constr_fail
                               end)
                end)
          end
        end in
      let __ := Reify.debug_leave_reify_in_context_success term res in
      res.
    Ltac reify base_type ident reify_base_type reify_ident var term :=
      reify_in_context base_type ident reify_base_type reify_ident var term (@var_context.nil base_type var) tt.
    Ltac Reify base_type ident reify_base_type reify_ident term :=
      constr:(fun var : type base_type -> Type
              => ltac:(let r := reify base_type ident reify_base_type reify_ident var term in
                       exact r)).
    Ltac Reify_rhs base_type ident reify_base_type reify_ident base_interp interp_ident _ :=
      let RHS := lazymatch goal with |- _ = ?RHS => RHS end in
      let R := Reify base_type ident reify_base_type reify_ident RHS in
      transitivity (@Interp base_type ident base_interp interp_ident _ R);
      [ | reflexivity ].

    Class Reified_of {base_type ident interp_base_type interp_ident} {t} (v : type.interp interp_base_type t) (rv : @Expr base_type ident t)
      := reified_ok : @Interp base_type ident interp_base_type interp_ident t rv = v.

    Lemma Reify_rhs {base_type ident interp_base_type interp_ident t v rv lhs}
          {H : @Reified_of base_type ident interp_base_type interp_ident t v rv}
      : lhs == @Interp base_type ident interp_base_type interp_ident t rv
        -> lhs == v.
    Proof.
      cbv [Reified_of] in H; subst v; exact id.
    Qed.
  End expr.
End Compilers.
Export Compilers.Exports.
