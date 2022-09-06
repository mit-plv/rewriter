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
Require Rewriter.Util.Tactics2.List.
Require Rewriter.Util.Tactics2.Ltac1.
Require Rewriter.Util.Tactics2.Message.
Require Rewriter.Util.Tactics2.Ident.
Require Import Rewriter.Util.Tactics2.Constr.Unsafe.MakeAbbreviations.
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

  Module Import Ltac2.
    Module Ident.
      (* TODO: find a less hacky way of doing this *)
      Ltac constant_to_lambda_reified cst :=
        let cst := fresh "reified_" cst in constr:(fun cst : True => cst).
      Ltac2 refine_constant_to_lambda_reified (c : Ltac1.t) : unit :=
        let f := ltac1:(c |- let v := constant_to_lambda_reified constr:(c) in exact v) in
        f c.
      Ltac2 reified_of_constr (c : constr) : ident
        := Ident.of_constr refine_constant_to_lambda_reified c.
    End Ident.
  End Ltac2.

  (* this is very super-linear, should not be used in production code *)
  Ltac2 with_term_in_context (cache : (unit -> binder) list) (tys : constr list) (term : constr) (tac : constr -> unit) : unit :=
    printf "Warning: with_term_in_context: Bad asymptotics";
    let rec aux0 (cache : (unit -> binder) list) (avoid : Fresh.Free.t) (k : unit -> unit)
      := match cache with
         | [] => k ()
         | b :: bs
           => let b := b () in
              let id := match Constr.Binder.name b with
                        | Some id => id
                        | None => Fresh.fresh avoid @DUMMY_with_term_in_context_MISSING
                        end in
              let avoid := Fresh.Free.union avoid (Fresh.Free.of_ids [id]) in
              let _ := Constr.in_context id (Constr.Binder.type b) (fun () => aux0 bs avoid k; Control.refine (fun () => 'I)) in
              ()
         end in
    let rec aux (tys : constr list) (acc : ident list) (avoid : Fresh.Free.t)
      := match tys with
         | [] => aux0 cache avoid (fun () => tac (Constr.Unsafe.substnl (List.map mkVar (List.rev acc)) 0 term))
         | ty :: tys
           => let id := Fresh.fresh avoid @DUMMY in
              let avoid := Fresh.Free.union avoid (Fresh.Free.of_ids [id]) in
              let _ := Constr.in_context id ty (fun () => aux tys (id :: acc) avoid; Control.refine (fun () => 'I)) in
              ()
         end in
    aux tys [] (Fresh.Free.of_constr term).

  Module Reify.
    Ltac2 debug_level := Pre.reify_debug_level.

    Ltac2 mutable should_debug_enter_reify () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_enter_reify_preprocess () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_enter_reify_ident_preprocess () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_enter_reify_after_preprocess () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_leave_reify_success () := Int.le 6 debug_level.
    Ltac2 mutable should_debug_leave_reify_failure () := Int.le 0 debug_level.
    Ltac2 mutable should_debug_leave_reify_normal_failure () := Int.le 6 debug_level.
    Ltac2 mutable should_debug_enter_reify_ident_after_preprocess () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_enter_lookup_ident () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_success () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_failure_verbose () := Int.le 6 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_failure () := Int.le 5 debug_level.
    Ltac2 mutable should_debug_enter_plug_template_ctx () := Int.le 7 debug_level.
    Ltac2 mutable should_debug_enter_reify_case () := Int.le 7 debug_level.
    Ltac2 mutable should_debug_fine_grained () := Int.le 100 debug_level.
    Ltac2 mutable should_debug_print_args () := Int.le 50 debug_level.
    Ltac2 mutable should_debug_let_bind () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_typing_failure () := Int.le 5 debug_level.
    Ltac2 mutable should_debug_typing_failure_assume_well_typed () := Int.le 2 debug_level.
    Ltac2 mutable should_debug_check_app_early () := Int.le 6 debug_level.
    Ltac2 mutable should_debug_profile () := Int.le 1 debug_level.

    Ltac2 debug_if (cond : unit -> bool) (tac : unit -> 'a) (default : 'a) :=
      if cond ()
      then tac ()
      else default.

    Ltac2 debug_typing_failure (funname : string) (x : constr) (err : exn)
      := debug_if should_debug_typing_failure (fun () => printf "Warning: %s: failure to typecheck %t: %a" funname x (fun () => Message.of_exn) err) ().
    Ltac2 debug_typing_failure_assume_well_typed (funname : string) (v : constr) (term : constr) (ctx_tys : binder list) (ty : constr)
      := debug_if should_debug_typing_failure_assume_well_typed (fun () => printf "Warning: %s: could not well-type %t due to underlying issue typechecking %t without relevant context %a, but assuming that it's well-typed because %t is not a template-parameter type" funname v term (fun () => Message.of_list Message.of_binder) ctx_tys ty) ().
    Ltac2 debug_profile (descr : string) (f : unit -> 'a) : 'a
      := if should_debug_profile ()
         then Control.time (Some descr) f
         else f ().
    Ltac2 debug_fine_grained (funname : string) (msg : unit -> message)
      := debug_if should_debug_fine_grained (fun () => printf "%s: %a" funname (fun () => msg) ()) ().
    Ltac2 debug_enter_reify (funname : string) (e : constr)
      := debug_if should_debug_enter_reify (fun () => printf "%s: Attempting to reify:" funname; printf "%t" e) ().
    Ltac2 debug_enter_reify_case (funname : string) (casename : string) (e : constr)
      := debug_if should_debug_enter_reify_case (fun () => printf "%s: Case: %s" funname casename) ().
    Ltac2 debug_enter_reify_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_preprocess (fun () => printf "%s: Attempting to preprocess:" funname; printf "%t" e) ().
    (*Ltac2 debug_enter_reify_ident_idtac (funname : string) (e : constr)
      := printf "%s: Attempting to reify (as ident):" funname; printf "%t" e.*)
    Ltac2 debug_enter_reify_after_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_after_preprocess (fun () => printf "%s: Attempting to reify (post-preprocessing):" funname; printf "%t" e) ().
    Ltac2 debug_enter_reify_ident_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_ident_preprocess (fun () => printf "%s: Attempting to (ident) preprocess:" funname; printf "%t" e) ().
    Ltac2 debug_enter_reify_ident_after_preprocess (funname : string) (e : constr)
      := debug_if should_debug_enter_reify_ident_after_preprocess (fun () => printf "%s: Attempting to reify ident (post-preprocessing):" funname; printf "%t" e) ().
    Ltac2 debug_leave_reify_success (funname : string) (e : constr) (ret : constr)
      := debug_if should_debug_leave_reify_success (fun () => printf "%s: Success in reifying: %t as %t" funname e ret) ().
    Ltac2 debug_leave_reify_failure (funname : string) (e : constr)
      := debug_if should_debug_leave_reify_failure (fun () => printf "%s: Failure in reifying:" funname; printf "%t" e) ().
    Ltac2 debug_leave_reify_normal_failure (funname : string) (e : constr)
      := debug_if should_debug_leave_reify_normal_failure (fun () => printf "%s: Failure in reifying:" funname; printf "%t" e) ().
    Ltac2 debug_enter_lookup_ident (funname : string) (e : constr)
      := debug_if should_debug_enter_lookup_ident (fun () => printf "%s: Attempting to lookup ident:" funname; printf "%t" e) ().
    Ltac2 debug_leave_lookup_ident_success (funname : string) (e : constr) (ret : constr)
      := debug_if should_debug_leave_lookup_ident_success (fun () => printf "%s: Success in looking up ident: %t as %t" funname e ret) ().
    Ltac2 debug_leave_lookup_ident_failure (funname : string) (e : constr) (ls : constr)
      := if should_debug_leave_lookup_ident_failure_verbose ()
         then printf "%s: Failure in looking up:" funname; printf "%t (in %t)" e ls
         else if should_debug_leave_lookup_ident_failure ()
              then printf "%s: Failure in looking up:" funname; printf "%t" e
              else ().
    Ltac2 debug_enter_plug_template_ctx (funname : string) (e : constr) (template_ctx : constr list)
      := debug_if
           should_debug_enter_plug_template_ctx
           (fun ()
            => printf
                 "%s: Attempting to plug template ctx into %t %a"
                 funname e (fun () => Message.of_list (fprintf "%t")) template_ctx)
           ().
    Ltac2 debug_let_bind (funname : string) (name : ident) (ty : constr) (val : constr)
      := debug_if
           should_debug_let_bind
           (fun ()
            => printf "%s: let-binding %I : %t := %t" funname name ty val)
           ().
    Ltac2 debug_print_args (funname : string) (pr : 'a -> message) (args : 'a)
      := debug_if should_debug_print_args (fun () => printf "%s: args: %a" funname (fun () => pr) args) ().
    Ltac2 debug_Constr_check (funname : string) (descr : constr -> constr -> exn -> message) (var : constr) (cache : (unit -> binder) list) (var_ty_ctx : constr list) (e : constr)
      := debug_if
           should_debug_check_app_early
           (fun () => match Constr.Unsafe.check e with
                      | Val e => e
                      | Err _
                        => with_term_in_context
                             cache
                             (List.map (fun t => mkApp var [t]) var_ty_ctx) e
                             (fun e' => match Constr.Unsafe.check e' with
                                        | Val _ => (* wasted a bunch of time *) ()
                                        | Err err
                                          => let descr := descr e e' err in
                                             Control.throw
                                              (Reification_panic
                                                 (fprintf "Anomaly: %s: %t failed to check (in context %a as %t): %a" funname e (fun () => Message.of_list Message.of_constr) var_ty_ctx e' (fun () a => a) descr))
                                        end);
                           e
                      end)
           e.
  End Reify.

  Module type.
    Import Language.Compilers.type.
    Ltac2 rec reify (base_reify : constr -> constr) (base_type : constr) (ty : constr) :=
      Reify.debug_enter_reify "type.reify" ty;
      let reify_rec (t : constr) := reify base_reify base_type t in
      let res :=
        lazy_match! (eval cbv beta in $ty) with
        | ?a -> ?b
          => let ra := reify_rec a in
             let rb := reify_rec b in
             '(@arrow $base_type $ra $rb)
        | @interp _ _ ?t => t
        | _ => let rt := base_reify ty in
               '(@base $base_type $rt)
        end in
      Reify.debug_leave_reify_success "type.reify" ty res;
      res.
    #[deprecated(since="8.15",note="Use Ltac2 type.reify instead.")]
     Ltac reify base_reify base_type ty :=
      let f := ltac2:(base_reify base_type ty
                      |- Control.refine (fun () => reify (fun v => Ltac1.apply_c base_reify [v]) (Ltac1.get_to_constr "type.reify:base_type" base_type) (Ltac1.get_to_constr "type.reify:ty" ty))) in
      constr:(ltac:(f base_reify base_type ty)).

    Class reified_of {base_type} {interp_base_type : base_type -> Type} (v : Type) (rv : type base_type)
      := reified_ok : @interp base_type interp_base_type rv = v.

    Ltac2 reify_via_tc (base_type : constr) (interp_base_type : constr) (ty : constr) :=
      let rv := '(_ : @reified_of $base_type $interp_base_type $ty _) in
      lazy_match! Constr.type rv with
      | @reified_of _ _ _ ?rv => rv
      end.
  End type.
  Module base.
    Import Language.Compilers.base.
    Local Notation einterp := type.interp.

    Ltac2 rec reify (base : constr) (reify_base : constr -> constr) (ty : constr) :=
      let reify_rec (ty : constr) := reify base reify_base ty in
      Reify.debug_enter_reify "base.reify" ty;
      let res :=
        lazy_match! (eval cbv beta in $ty) with
        | Datatypes.unit => '(@type.unit $base)
        | Datatypes.prod ?a ?b
          => let ra := reify_rec a in
             let rb := reify_rec b in
             '(@type.prod $base $ra $rb)
        | Datatypes.list ?t
          => let rt := reify_rec t in
             '(@type.list $base $rt)
        | Datatypes.option ?t
          => let rt := reify_rec t in
             '(@type.option $base $rt)
        | @interp (*$base*)?base' ?base_interp ?t => t
        | @einterp (@type (*$base*)?base') (@interp (*$base*)?base' ?base_interp) (@Compilers.type.base (@type (*$base*)?base') ?t) => t
        | ?ty => let rt := reify_base ty in
                 '(@type.type_base $base $rt)
        end in
      Reify.debug_leave_reify_success "base.reify" ty res;
      res.
    #[deprecated(since="8.15",note="Use Ltac2 base.reify instead.")]
     Ltac reify base reify_base ty :=
      let f := ltac2:(base reify_base ty
                      |- Control.refine (fun () => reify (Ltac1.get_to_constr "base" base) (fun v => Ltac1.apply_c reify_base [v]) (Ltac1.get_to_constr "ty" ty))) in
      constr:(ltac:(f base reify_base ty)).
  End base.

  Module pattern.
    Import Language.Compilers.pattern.
    Module base.
      Import Language.Compilers.pattern.base.
      Local Notation einterp := type.interp.

      Ltac2 rec reify (base : constr) (reify_base : constr -> constr) (ty : constr) :=
        let reify_rec (ty : constr) := reify base reify_base ty in
        Reify.debug_enter_reify "pattern.base.reify" ty;
        let res :=
          lazy_match! (eval cbv beta in $ty) with
          | Datatypes.unit => '(@type.unit $base)
          | Datatypes.prod ?a ?b
            => let ra := reify_rec a in
               let rb := reify_rec b in
               '(@type.prod $base $ra $rb)
          | Datatypes.list ?t
            => let rt := reify_rec t in
               '(@type.list $base $rt)
          | Datatypes.option ?t
            => let rt := reify_rec t in
               '(@type.option $base $rt)
          | @interp (*$base*)?base' ?base_interp ?lookup ?t => t
          | @einterp (@type (*$base*)?base') (@interp (*$base*)?base' ?base_interp ?lookup) (@Compilers.type.base (@type (*$base*)?base') ?t) => t
          | ?ty => let rt := reify_base ty in
                   '(@type.type_base $base $rt)
          end in
        Reify.debug_leave_reify_success "pattern.base.reify" ty res;
        res.
      #[deprecated(since="8.15",note="Use Ltac2 pattern.base.reify instead.")]
       Ltac reify base reify_base ty :=
        let f := ltac2:(base reify_base ty
                        |- Control.refine (fun () => reify (Ltac1.get_to_constr "base" base) (fun v => Ltac1.apply_c reify_base [v]) (Ltac1.get_to_constr "ty" ty))) in
        constr:(ltac:(f base reify_base ty)).
    End base.
  End pattern.

  Module expr.
    Import Language.Compilers.expr.

    Module var_context.
      Inductive list {base_type} {var : type base_type -> Type} :=
      | nil
      | cons {T t} (gallina_v : T) (v : var t) (ctx : list).
    End var_context.

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
    Ltac2 rec is_template_parameter (ctx_tys : binder list) (parameter_type : constr) : bool :=
      let do_red () :=
        let t := Std.eval_hnf parameter_type in
        if Constr.equal t parameter_type
        then false
        else is_template_parameter ctx_tys t in
      match Constr.Unsafe.kind parameter_type with
      | Constr.Unsafe.Sort _ => true
      | Constr.Unsafe.Cast x _ _ => is_template_parameter ctx_tys x
      | Constr.Unsafe.Prod b body => is_template_parameter (b :: ctx_tys) body
      | Constr.Unsafe.App _ _
        => do_red ()
      | Constr.Unsafe.Constant _ _
        => do_red ()
      | Constr.Unsafe.LetIn _ _ _
        => do_red ()
      | Constr.Unsafe.Case _ _ _ _ _
        => do_red ()
      | Constr.Unsafe.Proj _ _
        => do_red ()
      | _ => false
      end.
    #[deprecated(since="8.15",note="Use Ltac2 is_template_parameter instead.")]
    Ltac is_template_parameter parameter_type :=
      let f := ltac2:(parameter_type |- Control.refine (fun () => if is_template_parameter [] (Ltac1.get_to_constr "parameter_type" parameter_type) then 'true else 'false)) in
      constr:(ltac:(f parameter_type)).

    Ltac2 rec template_ctx_to_list (template_ctx : constr) : constr list :=
      lazy_match! template_ctx with
      | tt => []
      | (?arg, ?template_ctx')
        => arg :: template_ctx_to_list template_ctx'
      end.

    Ltac2 rec value_ctx_to_list (value_ctx : constr) : (ident * constr (* ty *) * constr (* var *)) list
      := lazy_match! value_ctx with
         | var_context.nil => []
         | @var_context.cons ?base_type ?var ?t ?rt ?v ?rv ?rest
           => match Constr.Unsafe.kind v with
              | Constr.Unsafe.Var c
                => (c, rt, rv)
              | _ => Control.zero (Invalid_argument (Some (fprintf "value_ctx_to_list: not a Var: %t (of type %t, mapped to %t : %t)" v t rv rt)))
              end
                :: value_ctx_to_list rest
         end.

    Ltac2 eval_cbv_delta_only (i : Std.reference list) (c : constr) :=
      Std.eval_cbv { Std.rBeta := false; Std.rMatch := false;
                     Std.rFix := false; Std.rCofix := false;
                     Std.rZeta := false; Std.rDelta := false;
                     Std.rConst := i }
                   c.
    Ltac2 eval_cbv_beta (c : constr) :=
      Std.eval_cbv { Std.rBeta := true; Std.rMatch := false;
                     Std.rFix := false; Std.rCofix := false;
                     Std.rZeta := false; Std.rDelta := false;
                     Std.rConst := [] }
                   c.

    (* f, f_ty, arg *)
    Ltac2 Type exn ::= [ Template_ctx_mismatch (constr, constr, constr) ].
    Ltac2 plug_template_ctx (ctx_tys : binder list) (f : constr) (template_ctx : constr list) :=
      Reify.debug_enter_plug_template_ctx "expr.plug_template_ctx" f template_ctx;
      let rec mkargs (ctx_tys : binder list) (f_ty : constr) (template_ctx : constr list) :=
        match template_ctx with
        | [] => (1, [], (fun body => body))
        | arg :: template_ctx'
          => match Constr.Unsafe.kind f_ty with
             | Constr.Unsafe.Cast f_ty _ _
               => mkargs ctx_tys f_ty template_ctx
             | Constr.Unsafe.Prod b f_ty
               => if is_template_parameter ctx_tys (Constr.Binder.type b)
                  then let (rel_base, args, close) := mkargs (b :: ctx_tys) f_ty template_ctx' in
                       (rel_base, arg :: args, close)
                  else let (rel_base, args, close) := mkargs (b :: ctx_tys) f_ty template_ctx' in
                       let rel_base := Int.add rel_base 1 in
                       (rel_base, mkRel rel_base :: args,
                         (fun body => mkLambda b (close body)))
             | _ => let f_ty' := Std.eval_hnf f_ty in
                    if Constr.equal f_ty f_ty'
                    then Control.throw (Template_ctx_mismatch f f_ty arg)
                    else mkargs ctx_tys f_ty' template_ctx
             end
        end in
      (* fast type-free path for empty template_ctx *)
      match template_ctx with
      | [] => f
      | _::_
        => let (_, args, close) := mkargs ctx_tys (Constr.type f) template_ctx in
           close (mkApp f args)
      end.
   #[deprecated(since="8.15",note="Use Ltac2 plug_template_ctx instead.")]
     Ltac plug_template_ctx f template_ctx :=
      let plug := ltac2:(f template_ctx
                         |- let template_ctx := (Ltac1.get_to_constr "template_ctx" template_ctx) in
                            let template_ctx := template_ctx_to_list template_ctx in
                            Control.refine (fun () => plug_template_ctx [] (Ltac1.get_to_constr "f" f) template_ctx)) in
      constr:(ltac:(plug f template_ctx)).

    Ltac2 rec reify_preprocess (ctx_tys : binder list) (term : constr) : constr :=
      Reify.debug_enter_reify_preprocess "expr.reify_preprocess" term;
      let reify_preprocess := reify_preprocess ctx_tys in
      let thunk
        := (* kludge around retyping *)
        let (cst, cTrue) := let term := '(I : True) in
                            match Constr.Unsafe.kind term with
                            | Constr.Unsafe.Cast _ cst cTrue => (cst, cTrue)
                            | _ => Control.throw (Reification_panic (fprintf "Anomaly: reify_preprocess: %t is not a Cast!" term))
                            end in
        fun (v : constr)
        => let v := Constr.Unsafe.make (Constr.Unsafe.Cast v cst cTrue) in (* ill-typed, but we'll strip the type soon *)
           (* this is a terrible kludge to access lifting of de Bruijn indices without retyping getting in our way *)
           let v := '(match $v return unit -> True with x => fun _ : unit => x end) in
           match Constr.Unsafe.kind v with
           | Constr.Unsafe.Lambda x v
             => match Constr.Unsafe.kind v with
                | Constr.Unsafe.Cast v _ _ => mkLambda x v
                | _ => Control.throw (Reification_panic (fprintf "Anomaly: reify_preprocess: %t is not a Cast (from under a Lambda)!" v))
                end
           | _ => Control.throw (Reification_panic (fprintf "Anomaly: reify_preprocess: %t is not a Lambda!" v))
           end in
      match Constr.Unsafe.kind term with
      | Constr.Unsafe.Cast x _ _
        => Reify.debug_enter_reify_case "expr.reify_preprocess" "Cast" term;
           reify_preprocess x
      | Constr.Unsafe.LetIn x a b (* let x := ?a in ?b *)
        => Reify.debug_enter_reify_case "expr.reify_preprocess" "LetIn" term;
           let v_lam () := mkApp (mkLambda x b) [a] in
           let v_inlined () := Constr.Unsafe.substnl [a] 0 b in
           let tx := Constr.Binder.type x in
           if is_template_parameter ctx_tys tx
           then (* it's a template parameter (something like a type), no need to abstract over it since we're just going to inline it later *)
             reify_preprocess (v_inlined ())
           else
             let v := v_lam () in
             match Constr.Unsafe.check v (* ensure that the abstraction is well-typed, i.e., that we're not relying on the value of the let to well-type the body *) with
             | Val v => reify_preprocess v
             | Err err (* if we do rely on the body of [x] to well-type [b], then just inline it *)
               => match Constr.Unsafe.check term with
                  | Val _
                    => Reify.debug_typing_failure "expr.reify_preprocess" v err;
                       reify_preprocess (v_inlined ())
                  | Err err'
                    => (* since the underlying term failed to typecheck, but the argument is not a template parameter, we just assume that it's well-typed to abstract over it *)
                      Reify.debug_typing_failure_assume_well_typed "expr.reify_preprocess" v term ctx_tys tx;
                      reify_preprocess v
                  end
           end
      | Constr.Unsafe.Case cinfo ret_ty cinv x branches
        => Reify.debug_enter_reify_case "expr.reify_preprocess" "Case" term;
           match Constr.Unsafe.kind ret_ty with
           | Constr.Unsafe.Lambda xb ret_ty
             => let ty := Constr.Unsafe.substnl [x] 0 ret_ty in
                lazy_match! Constr.Binder.type xb with
                | bool
                  => Reify.debug_enter_reify_case "expr.reify_preprocess" "Case:bool" term;
                     reify_preprocess (mkApp '@Thunked.bool_rect [ty; thunk (Array.get branches 0); thunk (Array.get branches 1); x])
                | prod ?a ?b
                  => Reify.debug_enter_reify_case "expr.reify_preprocess" "Case:prod" term;
                     reify_preprocess (mkApp '@prod_rect_nodep [a; b; ty; Array.get branches 0; x])
                | list ?t
                  => Reify.debug_enter_reify_case "expr.reify_preprocess" "Case:list" term;
                     reify_preprocess (mkApp '@Thunked.list_case [t; ty; thunk (Array.get branches 0); Array.get branches 1; x])
                | option ?t
                  => Reify.debug_enter_reify_case "expr.reify_preprocess" "Case:option" term;
                     reify_preprocess (mkApp '@Thunked.option_rect [t; ty; Array.get branches 0; thunk (Array.get branches 1); x])
                | _ => Reify.debug_enter_reify_preprocess "expr.reify_preprocess_extra" term;
                       reify_preprocess_extra ctx_tys term
                end
           | _ => printf "Warning: non-Lambda case return type %t in %t" ret_ty term;
                  Reify.debug_enter_reify_preprocess "expr.reify_preprocess_extra" term;
                  reify_preprocess_extra ctx_tys term
           end
      | _ => Reify.debug_enter_reify_preprocess "expr.reify_preprocess_extra" term;
             reify_preprocess_extra ctx_tys term
      end.

    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac reify_preprocess term :=
        let f := ltac2:(term
                        |- Control.refine (fun () => reify_preprocess [] (Ltac1.get_to_constr "term" term))) in
        constr:(ltac:(f term)).

    Ltac2 rec reify_ident_preprocess (ctx_tys : binder list) (term : constr) : constr :=
      Reify.debug_enter_reify_ident_preprocess "expr.reify_ident_preprocess" term;
      let reify_ident_preprocess := reify_ident_preprocess ctx_tys in
      let handle_eliminator (motive : constr) (rect_arrow_nodep : constr option) (rect_nodep : constr option) (rect : constr) (mid_args : constr list) (cases_to_thunk : constr list)
        := let mkApp_thunked_cases f pre_args
             := Control.with_holes
                  (fun () => mkApp f (List.append pre_args (List.append mid_args (List.map (fun arg => open_constr:(fun _ => $arg)) cases_to_thunk))))
                  (fun fv => match Constr.Unsafe.check fv with
                             | Val fv => fv
                             | Err err => Control.throw err
                             end) in
           let opt_recr (thunked : bool) orect args :=
             match orect with
             | Some rect => (reify_ident_preprocess,
                              if thunked
                              then mkApp_thunked_cases rect args
                              else mkApp rect (List.append args (List.append mid_args cases_to_thunk)))
             | None => Control.zero Match_failure
             end in
           let (f, x) := match! (eval cbv beta in $motive) with
                         | fun _ => ?a -> ?b
                           => opt_recr false rect_arrow_nodep [a; b]
                         | fun _ => ?t
                           => opt_recr true rect_nodep [t]
                         | ?t'
                           => if Constr.equal motive t'
                              then (reify_ident_preprocess_extra ctx_tys, term)
                              else opt_recr false (Some rect) [t']
                         end in
           f x in
      lazy_match! term with
      | Datatypes.S => reify_ident_preprocess 'Nat.succ
      | @Datatypes.prod_rect ?a ?b ?t0
        => handle_eliminator t0 None (Some '(@prod_rect_nodep $a $b)) '(@Datatypes.prod_rect $a $b) [] []
      | @Datatypes.bool_rect ?t0 ?ptrue ?pfalse
        => handle_eliminator t0 None (Some '@Thunked.bool_rect) '(@Datatypes.bool_rect) [] [ptrue; pfalse]
      | @Datatypes.nat_rect ?t0 ?p0
        => handle_eliminator t0 (Some '@nat_rect_arrow_nodep) (Some '@Thunked.nat_rect) '(@Datatypes.nat_rect) [] [p0]
      | ident.eagerly (@Datatypes.nat_rect) ?t0 ?p0
        => handle_eliminator t0 (Some '(ident.eagerly (@nat_rect_arrow_nodep))) (Some '(ident.eagerly (@Thunked.nat_rect))) '(ident.eagerly (@Datatypes.nat_rect)) [] [p0]
      | @Datatypes.list_rect ?a ?t0 ?pnil
        => handle_eliminator t0 (Some '(@list_rect_arrow_nodep $a)) (Some '(@Thunked.list_rect $a)) '(@Datatypes.list_rect $a) [] [pnil]
      | ident.eagerly (@Datatypes.list_rect) ?a ?t0 ?pnil
        => handle_eliminator t0 (Some '(ident.eagerly (@list_rect_arrow_nodep) $a)) (Some '(ident.eagerly (@Thunked.list_rect) $a)) '(ident.eagerly (@Datatypes.list_rect) $a) [] [pnil]
      | @ListUtil.list_case ?a ?t0 ?pnil
        => handle_eliminator t0 None (Some '(@Thunked.list_case $a)) '(@ListUtil.list_case $a) [] [pnil]
      | @Datatypes.option_rect ?a ?t0 ?psome ?pnone
        => handle_eliminator t0 None (Some '(@Thunked.option_rect $a)) '(@Datatypes.option_rect $a) [psome] [pnone]
      | ident.eagerly (?f ?x)
        => reify_ident_preprocess '(ident.eagerly $f $x)
      | ?term => reify_ident_preprocess_extra ctx_tys term
      end.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac reify_ident_preprocess term :=
        let f := ltac2:(term
                        |- Control.refine (fun () => reify_ident_preprocess [] (Ltac1.get_to_constr "term" term))) in
        constr:(ltac:(f term)).

    Ltac2 Type exn ::= [ Reify_ident_cps_failed ].
    Ltac wrap_reify_ident_cps reify_ident_cps idc :=
      reify_ident_cps
        idc
        ltac:(fun idc => refine idc)
               ltac:(fun _ => ltac2:(Control.zero Reify_ident_cps_failed)).
    Ltac2 reify_ident_opt_of_cps (wrapped_reify_ident_cps : Ltac1.t) : binder list -> constr -> constr option
      := fun ctx_tys idc
         => match Control.case (fun () => Ltac1.apply_c wrapped_reify_ident_cps [idc]) with
            | Val v => let (v, _) := v in Some v
            | Err err
              => match err with
                 | Reify_ident_cps_failed => None
                 | _ => Control.zero err
                 end
            end.

    Ltac2 Type exn ::= [ Not_headed_by_a_constant_under_binders (Constr.Unsafe.kind) ].
    Ltac2 rec head_reference_under_binders (term : constr) : (Std.reference * constr) result :=
      let k := Constr.Unsafe.kind term in
      match k with
      | Constr.Unsafe.App f args => head_reference_under_binders f
      | Constr.Unsafe.Cast c _ _ => head_reference_under_binders c
      | Constr.Unsafe.Lambda _ body => head_reference_under_binders body
      | Constr.Unsafe.Constant c inst => Val (Std.ConstRef c, term)
      | Constr.Unsafe.Var id => Val (Std.VarRef id, term)
      | _ => Err (Not_headed_by_a_constant_under_binders k)
      end.

    Module Cache.
      Ltac2 Type elem := { name : ident ; rterm : constr }.
      (* maps terms to elem *)
      Ltac2 Type t := (Fresh.Free.t * (constr * elem) list) ref.
      Ltac2 init (avoid : constr) : t
        := let avoid := Fresh.Free.union (Fresh.Free.of_constr avoid) (Fresh.Free.of_goal ()) in
           { contents := (avoid, []) }.
      Ltac2 find_opt (term : constr) (cache : t) : elem option
        := let (_, cache) := cache.(contents) in
           List.assoc_opt Constr.equal term cache.
      Ltac2 Type exn ::= [ Cache_contains_element (constr, constr, constr, elem) ].
      Ltac2 add (head_constant : constr) (term : constr) (rterm : constr) (cache : t) : ident (* newly bound name *)
        := let (avoid, known) := cache.(contents) in
           match List.assoc_opt Constr.equal term known with
           | Some e => Control.throw (Cache_contains_element head_constant term rterm e)

           | None
             => let id := Fresh.fresh avoid (Ident.reified_of_constr head_constant) in
                let avoid := Fresh.Free.union avoid (Fresh.Free.of_ids [id]) in
                let e := { name := id ; rterm := rterm } in
                (cache.(contents) := (avoid, (term, e) :: known));
                id
           end.
      Ltac2 elements (cache : t) : (constr * elem) list
        := let (_, cache) := cache.(contents) in
           cache.

      Ltac2 to_thunked_binder_context (cache : t) : (unit -> binder) list
        := List.rev (List.map (fun (_, e) () => Constr.Binder.make (Some (e.(Cache.name))) (Constr.type (e.(Cache.rterm)))) (Cache.elements cache)).
    End Cache.

    (* - [ctx_tys] is the list of binders that correspond to free de
         Bruijn variables; they're the binders in the source term
         we've gone underneath without extending the ambient context
         (for performance reasons)

       - [var_ty_ctx] is the corresponding list of reified types for
         the free de Bruijn variables

       - [value_ctx] is the mapping of free [Var]iables to reified
         types and [var] terms; it is the analogue of [var_ty_ctx] for
         binders that have been added to the ambient context

       - [template_ctx] is the list of deferred template parameters,
         application arguments we've peeled off but not yet reified
         because they are used dependently (e.g., arguments of type
         [Type] or [_ -> Type]) *)

    Ltac2 rec reify_in_context_opt (base_type : constr) (ident : constr) (reify_base_type : constr -> constr) (reify_ident_opt : binder list -> constr -> constr option) (var : constr) (term : constr) (ctx_tys : binder list) (var_ty_ctx : constr list) (value_ctx : (ident * constr (* ty *) * constr (* var *)) list) (template_ctx : constr list) (cache : Cache.t) : constr option :=
      let reify_rec_gen term ctx_tys var_ty_ctx template_ctx := reify_in_context_opt base_type ident reify_base_type reify_ident_opt var term ctx_tys var_ty_ctx value_ctx template_ctx cache in
      let reify_rec term := reify_rec_gen term ctx_tys var_ty_ctx template_ctx in
      let reify_rec_not_head term := reify_rec_gen term ctx_tys var_ty_ctx [] in
      let debug_check e
        := Reify.debug_Constr_check
             "expr.reify_in_context" (fun e e' err => Message.of_exn err) var
             (Cache.to_thunked_binder_context cache)
             var_ty_ctx e in
      let reify_ident_opt term
        := Option.map (fun idc => debug_check (mkApp '(@Ident) [base_type; ident; var; open_constr:(_); idc]))
                      (reify_ident_opt ctx_tys term) in
      Reify.debug_enter_reify "expr.reify_in_context" term;
      Reify.debug_print_args
        "expr.reify_in_context"
        (fun ()
         => fprintf
              "{ base_type= %t ; ident = %t ; var = %t ; term = %t ; ctx_tys = %a ; var_ty_ctx = %a ; value_ctx = %a ; template_ctx = %a }"
              base_type ident var term
              (fun () => Message.of_list (fun v => fprintf "%a : %t" (fun () a => a) (match Constr.Binder.name v with Some n => Message.of_ident n | None => Message.of_string "" end) (Constr.Binder.type v))) ctx_tys
              (fun () => Message.of_list Message.of_constr) var_ty_ctx
              (fun () => Message.of_list (fun (id, t, v) => fprintf "(%I, %t, %t)" id t v)) value_ctx
              (fun () => Message.of_list Message.of_constr) template_ctx) ();
      let found :=
        match Constr.Unsafe.kind term with
        | Constr.Unsafe.Rel n
          => Reify.debug_enter_reify_case "expr.reify_in_context" "Rel" term;
             let rt := List.nth var_ty_ctx (Int.sub n 1) in
             Some (debug_check (mkApp ('@Var) [base_type; ident; var; rt; term]))
        | Constr.Unsafe.Var id
          => Reify.debug_enter_reify_case "expr.reify_in_context" "Var" term;
             Reify.debug_fine_grained "expr.reify_in_context" (fun () => fprintf "Searching in %a" (fun () => Message.of_list (fun (id', x, y) => fprintf "(%I, %t, %t)" id' x y)) value_ctx);
             Option.bind
               (List.find_opt (fun (id', _, _) => Ident.equal id' id) value_ctx)
               (fun (_, rt, rv)
                => Some (debug_check (mkApp ('@Var) [base_type; ident; var; rt; rv])))
        | _ => None
        end in
      let res :=
        match found with
        | Some v => Some v
        | None
          => Reify.debug_enter_reify_case "expr.reify_in_context" "preprocess" term;
             let term := reify_preprocess ctx_tys term in
             Reify.debug_enter_reify_after_preprocess "expr.reify_in_context" term;
             let found :=
               match Constr.Unsafe.kind term with
               | Constr.Unsafe.Cast term _ _
                 => Reify.debug_enter_reify_case "expr.reify_in_context" "Cast" term;
                    Some (reify_rec term)
               | Constr.Unsafe.Lambda x f
                 => Some
                      (Reify.debug_enter_reify_case "expr.reify_in_context" "Lambda" term;
                       let t := Constr.Binder.type x in
                       if is_template_parameter ctx_tys t
                       then match template_ctx with
                            | arg :: template_ctx
                              => Reify.debug_enter_reify_case "expr.reify_in_context" "substnl template arg" term;
                                 reify_rec_gen (Constr.Unsafe.substnl [arg] 0 f) ctx_tys var_ty_ctx template_ctx
                            | []
                              => Control.throw (Reification_panic (fprintf "Empty template_ctx when reifying template binder of type %t" t))
                            end
                       else
                         (Reify.debug_enter_reify_case "expr.reify_in_context" "λ body" term;
                          let rt := type.reify reify_base_type base_type t in
                          let rx := Constr.Binder.make (Constr.Binder.name x) (debug_check (mkApp var [rt])) in
                          Option.map
                            (fun rf => debug_check (mkApp ('@Abs) [base_type; ident; var; rt; open_constr:(_); mkLambda rx rf]))
                            (reify_rec_gen f (x :: ctx_tys) (rt :: var_ty_ctx) template_ctx)))
               | Constr.Unsafe.App c args
                 => Reify.debug_enter_reify_case "expr.reify_in_context" "App (check LetIn)" term;
                    if Constr.equal c '@Let_In
                    then if Int.equal (Array.length args) 4
                         then Reify.debug_enter_reify_case "expr.reify_in_context" "LetIn" term;
                              let (ta, tb, a, b) := (Array.get args 0, Array.get args 1, Array.get args 2, Array.get args 3) in
                              Some
                                (Option.bind
                                   (reify_rec a)
                                   (fun ra
                                    => Option.bind
                                         (reify_rec b)
                                         (fun rb
                                          => lazy_match! rb with
                                             | @Abs _ _ _ ?s ?d ?f
                                               => Some (debug_check (mkApp ('@LetIn) [base_type; ident; var; s; d; ra; f]))
                                             | ?rb => Control.throw (Reification_panic (fprintf "Invalid non-Abs function reification of %t to %t" b rb))
                                             end)))
                         else None
                    else None
               | _ => None
               end in
             match found with
             | Some res => res
             | None
               => Reify.debug_enter_reify_case "expr.reify_in_context" "ident_preprocess" term;
                  let term := reify_ident_preprocess ctx_tys term in
                  Reify.debug_enter_reify_ident_after_preprocess "expr.reify_in_context" term;
                  match reify_ident_opt term with
                  | Some res => Some res
                  | None
                    => Reify.debug_enter_reify_case "expr.reify_in_context" "not ident" term;
                       lazy_match! term with
                       | ?f ?x
                         =>
                           Reify.debug_enter_reify_case "expr.reify_in_context" "App" term;
                           let x_is_template_arg
                             := match Control.case (fun () => Constr.type x) with
                                | Val ty
                                  => let (ty, _) := ty in
                                     is_template_parameter ctx_tys ty
                                | Err err
                                  => Reify.debug_typing_failure "expr.reify_in_context" x err;
                                     false
                                end in
                           if x_is_template_arg
                           then (* we can't reify things of type [Type], so we save it for later to plug in *)
                             Reify.debug_enter_reify_case "expr.reify_in_context" "accumulate template" term;
                             reify_rec_gen f ctx_tys var_ty_ctx (x :: template_ctx)
                           else
                             (Reify.debug_enter_reify_case "expr.reify_in_context" "App (non-template)" term;
                              Option.bind
                                (reify_rec_gen x ctx_tys var_ty_ctx [])
                                (fun rx
                                 => Option.bind
                                      (reify_rec_gen f ctx_tys var_ty_ctx template_ctx)
                                      (fun rf
                                       => Some (debug_check (mkApp '@App [base_type; ident; var; open_constr:(_); open_constr:(_); rf; rx])))))
                       | _
                         => Reify.debug_enter_reify_case "expr.reify_in_context" "pre-plug template_ctx" term;
                            let term := plug_template_ctx ctx_tys term template_ctx in
                            Reify.debug_enter_reify_case "expr.reify_in_context" "reify_ident_opt" term;
                            match reify_ident_opt term with
                            | Some res => Some res
                            | None
                              => match Cache.find_opt term cache with
                                 | Some id => Some (mkVar (id.(Cache.name)))
                                 | None
                                   => match head_reference_under_binders term with
                                      | Val c
                                        => let (c, h) := c in
                                           Reify.debug_enter_reify_case "expr.reify_in_context" "App Constant (unfold)" term;
                                           let term' := eval_cbv_delta_only [c] term in
                                           if Constr.equal term term'
                                           then printf "Unrecognized (non-unfoldable) term: %t" term;
                                                None
                                           else
                                             match reify_rec term' with
                                             | Some rv
                                               => let id := Cache.add h term rv cache in
                                                  Some (mkVar id)
                                             | None
                                               => printf "Failed to reify %t via unfolding to %t" term term';
                                                  None
                                             end
                                      | Err err => printf "Unrecognized (non-constant-headed) term: %t (%a)" term (fun () => Message.of_exn) err;
                                                   None
                                      end
                                 end
                            end
                       end
                  end
             end
        end in
      match res with
      | Some res
        => Reify.debug_leave_reify_success "expr.reify_in_context" term res;
           Some res
      | None
        => Reify.debug_leave_reify_failure "expr.reify_in_context" term;
           None
      end.

    Ltac2 reify_let_bind_cache (rterm : constr) (cache : Cache.t) : constr :=
      Reify.debug_profile
        "reify_let_bind_cache"
        (fun ()
         => let rec aux (elems : (_ * Cache.elem) list)
              := match elems with
                 | [] => rterm
                 | elem :: elems
                   => let (_, elem) := elem in
                      let (name, rv) := (elem.(Cache.name), elem.(Cache.rterm)) in
                      let rty := Constr.type rv in
                      let x := Constr.Binder.make (Some name) rty in
                      Reify.debug_let_bind "reify_let_bind_cache" name rty rv;
                      let rterm := Constr.in_context
                                     name rty (fun () => let v := aux elems in Control.refine (fun () => v)) in
                      let default () :=
                        printf "Warning: reify_let_bind_cache: not a lambda: %t" rterm;
                        rterm in
                      match Constr.Unsafe.kind rterm with
                      | Constr.Unsafe.Lambda x f
                        => mkLetIn x rv f
                      | _ => default ()
                      end
                 end in
            aux (List.rev (Cache.elements cache))).

    Ltac2 reify_in_context (base_type : constr) (ident : constr) (reify_base_type : constr -> constr) (reify_ident_opt : binder list -> constr -> constr option) (var : constr) (term : constr) (ctx_tys : binder list) (var_ty_ctx : constr list) (value_ctx : (ident * constr (* ty *) * constr (* var *)) list) (template_ctx : constr list) (cache : Cache.t option) : constr :=
      let cache := match cache with
                   | Some cache => cache
                   | None => Cache.init term
                   end in
      match Reify.debug_profile
              "reify_in_context_opt"
              (fun () => reify_in_context_opt base_type ident reify_base_type reify_ident_opt var term ctx_tys var_ty_ctx value_ctx template_ctx cache)
      with
      | Some v => reify_let_bind_cache v cache
      | None => Control.zero (Reification_failure (fprintf "Failed to reify: %t" term))
      end.

    Ltac2 reify (base_type : constr) (ident : constr) (reify_base_type : constr -> constr) (reify_ident_opt : binder list -> constr -> constr option) (var : constr) (term : constr) (cache : Cache.t option) : constr :=
      reify_in_context base_type ident reify_base_type reify_ident_opt var term [] [] [] [] cache.
    (* TODO: come up with a better naming convention than prefix [_] to replace starting-with-capital-letters *)
    (* TODO: figure out how to share the cache between multiple reifications *)
    Ltac2 _Reify (base_type : constr) (ident : constr) (reify_base_type : constr -> constr) (reify_ident_opt : binder list -> constr -> constr option) (term : constr) : constr :=
      let var := Fresh.fresh (Fresh.Free.union (Fresh.Free.of_goal ()) (Fresh.Free.of_constr term)) @var in
      Constr.in_context
        var '(type $base_type -> Type)
        (fun ()
         => let r := reify base_type ident reify_base_type reify_ident_opt (mkVar var) term None in
            Control.refine (fun () => r)).
    Ltac2 _Reify_rhs (base_type : constr) (ident : constr) (reify_base_type : constr -> constr) (reify_ident_opt : binder list -> constr -> constr option) (base_interp : constr) (interp_ident : constr) () : unit :=
      let rhs := lazy_match! goal with [ |- _ = ?rhs ] => rhs end in
      let r := _Reify base_type ident reify_base_type reify_ident_opt rhs in
      Std.transitivity '(@Interp $base_type $ident $base_interp $interp_ident _ $r)
      > [ | reflexivity ].

    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac reify_in_context base_type ident reify_base_type reify_ident var term value_ctx template_ctx :=
      let f := ltac2:(base_type ident reify_base_type reify_ident var term value_ctx template_ctx
                      |- let template_ctx := Ltac1.get_to_constr "template_ctx" template_ctx in
                         let value_ctx := Ltac1.get_to_constr "value_ctx" value_ctx in
                         Reify.debug_print_args
                           "ltac:expr.reify_in_context"
                           (fun () => fprintf "{ template_ctx = %t ; value_ctx = %t }" template_ctx value_ctx)
                           ();
                         let template_ctx := template_ctx_to_list template_ctx in
                         let value_ctx := value_ctx_to_list value_ctx in
                         let reify_base_type := fun ty => Ltac1.apply_c reify_base_type [ty] in
                         let reify_ident_opt := reify_ident_opt_of_cps reify_ident in
                         Control.refine (fun () => reify_in_context (Ltac1.get_to_constr "base_type" base_type) (Ltac1.get_to_constr "ident" ident) reify_base_type reify_ident_opt (Ltac1.get_to_constr "var" var) (Ltac1.get_to_constr "term" term) [] [] value_ctx template_ctx None)) in
      constr:(ltac:(f base_type ident reify_base_type ltac:(wrap_reify_ident_cps reify_ident) constr:(var) term value_ctx template_ctx)).
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac reify base_type ident reify_base_type reify_ident var term :=
      let f := ltac2:(base_type ident reify_base_type reify_ident var term
                      |- let reify_base_type := fun ty => Ltac1.apply_c reify_base_type [ty] in
                         let reify_ident_opt := reify_ident_opt_of_cps reify_ident in
                         Control.refine (fun () => reify (Ltac1.get_to_constr "base_type" base_type) (Ltac1.get_to_constr "ident" ident) reify_base_type reify_ident_opt (Ltac1.get_to_constr "var" var) (Ltac1.get_to_constr "term" term) None)) in
      constr:(ltac:(f base_type ident reify_base_type ltac:(wrap_reify_ident_cps reify_ident) constr:(var) term)).
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac Reify base_type ident reify_base_type reify_ident term :=
      let f := ltac2:(base_type ident reify_base_type reify_ident term
                      |- let reify_base_type := fun ty => Ltac1.apply_c reify_base_type [ty] in
                         let reify_ident_opt := reify_ident_opt_of_cps reify_ident in
                         Control.refine (fun () => _Reify (Ltac1.get_to_constr "base_type" base_type) (Ltac1.get_to_constr "ident" ident) reify_base_type reify_ident_opt (Ltac1.get_to_constr "term" term))) in
      constr:(ltac:(f base_type ident reify_base_type ltac:(wrap_reify_ident_cps reify_ident) term)).
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac Reify_rhs base_type ident reify_base_type reify_ident base_interp interp_ident _ :=
      let f := ltac2:(base_type ident reify_base_type reify_ident base_interp interp_ident
                      |- let reify_base_type := fun ty => Ltac1.apply_c reify_base_type [ty] in
                         let reify_ident_opt := reify_ident_opt_of_cps reify_ident in
                         _Reify_rhs (Ltac1.get_to_constr "base_type" base_type) (Ltac1.get_to_constr "ident" ident) reify_base_type reify_ident_opt (Ltac1.get_to_constr "base_interp" base_interp) (Ltac1.get_to_constr "interp_ident" interp_ident) ()) in
      f base_type ident reify_base_type ltac:(wrap_reify_ident_cps reify_ident) base_interp interp_ident.

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
