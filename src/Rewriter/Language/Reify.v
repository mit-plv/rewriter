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
    Ltac2 Type exn ::= [ Not_a_constr (string, Ltac1.t) ].
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac2 get_to_constr (debug_name : string) v :=
      match Ltac1.to_constr v with
      | Some v => v
      | None => Control.throw (Not_a_constr debug_name v)
      end.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac2 apply_c (f : Ltac1.t) (args : constr list) : constr :=
      '(ltac2:(Ltac1.apply f (List.map Ltac1.of_constr args) (fun v => Control.refine (fun () => get_to_constr "apply_c:arg" v)))).
  End Ltac1.
  (* TODO: move to Util *)
  Ltac2 mkApp (f : constr) (args : constr list) :=
    Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list args)).
  Ltac2 mkLambda b (body : constr) :=
    Constr.Unsafe.make (Constr.Unsafe.Lambda b body).
  Ltac2 mkRel (i : int) :=
    Constr.Unsafe.make (Constr.Unsafe.Rel i).
  Ltac2 mkVar (i : ident) :=
    Constr.Unsafe.make (Constr.Unsafe.Var i).

  (* TODO: move *)
  Module Message.
    Ltac2 of_list (pr : 'a -> message) (ls : 'a list) : message
      := fprintf
           "[%a]"
           (fun () a => a)
           (match ls with
            | [] => fprintf ""
            | x :: xs
              => List.fold_left (fun init x => fprintf "%a, %a" (fun () a => a) init (fun () => pr) x) xs (pr x)
            end).
    Ltac2 of_binder (b : binder) : message
      := fprintf "%a : %t" (fun () a => a) (match Constr.Binder.name b with
                                            | Some n => fprintf "%I" n
                                            | None => fprintf ""
                                            end)
                 (Constr.Binder.type b).
  End Message.

  (* this is very super-linear, should not be used in production code *)
  Ltac2 with_term_in_context (tys : constr list) (term : constr) (tac : constr -> unit) : unit :=
    printf "Warning: with_term_in_context: Bad asymptotics";
    let rec aux (tys : constr list) (acc : ident list) (avoid : Fresh.Free.t)
      := match tys with
         | [] => tac (Constr.Unsafe.substnl (List.map mkVar (List.rev acc)) 0 term)
         | ty :: tys
           => let id := Fresh.fresh avoid @DUMMY in
              let avoid := Fresh.Free.union avoid (Fresh.Free.of_ids [id]) in
              let _ := Constr.in_context id ty (fun () => aux tys (id :: acc) avoid; Control.refine (fun () => 'I)) in
              ()
         end in
    aux tys [] (Fresh.Free.of_constr term).

  Module Reify.
    Ltac2 debug_level := Pre.reify_debug_level.

    Ltac2 mutable should_debug_enter_reify () := Int.le 2 debug_level.
    Ltac2 mutable should_debug_enter_reify_preprocess () := Int.le 2 debug_level.
    Ltac2 mutable should_debug_enter_reify_ident_preprocess () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_enter_reify_after_preprocess () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_leave_reify_success () := Int.le 5 debug_level.
    Ltac2 mutable should_debug_leave_reify_failure () := Int.le 0 debug_level.
    Ltac2 mutable should_debug_leave_reify_normal_failure () := Int.le 5 debug_level.
    Ltac2 mutable should_debug_enter_reify_ident_after_preprocess () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_enter_lookup_ident () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_success () := Int.le 3 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_failure_verbose () := Int.le 5 debug_level.
    Ltac2 mutable should_debug_leave_lookup_ident_failure () := Int.le 4 debug_level.
    Ltac2 mutable should_debug_enter_plug_template_ctx () := Int.le 6 debug_level.
    Ltac2 mutable should_debug_enter_reify_case () := Int.le 6 debug_level.
    Ltac2 mutable should_debug_fine_grained () := Int.le 100 debug_level.
    Ltac2 mutable should_debug_print_args () := Int.le 50 debug_level.
    Ltac2 mutable should_debug_typing_failure () := Int.le 1 debug_level.
    Ltac2 mutable should_debug_check_app_early () := Int.le 5 debug_level.

    Ltac2 debug_if (cond : unit -> bool) (tac : unit -> 'a) (default : 'a) :=
      if cond ()
      then tac ()
      else default.

    Ltac2 debug_typing_failure (funname : string) (x : constr) (err : exn)
      := debug_if should_debug_typing_failure (fun () => printf "Warning: %s: failure to typecheck %t: %a" funname x (fun () => Message.of_exn) err) ().
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
    Ltac2 debug_print_args (funname : string) (pr : 'a -> message) (args : 'a)
      := debug_if should_debug_print_args (fun () => printf "%s: args: %a" funname (fun () => pr) args) ().

    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_in_context term :=
      let f := ltac2:(term |- debug_enter_reify "expr.reify_in_context" (Ltac1.get_to_constr "term" term)) in
      f term.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_in_context_after_preprocess term :=
      let f := ltac2:(term |- debug_enter_reify_after_preprocess "expr.reify_in_context" (Ltac1.get_to_constr "term" term)) in
      f term.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_enter_reify_ident_after_preprocess term :=
      let f := ltac2:(term |- debug_enter_reify_ident_after_preprocess "expr.reify_in_context" (Ltac1.get_to_constr "term" term)) in
      f term.
    #[deprecated(since="8.15",note="Use Ltac2 instead.")]
     Ltac debug_leave_reify_in_context_success term res :=
      let f := ltac2:(term res |- debug_leave_reify_success "expr.reify_in_context" (Ltac1.get_to_constr "term" term) (Ltac1.get_to_constr "res" res)) in
      f term res.
    Ltac2 debug_Constr_check (funname : string) (descr : constr -> constr -> exn -> message) (var : constr) (var_ty_ctx : constr list) (e : constr)
      := debug_if
           should_debug_check_app_early
           (fun () => match Constr.Unsafe.check e with
                      | Val e => e
                      | Err _
                        => with_term_in_context
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
           let v := mkApp (mkLambda x b) [a] in
           match Constr.Unsafe.check v (* ensure that the abstraction is well-typed, i.e., that we're not relying on the value of the let to well-type the body *) with
           | Val v => reify_preprocess v
           | Err err (* if we do rely on the body of [x] to well-type [b], then just inline it *)
             => match Constr.Unsafe.check term with
                | Val _ => Reify.debug_typing_failure "expr.reify_preprocess" v err
                | Err _ => printf "Warning: expr.reify_preprocess: could not well-type %t due to underlying issue typechecking %t without relevant context %a" v term (fun () => Message.of_list Message.of_binder) ctx_tys
                end;
                reify_preprocess (Constr.Unsafe.substnl [a] 0 b)
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
