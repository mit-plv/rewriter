Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Require Rewriter.Util.Tactics2.Array.
Require Rewriter.Util.Tactics2.Proj.
Require Rewriter.Util.Tactics2.Option.
Require Import Rewriter.Util.Tactics2.Iterate.
Local Set Warnings Append "-masking-absolute-name".
Require Import Rewriter.Util.plugins.Ltac2Extra.
Import Ltac2.Constr.
Import Ltac2.Bool.

Ltac2 is_sort(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Sort _ => true
  | _ => false
  end.

Module Unsafe.
  Export Ltac2.Constr.Unsafe.

  Ltac2 rec kind_nocast_gen kind (x : constr) :=
    let k := kind x in
    match k with
    | Cast x _ _ => kind_nocast_gen kind x
    | _ => k
    end.

  Ltac2 kind_nocast (x : constr) : kind := kind_nocast_gen kind x.

  Module Case.
    Ltac2 iter_invert (f : constr -> unit) (ci : case_invert) : unit :=
      match ci with
      | NoInvert => ()
      | CaseInvert indices => Array.iter f indices
      end.
  End Case.

  (** [iter_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)
  Ltac2 iter_with_binders (g : 'a -> 'a) (f : 'a -> constr -> unit) (n : 'a) (c : constr) : unit :=
    match kind c with
    | Rel _ => () | Meta _ => () | Var _ => () | Sort _ => () | Constant _ _ => () | Ind _ _ => ()
    | Constructor _ _ => () | Uint63 _ => () | Float _ => ()
    | Cast c _ t => f n c; f n t
    | Prod b c => f n (Binder.type b); f (g n) c
    | Lambda b c => f n (Binder.type b); f (g n) c
    | LetIn b t c => f n (Binder.type b); f n t; f (g n) c
    | App c l => f n c; Array.iter (f n) l
    | Evar _ l => () (* not possible to iter in Ltac2... *)
    | Case _ x iv y bl
      => Array.iter (f n) bl;
         Case.iter_invert (f n) iv;
         f n x;
         f n y
    | Proj _p c => f n c
    | Fix _ _ tl bl =>
        Array.iter (fun b => f n (Binder.type b)) tl;
        Array.iter (f (iterate g (Array.length tl) n)) bl
    | CoFix _ tl bl =>
        Array.iter (fun b => f n (Binder.type b)) tl;
        Array.iter (f (iterate g (Array.length tl) n)) bl
    | Array _u t def ty =>
        Array.iter (f n) t; f n def; f n ty
    end.
End Unsafe.
Import Unsafe.

Ltac2 equal_nounivs : constr -> constr -> bool := Ltac2.Constr.equal_nounivs.
