Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Require Ltac2.Ltac1.
Require Export Rewriter.Util.FixCoqMistakes.

Ltac2 of_constr (refine_to_named_lambda : Ltac1.t -> unit) (c : constr) : ident
  := let default () := Control.throw (Tactic_failure (Some (fprintf "Ident.of_constr: failure to make a name from %t" c))) in
     match Constr.Unsafe.kind '(ltac2:(refine_to_named_lambda (Ltac1.of_constr c))) with
     | Constr.Unsafe.Lambda x _
       => match Constr.Binder.name x with
          | Some id => id
          | None => default ()
          end
     | _ => default ()
     end.
