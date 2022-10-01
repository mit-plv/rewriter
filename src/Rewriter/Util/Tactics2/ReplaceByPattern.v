Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Require Import Rewriter.Util.Tactics2.Constr.
Require Import Rewriter.Util.Tactics2.Constr.Unsafe.MakeAbbreviations.
Require Import Rewriter.Util.Tactics2.DecomposeLambda.
Require Rewriter.Util.Tactics2.Message.
Import Ltac2.Constr.Unsafe Tactics2.Constr.Unsafe DecomposeLambda.Constr.Unsafe.

Module Constr.
  Export Ltac2.Constr Tactics2.Constr DecomposeLambda.Constr.
  Module Unsafe.
    Export Ltac2.Constr.Unsafe Tactics2.Constr.Unsafe DecomposeLambda.Constr.Unsafe.

    Ltac2 replace_by_pattern (from : constr list) (to : constr list) (term : constr) : constr :=
      Control.assert_valid_argument "replace_by_pattern" (Int.gt (List.length from) 0);
      Control.assert_valid_argument "replace_by_pattern" (Int.equal (List.length from) (List.length to));
      let term := Std.eval_pattern (List.map (fun c => (c, Std.AllOccurrences)) from) term in
      match kind_nocast term with
      | App term args
        => let (_, term) := decompose_lam_n_assum (List.length from) term in
           substnl (List.rev to) 0 term
      | _ => Control.throw (Tactic_failure (Some (fprintf "pattern returned non-app: %t" term)))
      end.
  End Unsafe.

  Ltac2 replace_by_pattern (from : constr list) (to : constr list) (term : constr) : constr :=
    match Constr.Unsafe.check (Unsafe.replace_by_pattern from to term) with
    | Val v => v
    | Err err
      => Control.zero (Tactic_failure (Some (fprintf "Could not replace %a with %a in %t: %a" (fun () => Message.of_list Message.of_constr) from (fun () => Message.of_list Message.of_constr) to term (fun () => Message.of_exn) err)))
    end.
End Constr.
