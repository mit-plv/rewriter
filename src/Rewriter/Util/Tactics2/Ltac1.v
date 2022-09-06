Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.

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
