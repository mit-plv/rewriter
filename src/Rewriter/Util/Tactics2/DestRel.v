Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_rel (kind) ].
Ltac2 destRel (c : constr) :=
  let k := kind c in
  match k with
  | Rel i => i
  | _ => Control.throw (Not_a_rel k)
  end.
