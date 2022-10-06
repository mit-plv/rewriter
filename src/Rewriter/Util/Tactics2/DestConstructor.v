Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_constructor (kind) ].
Ltac2 destConstructor (c : constr) :=
  let k := kind c in
  match k with
  | Constructor e inst => (e, inst)
  | _ => Control.throw (Not_a_constructor k)
  end.
