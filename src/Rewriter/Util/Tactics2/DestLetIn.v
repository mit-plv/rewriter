Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_let_in (kind) ].
Ltac2 destLetIn (c : constr) :=
  let k := kind c in
  match k with
  | LetIn x y z => (x, y, z)
  | _ => Control.throw (Not_a_let_in k)
  end.
