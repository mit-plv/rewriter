Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_an_app (kind) ].
Ltac2 destApp (c : constr) :=
  let k := kind c in
  match k with
  | App f args => (f, args)
  | _ => Control.throw (Not_an_app k)
  end.
