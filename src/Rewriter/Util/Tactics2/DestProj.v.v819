Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_proj (kind) ].
Ltac2 destProj (c : constr) :=
  let k := kind c in
  match k with
  | Proj p v => (p, v)
  | _ => Control.throw (Not_a_proj k)
  end.
