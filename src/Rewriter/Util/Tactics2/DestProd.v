Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_prod (kind) ].
Ltac2 destProd (c : constr) :=
  let k := kind c in
  match k with
  | Prod x f => (x, f)
  | _ => Control.throw (Not_a_prod k)
  end.
