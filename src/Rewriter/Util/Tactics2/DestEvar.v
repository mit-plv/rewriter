Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_an_evar (kind) ].
Ltac2 destEvar (c : constr) :=
  let k := kind c in
  match k with
  | Evar e inst => (e, inst)
  | _ => Control.throw (Not_an_evar k)
  end.
