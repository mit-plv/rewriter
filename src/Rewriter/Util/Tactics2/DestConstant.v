Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_constant (kind) ].
Ltac2 destConstant (c : constr) :=
  let k := kind c in
  match k with
  | Constant e inst => (e, inst)
  | _ => Control.throw (Not_a_constant k)
  end.
