Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_an_ind (kind) ].
Ltac2 destInd (c : constr) :=
  let k := kind c in
  match k with
  | Ind e inst => (e, inst)
  | _ => Control.throw (Not_an_ind k)
  end.
