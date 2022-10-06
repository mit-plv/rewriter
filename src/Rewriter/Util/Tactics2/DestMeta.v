Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_meta (kind) ].
Ltac2 destMeta (c : constr) :=
  let k := kind c in
  match k with
  | Meta e => e
  | _ => Control.throw (Not_a_meta k)
  end.
