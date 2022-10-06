Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Constr.Unsafe.

Ltac2 Type exn ::= [ Not_a_var (kind) ].
Ltac2 destVar (c : constr) :=
  let k := kind c in
  match k with
  | Var v => v
  | _ => Control.throw (Not_a_var k)
  end.
