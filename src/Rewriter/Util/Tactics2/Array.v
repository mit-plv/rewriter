Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Import Ltac2.Array.

Ltac2 rec for_all2_aux (p : 'a -> 'b -> bool) (a : 'a array) (b : 'b array) (pos : int) (len : int) :=
  if Int.equal len 0
  then true
  else if p (get a pos) (get b pos)
       then for_all2_aux p a b (Int.add pos 1) (Int.sub len 1)
       else false.

Ltac2 equal p a b :=
  let lena := length a in
  let lenb := length b in
  if Int.equal lena lenb
  then for_all2_aux p a b 0 lena
  else false.
