Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.

Ltac2 equal (eq : 'a -> 'b -> bool) (a : 'a option) (b : 'b option) : bool
  := match a with
     | None => match b with
               | None => true
               | _ => false
               end
     | Some a => match b with
                 | Some b => eq a b
                 | _ => false
                 end
     end.
