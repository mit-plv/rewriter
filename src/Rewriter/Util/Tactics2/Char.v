Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.

(** Special characters *)
Ltac2 null () : char := Char.of_int 0.
Ltac2 backspace () : char := Char.of_int 8.
Ltac2 tab () : char := Char.of_int 9.
Ltac2 lf () : char := Char.of_int 10.
Ltac2 newpage () : char := Char.of_int 12.
Ltac2 cr () : char := Char.of_int 13.
Ltac2 escape () : char := Char.of_int 27.
Ltac2 newline () : char := Char.of_int 10.
