Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Require Rewriter.Util.Tactics2.Char.

(** Special characters *)
Ltac2 null () : string := String.make 1 (Char.null ()).
Ltac2 backspace () : string := String.make 1 (Char.backspace ()).
Ltac2 tab () : string := String.make 1 (Char.tab ()).
Ltac2 lf () : string := String.make 1 (Char.lf ()).
Ltac2 newpage () : string := String.make 1 (Char.newpage ()).
Ltac2 cr () : string := String.make 1 (Char.cr ()).
Ltac2 escape () : string := String.make 1 (Char.escape ()).
Ltac2 newline () : string := String.make 1 (Char.newline ()).
