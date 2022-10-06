Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.

Ltac2 in_evar (e : evar) (t : unit -> unit) : unit :=
  Control.new_goal e >
    [ ..
    | t (); Control.shelve () ].

Module Evar.
  Ltac2 instantiate (e : evar) (c : unit -> constr) : unit :=
    in_evar e (fun () => Control.refine c).
End Evar.
