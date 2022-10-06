Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.

Ltac2 in_evar (e : evar) (t : unit -> 'a) : 'a :=
  let cell : 'a option ref := { contents := None } in
  Control.new_goal e >
    [ ..
    | let v := t () in cell.(contents) := Some v; Control.shelve () ];
  Option.get (cell.(contents)).

Module Evar.
  Ltac2 instantiate (e : evar) (c : unit -> constr) : unit :=
    in_evar e (fun () => Control.refine c).
End Evar.
