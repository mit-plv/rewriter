Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Require Export Rewriter.Util.FixCoqMistakes.
Require Rewriter.Util.Tactics2.List.

Ltac2 of_list (pr : 'a -> message) (ls : 'a list) : message
  := fprintf
       "[%a]"
       (fun () a => a)
       (match ls with
        | [] => fprintf ""
        | x :: xs
          => List.fold_left (fun init x => fprintf "%a, %a" (fun () a => a) init (fun () => pr) x) (pr x) xs
        end).

Ltac2 of_binder (b : binder) : message
  := fprintf "%a : %t" (fun () a => a) (match Constr.Binder.name b with
                                        | Some n => fprintf "%I" n
                                        | None => fprintf ""
                                        end)
             (Constr.Binder.type b).
