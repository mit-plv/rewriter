Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.

(* Drop once the minimum dependency has been bumpped to 8.17 *)
Ltac2 rec for_all2_aux (on_length_mismatch : 'a list -> 'b list -> bool) f xs ys :=
  match xs with
  | [] => match ys with
          | [] => true
          | y :: ys' => on_length_mismatch xs ys
          end
  | x :: xs'
    => match ys with
       | [] => on_length_mismatch xs ys
       | y :: ys'
         => match f x y with
            | true => for_all2_aux on_length_mismatch f xs' ys'
            | false => false
            end
       end
  end.

(* Drop once the minimum dependency has been bumpped to 8.17 *)
Ltac2 equal f xs ys := for_all2_aux (fun _ _ => false) f xs ys.
