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

(* Drop once the minimum dependency has been bumpped to 8.19 *)
Ltac2 rec fold_right (f : 'a -> 'b -> 'b) (ls : 'a list) (a : 'b) : 'b :=
  match ls with
  | [] => a
  | l :: ls => f l (fold_right f ls a)
  end.

(* Drop once the minimum dependency has been bumpped to 8.19 *)
Ltac2 rec fold_left (f : 'a -> 'b -> 'a) (a : 'a) (xs : 'b list) : 'a :=
  match xs with
  | [] => a
  | x :: xs => fold_left f (f a x) xs
  end.
