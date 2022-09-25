Require Import Ltac2.Ltac2.
Require Export Rewriter.Util.FixCoqMistakes.
Require Rewriter.Util.Tactics2.Array.
Require Rewriter.Util.Tactics2.Proj.
Require Rewriter.Util.Tactics2.Option.
Import Ltac2.Constr.
Import Ltac2.Bool.

Ltac2 is_sort(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Sort _ => true
  | _ => false
  end.

Import Constr.Unsafe.

Ltac2 rec kind_nocast_gen kind (x : constr) :=
  let k := kind x in
  match k with
  | Cast x _ _ => kind_nocast_gen kind x
  | _ => k
  end.

Ltac2 rec equal_nounivs (x : constr) (y : constr) : bool :=
  let kind := kind_nocast_gen kind in
  if Constr.equal x y
  then true
  else match kind x with
       | Cast x _ _ => equal_nounivs x y
       | App fx xs
         => match kind y with
            | App fy ys
              => equal_nounivs fx fy
                 && Array.equal equal_nounivs xs ys
            | _ => false
            end
       | Rel _ => false
       | Var _ => false
       | Meta _ => false
       | Uint63 _ => false
       | Float _ => false
       | Evar ex instx
         => match kind y with
            | Evar ey insty
              => let inst := Array.empty () in
                 if Constr.equal (make (Evar ex inst)) (make (Evar ey inst))
                 then Array.equal equal_nounivs instx insty
                 else false
            | _ => false
            end
       | Sort sx
         => match kind y with
            | Sort sy => true
            | _ => false
            end
       | Prod xb fx
         => match kind y with
            | Prod yb fy
              => equal_nounivs (Binder.type xb) (Binder.type yb) && equal_nounivs fx fy
            | _ => false
            end
       | Lambda xb fx
         => match kind y with
            | Lambda yb fy
              => equal_nounivs (Binder.type xb) (Binder.type yb) && equal_nounivs fx fy
            | _ => false
            end
       | LetIn xb xv fx
         => match kind y with
            | LetIn yb yv fy
              => equal_nounivs (Binder.type xb) (Binder.type yb) && equal_nounivs xv yv && equal_nounivs fx fy
            | _ => false
            end
       | Constant cx instx
         => match kind y with
            | Constant cy insty
              => Constr.equal (make (Constant cx instx)) (make (Constant cy instx))
            | _ => false
            end
       | Ind ix instx
         => match kind y with
            | Ind iy insty
              => Ind.equal ix iy
            | _ => false
            end
       | Constructor cx instx
         => match kind y with
            | Constructor cy insty
              => Constr.equal (make (Constructor cx instx)) (make (Constructor cy instx))
            | _ => false
            end
       | Fix xa xi xb xf
         => match kind y with
            | Fix ya yi yb yf
              => Array.equal Int.equal xa ya
                 && Int.equal xi yi
                 && Array.equal (fun b1 b2 => equal_nounivs (Binder.type b1) (Binder.type b2)) xb yb
                 && Array.equal equal_nounivs xf yf
            | _ => false
            end
       | CoFix xi xb xf
         => match kind y with
            | CoFix yi yb yf
              => Int.equal xi yi
                 && Array.equal (fun b1 b2 => equal_nounivs (Binder.type b1) (Binder.type b2)) xb yb
                 && Array.equal equal_nounivs xf yf
            | _ => false
            end
       | Proj px cx
         => match kind y with
            | Proj py cy
              => Proj.equal px py && equal_nounivs cx cy
            | _ => false
            end
       | Array _ x1 x2 x3
         => match kind y with
            | Array _ y1 y2 y3
              => Array.equal equal_nounivs x1 y1
                 && equal_nounivs x2 y2
                 && equal_nounivs x3 y3
            | _ => false
            end
       | Case cx x1 cix x2 x3
         => match kind y with
            | Case cy y1 ciy y2 y3
              => Option.equal (Array.equal equal_nounivs)
                              (match cix with
                               | NoInvert => None
                               | CaseInvert cix => Some cix
                               end)
                              (match cix with
                               | NoInvert => None
                               | CaseInvert ciy => Some ciy
                               end)
                 && equal_nounivs x1 y1
                 && equal_nounivs x2 y2
                 && Array.equal equal_nounivs x3 y3
            | _ => false
            end
       end.
