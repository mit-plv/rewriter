Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Require Import Rewriter.Util.Tactics2.Constr.
Require Import Rewriter.Util.Tactics2.Constr.Unsafe.MakeAbbreviations.
Require Export Rewriter.Util.FixCoqMistakes.

Module Constr.
  Export Ltac2.Constr.
  Export Tactics2.Constr.
  Module Unsafe.
    Export Tactics2.Constr.Unsafe.
    (** Pops [n] lambda abstractions, and pop letins only if needed to
        expose enough lambdas, skipping casts. *)
    Ltac2 decompose_lam_n_assum (n : int) (c : constr) : (binder * constr option) list * constr :=
      Control.assert_valid_argument "decompose_lam_n_assum: integer parameter must be positive." (Int.gt n 0);
      let rec lamdec_rec l n c :=
            if Int.equal n 0 then (l, c)
            else
              match kind_nocast c with
              | Lambda b c => lamdec_rec ((b, None) :: l) (Int.sub n 1) c
              | LetIn b v c => lamdec_rec ((b, Some v) :: l) n c
              | _ => Control.throw (Tactic_failure (Some (fprintf "decompose_lam_n_assum: not enough abstractions (want %i more): %t" n c)))
              end
      in
      lamdec_rec [] n c.
  End Unsafe.
End Constr.
