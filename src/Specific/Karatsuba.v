Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import (*Crypto.Util.Tactics*) Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil Crypto.Util.Tactics.
Require Import Crypto.Arithmetic.Karatsuba.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.IdfunWithAlt.
Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

(***
Modulus : 2^448-2^224-1
Base: 56
***)
Section Ops51.
  Local Infix "^" := tuple : type_scope.

  (* These definitions will need to be passed as Ltac arguments (or
  cleverly inferred) when things are eventually automated *)
  Definition sz := 8%nat.
  Definition bitwidth := 64.
  Definition s : Z := 2^448.
  Definition c : list B.limb := [(1, 1); (2^224, 1)].
  Definition coef_div_modulus : nat := 2. (* add 2*modulus before subtracting *)
  Definition carry_chain1 := Eval vm_compute in (seq 0 (pred sz)).
  Definition carry_chain2 := ([0;1])%nat.
  Definition a24 := 121665%Z.

  (* These definitions are inferred from those above *)
  Definition m := Eval vm_compute in Z.to_pos (s - Associational.eval c). (* modulus *)
  Definition wt := fun i : nat =>
                     let si := Z.log2 s * i in
                     2 ^ ((si/sz) + (if dec ((si/sz)*sz=si) then 0 else 1)).
  Definition sz2 := Eval vm_compute in ((sz * 2) - 1)%nat.
  Definition m_enc :=
    Eval vm_compute in (Positional.encode (modulo:=modulo) (div:=div) (n:=sz) wt (s-Associational.eval c)).
  Definition coef := (* subtraction coefficient *)
    Eval vm_compute in
      ((fix addm (acc: Z^sz) (ctr : nat) : Z^sz :=
         match ctr with
         | O => acc
         | S n => addm (Positional.add_cps wt acc m_enc id) n
        end) (Positional.zeros sz) coef_div_modulus).
  Definition coef_mod : mod_eq m (Positional.eval (n:=sz) wt coef) 0 := eq_refl.

  Lemma sz_nonzero : sz <> 0%nat. Proof. vm_decide. Qed.
  Lemma wt_nonzero i : wt i <> 0.
  Proof.
    apply Z.pow_nonzero; zero_bounds; try break_match; vm_decide.
  Qed.

  Lemma wt_divides_chain1 i (H:In i carry_chain1) : wt (S i) / wt i <> 0.
  Proof.
    cbv [In carry_chain1] in H.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try (exfalso; assumption); subst; try vm_decide.
  Qed.
  Lemma wt_divides_chain2 i (H:In i carry_chain2) : wt (S i) / wt i <> 0.
  Proof.
    cbv [In carry_chain2] in H.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try (exfalso; assumption); subst; try vm_decide.
  Qed.
  Lemma wt_divides_full i : wt (S i) / wt i <> 0.
  Proof.
    cbv [wt].
    match goal with |- _ ^ ?x / _ ^ ?y <> _ => assert (0 <= y <= x) end.
    { rewrite Nat2Z.inj_succ.
      split; try break_match; ring_simplify;
      repeat match goal with
             | _ => apply Z.div_le_mono; try vm_decide; [ ]
             | _ => apply Z.mul_le_mono_nonneg_l; try vm_decide; [ ]
             | _ => apply Z.add_le_mono; try vm_decide; [ ]
             | |- ?x <= ?y + 1 => assert (x <= y); [|omega]
             | |- ?x + 1 <= ?y => rewrite <- Z.div_add by vm_decide
             | _ => progress zero_bounds
             | _ => progress ring_simplify
             | _ => vm_decide
             end. }
    break_match; rewrite <-Z.pow_sub_r by omega;
      apply Z.pow_nonzero; omega.
  Qed.

  Local Ltac solve_constant_sig :=
    lazymatch goal with
    | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
      => let t := (eval vm_compute in
                      (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt (F.to_Z (m:=M) v))) in
         (exists t; vm_decide)
    end.

  Definition zero_sig :
    { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}.
  Proof.
    solve_constant_sig.
  Defined.

  Definition one_sig :
    { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}.
  Proof.
    solve_constant_sig.
  Defined.

  Definition a24_sig :
    { a24t : Z^sz | Positional.Fdecode (m:=m) wt a24t = F.of_Z m a24 }.
  Proof.
    solve_constant_sig.
  Defined.

  Definition add_sig :
    { add : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m:=m) wt in
                 eval (add a b) = (eval a  + eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero.
    let x := constr:(
        Positional.add_cps (n := sz) wt a b id) in
    solve_op_F wt x. reflexivity.
  Defined.

  Definition sub_sig :
    {sub : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m:=m) wt in
                 eval (sub a b) = (eval a - eval b)%F}.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.sub_cps (n:=sz) (coef := coef) wt a b id) in
    solve_op_F wt x. reflexivity.
  Defined.

  Definition opp_sig :
    {opp : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (opp a) = F.opp (eval a)}.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.opp_cps (n:=sz) (coef := coef) wt a id) in
    solve_op_F wt x. reflexivity.
  Defined.

  Definition half_sz : nat := Eval compute in (sz / 2).
  Lemma half_sz_nonzero : half_sz <> 0%nat. Proof. cbv; congruence. Qed.

  Definition goldilocks_mul_sig :
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       mul a b = goldilocks_mul_cps (n:=half_sz) (n2:=sz) wt (2 ^ 224) a b id}.
  Proof.
    eexists; cbv beta zeta; intros.
    cbv [goldilocks_mul_cps].
    repeat autounfold.
    basesystem_partial_evaluation_RHS.
    do_replace_match_with_destructuring_match_in_goal.
    reflexivity.
  Defined.

  Definition goldilocks_mul_for_bounds_checker_sig :
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       mul a b = goldilocks_mul_cps_for_bounds_checker (n:=half_sz) (n2:=sz) wt (2 ^ 224) a b id}.
  Proof.
    eexists; cbv beta zeta; intros.
    cbv [goldilocks_mul_cps_for_bounds_checker].
    repeat autounfold.
    basesystem_partial_evaluation_RHS.
    do_replace_match_with_destructuring_match_in_goal.
    reflexivity.
  Defined.

  Lemma goldilocks_mul_sig_equiv a b :
    proj1_sig goldilocks_mul_sig a b =
    proj1_sig goldilocks_mul_for_bounds_checker_sig a b.
  Proof.
   rewrite (proj2_sig goldilocks_mul_sig).
   rewrite (proj2_sig goldilocks_mul_for_bounds_checker_sig).
   apply goldilocks_mul_equiv;
               auto using half_sz_nonzero, sz_nonzero, wt_nonzero.
  Qed.

  Definition mul_sig :
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (mul a b) = (eval a  * eval b)%F}.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero.
    let x := constr:(
               goldilocks_mul (n:=half_sz) (n2:=sz) wt (2^224) a b ) in
    F_mod_eq;
      transitivity (Positional.eval wt x); repeat autounfold;

   [
   | autorewrite with uncps push_id push_basesystem_eval;
     apply goldilocks_mul_correct; try assumption; cbv; congruence ].
   cbv [mod_eq]; apply f_equal2;
     [  | reflexivity ]; apply f_equal.
   cbv [goldilocks_mul].
   transitivity
     (Tuple.eta_tuple
      (fun a
       => Tuple.eta_tuple
            (fun b
             => id_tuple_with_alt
                  ((proj1_sig goldilocks_mul_sig) a b)
                  ((proj1_sig goldilocks_mul_for_bounds_checker_sig) a b))
            b)
      a).
   { cbv [proj1_sig goldilocks_mul_for_bounds_checker_sig goldilocks_mul_sig Tuple.eta_tuple Tuple.eta_tuple_dep sz Tuple.eta_tuple'_dep id_tuple_with_alt id_tuple'_with_alt];
       cbn [fst snd].
     reflexivity. }
   { rewrite !Tuple.strip_eta_tuple, !unfold_id_tuple_with_alt.
     rewrite (proj2_sig goldilocks_mul_sig). reflexivity. }
 Defined.

  Definition square_sig :
    {square : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (square a) = (eval a  * eval a)%F}.
  Proof.
    eexists; cbv beta zeta; intros.
    rewrite <-(proj2_sig mul_sig).
    apply f_equal.
    cbv [proj1_sig mul_sig].
    reflexivity.
  Defined.

  (* Performs a full carry loop (as specified by carry_chain) *)
  Definition carry_sig :
    {carry : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (carry a) = eval a}.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero. pose proof wt_divides_chain1.
    pose proof div_mod. pose proof wt_divides_chain2.
    let x := constr:(
               Positional.chained_carries_cps (n:=sz) (div:=div)(modulo:=modulo) wt a carry_chain1
                  (fun r => Positional.carry_reduce_cps (n:=sz) (div:=div) (modulo:=modulo) wt s c r
                  (fun rrr => Positional.chained_carries_cps (n:=sz) (div:=div) (modulo:=modulo) wt rrr carry_chain2 id
             ))) in
    solve_op_F wt x. reflexivity.
  Defined.

  Require Import Crypto.Arithmetic.Saturated.

  Section PreFreeze.
    Lemma wt_pos i : wt i > 0.
    Proof.
        apply Z.lt_gt.
        apply Z.pow_pos_nonneg; zero_bounds; try break_match; vm_decide.
    Qed.

    Lemma wt_multiples i : wt (S i) mod (wt i) = 0.
    Admitted.

    Lemma wt_divides_full_pos i : wt (S i) / wt i > 0.
    Proof.
        pose proof (wt_divides_full i).
        apply Z.div_positive_gt_0; auto using wt_pos.
        apply wt_multiples.
    Qed.
  End PreFreeze.

  Hint Opaque freeze : uncps.
  Hint Rewrite freeze_id : uncps.

  Definition freeze_sig :
    {freeze : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
         (0 <= Positional.eval wt a < 2 * Z.pos m)->
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (freeze a) = eval a}.
  Proof.
    eexists; cbv beta zeta; intros.
    pose proof wt_nonzero. pose proof wt_pos.
    pose proof div_mod. pose proof wt_divides_full_pos.
    pose proof wt_multiples.
    pose proof div_correct. pose proof modulo_correct.
    let x := constr:(freeze (n:=sz) wt (Z.ones bitwidth) m_enc a) in
    F_mod_eq;
      transitivity (Positional.eval wt x); repeat autounfold;
        [ | autorewrite with uncps push_id push_basesystem_eval;
            rewrite eval_freeze with (c:=c);
            try eassumption; try omega; try reflexivity;
            try solve [auto using B.Positional.select_id,
                       B.Positional.eval_select, zselect_correct];
            vm_decide].
   cbv[mod_eq]; apply f_equal2;
     [  | reflexivity ]; apply f_equal.
   cbv - [runtime_opp runtime_add runtime_mul runtime_shr runtime_and Let_In Z.add_get_carry Z.zselect].
   reflexivity.
  Defined.

  Definition ring_56 :=
    (Ring.ring_by_isomorphism
         (F := F m)
         (H := Z^sz)
         (phi := Positional.Fencode wt)
         (phi' := Positional.Fdecode wt)
         (zero := proj1_sig zero_sig)
         (one := proj1_sig one_sig)
         (opp := proj1_sig opp_sig)
         (add := proj1_sig add_sig)
         (sub := proj1_sig sub_sig)
         (mul := proj1_sig mul_sig)
         (phi'_zero := proj2_sig zero_sig)
         (phi'_one := proj2_sig one_sig)
         (phi'_opp := proj2_sig opp_sig)
         (Positional.Fdecode_Fencode_id
            (sz_nonzero := sz_nonzero)
            (div_mod := div_mod)
            wt eq_refl wt_nonzero wt_divides_full)
         (Positional.eq_Feq_iff wt)
         (proj2_sig add_sig)
         (proj2_sig sub_sig)
         (proj2_sig mul_sig)
      ).

(*
Eval cbv [proj1_sig add_sig] in (proj1_sig add_sig).
Eval cbv [proj1_sig sub_sig] in (proj1_sig sub_sig).
Eval cbv [proj1_sig opp_sig] in (proj1_sig opp_sig).
Eval cbv [proj1_sig mul_sig] in (proj1_sig mul_sig).
Eval cbv [proj1_sig carry_sig] in (proj1_sig carry_sig).
*)

End Ops51.
