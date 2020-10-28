Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Global Instance list_rect_Proper_dep_gen {A P} (RP : forall x : list A, P x -> P x -> Prop)
  : Proper (RP nil ==> forall_relation (fun x => forall_relation (fun xs => RP xs ==> RP (cons x xs))) ==> forall_relation RP) (@list_rect A P) | 10.
Proof.
  cbv [forall_relation respectful]; intros N N' HN C C' HC ls.
  induction ls as [|l ls IHls]; cbn [list_rect];
    repeat first [ apply IHls | apply HC | apply HN | progress intros | reflexivity ].
Qed.
Global Instance list_rect_Proper_dep {A P} : Proper (eq ==> forall_relation (fun _ => forall_relation (fun _ => forall_relation (fun _ => eq))) ==> forall_relation (fun _ => eq)) (@list_rect A P) | 1.
Proof.
  cbv [forall_relation respectful Proper]; intros; eapply (@list_rect_Proper_dep_gen A P (fun _ => eq)); cbv [forall_relation respectful]; intros; subst; eauto.
Qed.
Global Instance list_rect_Proper_gen {A P} R
  : Proper (R ==> (eq ==> eq ==> R ==> R) ==> eq ==> R) (@list_rect A (fun _ => P)) | 10.
Proof. repeat intro; subst; apply (@list_rect_Proper_dep_gen A (fun _ => P) (fun _ => R)); cbv [forall_relation respectful] in *; eauto. Qed.
Global Instance list_rect_Proper {A P} : Proper (eq ==> pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq)) ==> eq ==> eq) (@list_rect A (fun _ => P)).
Proof. repeat intro; subst; apply (@list_rect_Proper_dep A (fun _ => P)); eauto. Qed.
