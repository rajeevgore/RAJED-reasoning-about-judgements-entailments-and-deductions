From Ksat Require Import defs.
From Ksat Require Import semantics.

Require Import List.
Import ListNotations.
Require Import Recdef.
Require Import Psatz.
Require Import String.
Open Scope string_scope.

Require Import Classical.

Inductive fml :=
  | varf (p : string)
  | negf (phi : fml)
  | andf (phi psi : fml)
  | orf (phi psi : fml)
  | implf (phi psi : fml)
  | boxf (phi : fml)
  | diaf (phi : fml).

Fixpoint fml_force (M : kripke) (w : world M) (xi : fml) : Prop :=
  match xi with
  | varf p        => val M w p
  | negf phi      => ~ fml_force M w phi
  | andf phi psi  => fml_force M w phi /\ fml_force M w psi
  | orf phi psi   => fml_force M w phi \/ fml_force M w psi
  | implf phi psi => fml_force M w phi -> fml_force M w psi
  | boxf phi      => forall w', rel M w w' -> fml_force M w' phi
  | diaf phi      => exists w', rel M w w' /\ fml_force M w' phi
  end.

Definition fml_sat (M : kripke) (w : world M) (G : list fml) : Prop :=
  forall phi, In phi G -> fml_force M w phi.

Definition fml_satable (G : list fml) : Prop :=
  exists (M : kripke) w, fml_sat M w G.

(* Definition fml_unsatable (G : list fml) : Prop :=
  forall (M : kripke) w, ~ fml_sat M w G. *)

Fixpoint to_nnf (xi : fml) : nnf :=
  match xi with
  | varf p        => var p
  | negf phi      => neg_nnf (to_nnf phi)
  | andf phi psi  => and (to_nnf phi) (to_nnf psi)
  | orf phi psi   => or (to_nnf phi) (to_nnf psi)
  | implf phi psi => or (neg_nnf (to_nnf phi)) (to_nnf psi)
  | boxf phi      => box (to_nnf phi)
  | diaf phi      => dia (to_nnf phi)
  end.

Theorem force_fml_nnf_iff (M : kripke) : forall w phi,
  fml_force M w phi <-> force M w (to_nnf phi).
Proof.
intros w phi. revert w. induction phi.
- tauto.
- simpl. setoid_rewrite IHphi. setoid_rewrite force_neg_not_iff. tauto.
- simpl. setoid_rewrite IHphi1. setoid_rewrite IHphi2. tauto.
- simpl. setoid_rewrite IHphi1. setoid_rewrite IHphi2. tauto.
- simpl. setoid_rewrite IHphi1. setoid_rewrite IHphi2.
  setoid_rewrite force_neg_not_iff. intro w. tauto.
- simpl. setoid_rewrite IHphi. tauto.
- simpl. setoid_rewrite IHphi. tauto.
Qed.

Theorem fml_sat_of_empty (M : kripke) w : fml_sat M w [].
Proof. unfold fml_sat. simpl. tauto. Qed.

Theorem sat_fml_nnf_iff (M : kripke) w : forall G,
  fml_sat M w G <-> sat M w (map to_nnf G).
Proof.
induction G as [|psi tl].
- simpl. pose proof (sat_of_empty M w).
  pose proof (fml_sat_of_empty M w). tauto.
- split.
  + intro H. simpl. intros phi Hphi. simpl in Hphi.
    destruct Hphi as [Hphil|Hphir].
    * rewrite <- Hphil. apply force_fml_nnf_iff. apply H.
      simpl. left. reflexivity.
    * assert (fml_sat M w tl). intros xi Hxi.
      apply H. simpl. right. assumption.
      apply IHtl; assumption.
  + intros H phi Hphi. destruct Hphi as [Hphil|Hphir].
    * apply force_fml_nnf_iff. apply H. rewrite Hphil. simpl. now left.
    * apply IHtl; try assumption. eapply sat_subset;
      [idtac|apply H]. apply incl_map, incl_tl, incl_refl.
Qed.

(* Theorem satable_fml_nnf_iff :
  forall G, fml_satable G <-> satable (map to_nnf G).
Proof.
intro G. unfold fml_satable, satable.
setoid_rewrite sat_fml_nnf_iff. tauto.
Qed. *)

(* Theorem unsatable_fml_nnf_iff (G : list fml) :
  fml_unsatable G <-> unsatable (map to_nnf G).
Proof.
split; intros H M w H0; apply (H M w);
apply sat_fml_nnf_iff in H0; assumption.
Qed. *)
