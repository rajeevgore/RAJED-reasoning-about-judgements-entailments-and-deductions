Require Import utils.
Require Import nnf.
Require Import seqt.
Require Import semantics.

Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Require Import Classical.


Inductive fml :=
  | varf (p : string)
  | negf (phi : fml)
  | andf (phi psi : fml)
  | orf (phi psi : fml)
  | implf (phi psi : fml)
  | alwf (phi : fml)
  | evef (phi : fml)
  | beff (phi psi : fml)
  | untf (phi psi : fml)
  | nextf (phi : fml).


Fixpoint fml_force (M : kripke) (i : nat) (xi : fml) : Prop :=
  match xi with
  | varf p        => val M (kseq M i) p
  | negf phi      => ~ fml_force M i phi
  | andf phi psi  => fml_force M i phi /\ fml_force M i psi
  | orf phi psi   => fml_force M i phi \/ fml_force M i psi
  | implf phi psi => fml_force M i phi -> fml_force M i psi
  | alwf phi      => forall k, k >= i -> fml_force M k phi
  | evef phi      => exists k, k >= i /\ fml_force M k phi
  | beff phi psi  => forall k, k >= i -> fml_force M k psi ->
      exists j, i <= j < k /\ fml_force M j phi
  | untf phi psi  => exists k, k >= i /\ fml_force M k psi /\
      forall j, i <= j < k -> fml_force M j phi
  | nextf phi     => fml_force M (S i) phi
  end.

Definition fml_sat (M : kripke) (i : nat) (G : list fml) : Prop :=
  forall phi, In phi G -> fml_force M i phi.

Definition fml_satable (G : list fml) : Prop := exists M i, fml_sat M i G.


Fixpoint to_nnf (xi : fml) : nnf :=
  match xi with
  | varf p        => var p
  | negf phi      => neg_nnf (to_nnf phi)
  | andf phi psi  => and (to_nnf phi) (to_nnf psi)
  | orf phi psi   => or (to_nnf phi) (to_nnf psi)
  | implf phi psi => or (neg_nnf (to_nnf phi)) (to_nnf psi)
  | alwf phi      => bef (nnf_false) (neg_nnf (to_nnf phi))
  | evef phi      => unt (nnf_true) (to_nnf phi)
  | beff phi psi  => bef (to_nnf phi) (to_nnf psi)
  | untf phi psi  => unt (to_nnf phi) (to_nnf psi)
  | nextf phi     => next (to_nnf phi)
  end.


(* The rest requires XM *)

Theorem force_fml_nnf_iff : forall M phi i,
  fml_force M i phi <-> force M i (to_nnf phi).
Proof.
  intros M phi. induction phi.
  - simpl. tauto.
  - simpl. setoid_rewrite IHphi.
    setoid_rewrite force_neg_not_iff. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2.
    setoid_rewrite force_neg_not_iff. intro i. tauto.
  - unfold to_nnf. fold (to_nnf phi).
    remember (nnf_false) as F.
    simpl.
    setoid_rewrite force_neg_not_iff.
    setoid_rewrite <- IHphi.
    intro i. split.
    + intro H. intros k kgei H0. contradict H0.
      apply H. assumption.
    + intro H. intros k kgei. apply NNPP. intro H0.
      destruct (H k kgei H0) as [j [_ Hj]].
      apply (@nnf_false_is_false M j).
      rewrite HeqF in Hj. assumption.
  - unfold to_nnf. fold (to_nnf phi).
    remember (nnf_true) as T.
    simpl. setoid_rewrite <- IHphi. intro i. split.
    + intro H. destruct H as [k [kgei Hk]].
      exists k. repeat (split; try assumption).
      intros j ilejltk. rewrite HeqT.
      apply nnf_true_is_true.
    + intro H. destruct H as [k [kgei [H _]]].
      exists k. split; assumption.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2. tauto.
  - simpl. setoid_rewrite IHphi. tauto.
Qed.

Theorem sat_fml_nnf_iff : forall M G i,
  fml_sat M i G <-> sat M i (map to_nnf G).
Proof.
  intros M G. induction G as [|phi G].
  - intro i. split.
    + intro H. intros phi Hphi. contradict Hphi.
    + intro H. intros phi Hphi. contradict Hphi.
  - intro i. split.
    + intro H. intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * rewrite <- Hpsi. apply force_fml_nnf_iff.
        apply H. now left.
      * apply IHG; try assumption.
        intros xi Hxi. apply H. now right.
    + intro H. intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * rewrite <- Hpsi. apply force_fml_nnf_iff.
        apply H. now left.
      * apply IHG; try assumption.
        intros xi Hxi. apply H. now right.
Qed.
