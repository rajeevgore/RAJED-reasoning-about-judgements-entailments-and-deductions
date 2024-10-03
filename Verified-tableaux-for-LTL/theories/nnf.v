Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import String.
Open Scope string_scope.


Set Implicit Arguments.

Inductive nnf : Type :=
  | var (p : string)
  | neg (p : string)
  | and (phi psi : nnf)
  | or (phi psi : nnf)
  | bef (phi psi : nnf)
  | unt (phi psi : nnf)
  | next (phi : nnf).


Definition nnf_true  := or (var "") (neg "").
Definition nnf_false := and (var "") (neg "").

Definition nnf_eqdec (phi psi : nnf) : {phi = psi} + {phi <> psi}.
Proof. decide equality; apply string_dec. Defined.

Definition erase_nnf := set_remove nnf_eqdec.
Definition inter_nnf := set_inter nnf_eqdec.
Definition remove_nnf := remove nnf_eqdec.

Fixpoint neg_nnf (xi : nnf) : nnf :=
  match xi with
  | var p       => neg p
  | neg p       => var p
  | and phi psi => or (neg_nnf phi) (neg_nnf psi)
  | or phi psi  => and (neg_nnf phi) (neg_nnf psi)
  | bef phi psi => unt (neg_nnf phi) psi
  | unt phi psi => bef (neg_nnf phi) psi
  | next phi    => next (neg_nnf phi)
  end.

Definition nnf_isalpha (phi : nnf) : Prop :=
  match phi with
  | and _ _ => True
  | bef _ _ => True
  | _       => False
  end.

Definition nnf_isalpha_dec (phi : nnf) :
  {nnf_isalpha phi} + {~ nnf_isalpha phi}.
Proof. destruct phi; ((now left)||(now right)). Defined.

Definition get_alpha : forall G : list nnf,
  {phi : nnf | In phi G /\ nnf_isalpha phi} +
  {forall phi, In phi G -> ~ nnf_isalpha phi}.
Proof.
induction G as [|phi G'].
- right. simpl. tauto.
- destruct IHG' as [Hl|Hr].
  + left. destruct Hl as [psi Hin]. exists psi. simpl. tauto.
  + destruct (nnf_isalpha_dec phi) as [Halpha|Hnalpha].
    * left. exists phi. split; [now left|assumption].
    * right. intros psi H. destruct H as [H|H];
      [rewrite <- H|apply Hr]; assumption.
Defined.

Definition df_nnf : nnf := var "". (* an arbitrary default formula *)

Definition nnf_alpha1 (xi : nnf) : nnf :=
  match xi with
  | and phi psi => phi
  | bef phi psi => neg_nnf psi
  | _       => df_nnf
  end.

Definition nnf_alpha2 (xi : nnf) : nnf :=
  match xi with
  | and phi psi => psi
  | bef phi psi => or phi (next (bef phi psi))
  | _       => df_nnf
  end.

Definition nnf_isbeta (phi : nnf) : Prop :=
  match phi with
  | or _ _  => True
  | unt _ _ => True
  | _       => False
  end.

Definition nnf_isbeta_dec (phi : nnf) :
  {nnf_isbeta phi} + {~ nnf_isbeta phi}.
Proof. destruct phi; ((now left)||(now right)). Defined.

Definition get_beta : forall G : list nnf,
  {phi : nnf | In phi G /\ nnf_isbeta phi} +
  {forall phi, In phi G -> ~ nnf_isbeta phi}.
Proof.
induction G as [|phi G'].
- right. simpl. tauto.
- destruct IHG' as [Hl|Hr].
  + left. destruct Hl as [psi Hin]. exists psi. simpl. tauto.
  + destruct (nnf_isbeta_dec phi) as [Hbeta|Hnbeta].
    * left. exists phi. split; [now left|assumption].
    * right. intros psi H. destruct H as [H|H];
      [rewrite <- H|apply Hr]; assumption.
Defined.

Definition nnf_beta1 (xi : nnf) : nnf :=
  match xi with
  | or phi psi  => phi
  | unt phi psi => psi
  | _       => df_nnf
  end.

Definition nnf_beta2 (xi : nnf) : nnf :=
  match xi with
  | or phi psi  => psi
  | unt phi psi => and phi (next (unt phi psi))
  | _       => df_nnf
  end.

Lemma beta_not_alpha [phi] : nnf_isbeta phi -> ~ nnf_isalpha phi.
Proof. destruct phi; simpl; tauto. Qed.
