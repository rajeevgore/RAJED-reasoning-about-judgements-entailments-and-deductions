Require Import List ListSet.
Import ListNotations.
Require Import ListSetNotations.

Require Import EqDec.
Require Import Utils.

Definition fun_agree {A B : Type} (f g : A -> B) (E : list A) : Prop :=
  forall x, x ∈ E -> f x = g x.

Lemma fun_agree_refl {A B : Type} (f : A -> B) (E : list A) : fun_agree f f E.
Proof. exact (fun x Hx => eq_refl). Qed.

Lemma fun_agree_mono {A B : Type} {f g : A -> B} {E F : list A} :
  E ⊆ F -> fun_agree f g F -> fun_agree f g E.
Proof.
  intros Hinc Hagr. intros x Hx. apply Hagr, Hinc, Hx.
Qed.

Lemma fun_agree_Empty {A B : Type} (f g : A -> B) : fun_agree f g [].
Proof. intros x Hx. contradiction. Qed.

Lemma fun_agree_Empty_iff {A B : Type} (f g : A -> B) : fun_agree f g [] <-> True.
Proof. split; intros; (tauto || apply fun_agree_Empty). Qed.

Lemma fun_agree_Union_iff {A B : Type} (f g : A -> B) (E F : list A) :
  (fun_agree f g E /\ fun_agree f g F) <-> fun_agree f g (E ++ F).
Proof.
  split.
  - intros [HE HF]. intros x Hx. rewrite in_app_iff in Hx.
    destruct Hx; [apply HE | apply HF]; assumption.
  - intro H. split; intros x Hx; apply H; rewrite in_app_iff;
      [constructor 1 | constructor 2]; assumption.
Qed.

Lemma fun_agree_multi_Union_iff {A B : Type} (f g : A -> B) (U : list (list A)) :
  (forall E, E ∈ U -> fun_agree f g E) <-> fun_agree f g (list_union U id).
Proof.
  induction U as [|E U]. simpl. rewrite fun_agree_Empty_iff. tauto.
  unfold list_union. simpl fold_right.
  rewrite <- fun_agree_Union_iff, <- IHU. split.
  - intro H. split.
    + apply H. now left.
    + intros F HF. apply H. now right.
  - intros H F HF. destruct HF as [HF|HF].
    + rewrite <- HF. tauto.
    + apply H. assumption.
Qed.

Lemma fun_agree_Singleton {A B : Type} {a : A} {f g : A -> B} :
  fun_agree f g [a] <-> f a = g a.
Proof.
  split.
  - intro H. apply H. constructor. reflexivity.
  - intros H x Hx. destruct Hx as [Hx|]; try contradiction. rewrite <- Hx. assumption.
Qed.

Lemma fun_agree_Inter_elim {A B : Type} (Aeq_dec : eq_dec A) (f g h : A -> B) (E F : list A) :
  (forall x, x ∈ (set_inter Aeq_dec E F) -> f x = g x) ->
  (forall x, x ∈ E -> f x = h x) ->
  (forall x, x ∉ E -> g x = h x) ->
  fun_agree f h E /\ fun_agree g h F.
Proof.
  intros Hag Hfh Hgh. split; [exact Hfh | idtac].
  intros x Hx. destruct (in_dec Aeq_dec x E) as [Hin|Hnin].
  - eapply eq_trans; [idtac | now apply Hfh].
    apply eq_sym. apply Hag. apply set_inter_iff. tauto.
  - apply Hgh. assumption.
Qed.

Lemma dec_fun_agree {A B : Type} (Beq_dec : eq_dec B) (E : list A) :
  forall (f g : A -> B), fun_agree f g E + {a : A | a ∈ E & f a <> g a}.
Proof.
  intros f g. induction E; try (left; now intros).
  destruct IHE as [Hfeq|Hnfeq].
  - destruct (Beq_dec (f a) (g a)) as [Heq|Hneq].
    + left. intros x Hx. destruct Hx as [Hx|Hx]; try now rewrite <- Hx.
      revert x Hx. assumption.
    + right. exists a; [now left | assumption].
  - destruct Hnfeq as [a0 Ha Hneq]. right. exists a0; [now right | assumption].
Qed.
