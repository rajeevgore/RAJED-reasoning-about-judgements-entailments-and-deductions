From Ksat Require Import defs.

Require Import List.
Import ListNotations.



Fixpoint sub_nnf (xi : nnf) : list nnf :=
  xi ::
  match xi with
  | var p        => []
  | neg p        => []
  | and phi psi  => (sub_nnf phi ++ sub_nnf psi)
  | or phi psi   => (sub_nnf phi ++ sub_nnf psi)
  | box phi      => sub_nnf phi
  | dia phi      => sub_nnf phi
  end.

Theorem mem_sub_nnf_self : forall phi : nnf, In phi (sub_nnf phi).
Proof.
  induction phi; simpl; left; reflexivity.
Qed.

Theorem mem_sub_nnf_and {phi psi : nnf} : forall xi : nnf,
  In (and phi psi) (sub_nnf xi) -> In phi (sub_nnf xi) /\ In psi (sub_nnf xi).
Proof.
induction xi as [ | | | |xi'|xi']; intro H; simpl in H.
- elim H; [discriminate | contradiction].
- elim H; [discriminate | contradiction].
- elim H.
  + intro H0. rewrite H0. simpl. split.
    * right. apply in_or_app. left. apply mem_sub_nnf_self.
    * right. apply in_or_app. right. apply mem_sub_nnf_self.
  + intro H0. apply in_app_or in H0. elim H0.
    * intro H1. apply IHxi1 in H1. simpl. split;
      (right; apply in_or_app; left; apply H1).
    * intro H1. apply IHxi2 in H1. simpl. split;
      (right; apply in_or_app; right; apply H1).
- elim H.
  + discriminate.
  + intro H0. apply in_app_or in H0. elim H0.
      * intro H1. apply IHxi1 in H1. simpl. split;
        (right; apply in_or_app; left; apply H1).
      * intro H1. apply IHxi2 in H1. simpl. split;
        (right; apply in_or_app; right; apply H1).
- elim H.
  + discriminate.
  + intro H0. apply IHxi' in H0. simpl. split; right; apply H0.
- elim H.
  + discriminate.
  + intro H0. apply IHxi' in H0. simpl. split; right; apply H0.
Qed.

Theorem mem_sub_nnf_or {phi psi : nnf} : forall xi : nnf,
  In (or phi psi) (sub_nnf xi) -> In phi (sub_nnf xi) /\ In psi (sub_nnf xi).
Proof.
induction xi as [ | | | |xi'|xi']; intro H; simpl in H.
- elim H; [discriminate | contradiction].
- elim H; [discriminate | contradiction].
- elim H.
  + discriminate.
  + intro H0. apply in_app_or in H0. elim H0.
      * intro H1. apply IHxi1 in H1. simpl. split;
        (right; apply in_or_app; left; apply H1).
      * intro H1. apply IHxi2 in H1. simpl. split;
        (right; apply in_or_app; right; apply H1).
- elim H.
  + intro H0. rewrite H0. simpl. split.
    * right. apply in_or_app. left. apply mem_sub_nnf_self.
    * right. apply in_or_app. right. apply mem_sub_nnf_self.
  + intro H0. apply in_app_or in H0. elim H0.
    * intro H1. apply IHxi1 in H1. simpl. split;
      (right; apply in_or_app; left; apply H1).
    * intro H1. apply IHxi2 in H1. simpl. split;
      (right; apply in_or_app; right; apply H1).
- elim H.
  + discriminate.
  + intro H0. apply IHxi' in H0. simpl. split; right; apply H0.
- elim H.
  + discriminate.
  + intro H0. apply IHxi' in H0. simpl. split; right; apply H0.
Qed.

Theorem mem_sub_nnf_box {phi : nnf} : forall xi : nnf,
  In (box phi) (sub_nnf xi) -> In phi (sub_nnf xi).
Proof.
induction xi as [ | | | |xi'|xi']; intro H; simpl in H.
- elim H; [discriminate | contradiction].
- elim H; [discriminate | contradiction].
- elim H.
  + discriminate.
  + intro H0. apply in_app_or in H0. elim H0.
    * intro H1. apply IHxi1 in H1. simpl. right. apply in_or_app. left. apply H1.
    * intro H1. apply IHxi2 in H1. simpl. right. apply in_or_app. right. apply H1.
- elim H.
  + discriminate.
  + intro H0. apply in_app_or in H0. elim H0.
    * intro H1. apply IHxi1 in H1. simpl. right. apply in_or_app. left. apply H1.
    * intro H1. apply IHxi2 in H1. simpl. right. apply in_or_app. right. apply H1.
- elim H.
  + intro H0. simpl. right. injection H0. intro H1. rewrite H1. apply mem_sub_nnf_self.
  + intro H0. simpl. right. apply IHxi' in H0. assumption.
- elim H.
  + discriminate.
  + intro H0. simpl. right. apply IHxi' in H0. assumption.
Qed.

Theorem mem_sub_nnf_dia {phi : nnf} : forall xi : nnf,
  In (dia phi) (sub_nnf xi) -> In phi (sub_nnf xi).
Proof.
induction xi as [ | | | |xi'|xi']; intro H; simpl in H.
- elim H; [discriminate | contradiction].
- elim H; [discriminate | contradiction].
- elim H.
  + discriminate.
  + intro H0. apply in_app_or in H0. elim H0.
    * intro H1. apply IHxi1 in H1. simpl. right. apply in_or_app. left. apply H1.
    * intro H1. apply IHxi2 in H1. simpl. right. apply in_or_app. right. apply H1.
- elim H.
  + discriminate.
  + intro H0. apply in_app_or in H0. elim H0.
    * intro H1. apply IHxi1 in H1. simpl. right. apply in_or_app. left. apply H1.
    * intro H1. apply IHxi2 in H1. simpl. right. apply in_or_app. right. apply H1.
- elim H.
  + discriminate.
  + intro H0. simpl. right. apply IHxi' in H0. assumption.
- elim H.
  + intro H0. simpl. right. injection H0. intro H1. rewrite H1. apply mem_sub_nnf_self.
  + intro H0. simpl. right. apply IHxi' in H0. assumption.
Qed.


(* Closure *)

Fixpoint closure (G : list nnf) : list nnf :=
  match G with
  | []         => []
  | phi :: Gtl => sub_nnf phi ++ closure Gtl
  end.

Theorem mem_closure_self : forall (G : list nnf), incl G (closure G).
Proof.
induction G as [|hd tl].
- apply incl_nil_l.
- simpl. unfold incl. intros a H. simpl in H. apply in_or_app. elim H.
  + intro H0. left. rewrite H0. apply mem_sub_nnf_self.
  + intro H0. unfold incl in IHtl. apply IHtl in H0. right. assumption.
Qed.

Theorem mem_closure_and {phi psi : nnf} : forall G : list nnf,
  In (and phi psi) (closure G) -> In phi (closure G) /\ In psi (closure G).
Proof.
induction G as [|hd tl].
- simpl. tauto.
- simpl. intro H. apply in_app_or in H. split; apply in_or_app; elim H;
  ((intro H0; left; apply mem_sub_nnf_and in H0; apply H0)
  || (intro H0; right; apply IHtl in H0; apply H0)).
Qed.

Theorem mem_closure_or {phi psi : nnf} : forall G : list nnf,
  In (or phi psi) (closure G) -> In phi (closure G) /\ In psi (closure G).
Proof.
induction G as [|hd tl].
- simpl. tauto.
- simpl. intro H. apply in_app_or in H. split; apply in_or_app; elim H;
  ((intro H0; left; apply mem_sub_nnf_or in H0; apply H0)
  || (intro H0; right; apply IHtl in H0; apply H0)).
Qed.

Theorem mem_closure_box {phi : nnf} : forall G : list nnf,
  In (box phi) (closure G) -> In phi (closure G).
Proof.
induction G as [|hd tl].
- simpl. tauto.
- simpl. intro H. apply in_app_or in H. apply in_or_app; elim H;
  ((intro H0; left; apply mem_sub_nnf_box in H0; apply H0)
  || (intro H0; right; apply IHtl in H0; apply H0)).
Qed.

Theorem mem_closure_dia {phi : nnf} : forall G : list nnf,
  In (dia phi) (closure G) -> In phi (closure G).
Proof.
induction G as [|hd tl].
- simpl. tauto.
- simpl. intro H. apply in_app_or in H. apply in_or_app; elim H;
  ((intro H0; left; apply mem_sub_nnf_dia in H0; apply H0)
  || (intro H0; right; apply IHtl in H0; apply H0)).
Qed.



Fixpoint filter_undia (l1 l2 : list nnf) : list nnf :=
  match l2 with
  | [] => []
  | dia phi :: tl =>
      if (in_dec nnf_eqdec phi l1)
      then filter_undia l1 tl
      else phi :: filter_undia l1 tl
  | _ :: tl => filter_undia l1 tl
  end.

Theorem mem_filter_undia_left : forall {l} {G} {phi}
  (h1 : In (dia phi) G) (h2 : ~In phi l), In phi (filter_undia l G).
Proof.
intro l. induction G as [|hd tl].
- contradiction.
- intros phi H H0. simpl in H. elim H.
  + intro H1. rewrite H1. simpl. destruct (in_dec nnf_eqdec phi l).
    * contradiction.
    * simpl. left. reflexivity.
  + intro H1. pose proof (IHtl phi H1 H0) as H2. destruct hd as [ | | | |hd'|hd'];
    simpl; try assumption. destruct (in_dec nnf_eqdec hd' l).
    * assumption.
    * simpl. right. assumption.
Qed.


Theorem mem_filter_dia_right_aux : forall {l G} {phi},
  In phi (filter_undia l G) -> In (dia phi) G.
Proof.
intro l. induction G as [|hd tl].
- trivial.
- destruct hd as [ | | | |hd'|hd'];
  try (intros phi H; simpl in H; apply IHtl in H; right; assumption).
  intro phi. simpl. destruct (in_dec nnf_eqdec hd' l).
  + intro H. right. exact (IHtl phi H).
  + simpl. intro H. elim H.
    * intro H0. left. rewrite H0. reflexivity.
    * intro H0. right. exact (IHtl phi H0).
Qed.


Theorem mem_filter_dia_right : forall {l G} {phi}, In phi (filter_undia l G) -> ~In phi l.
Proof.
intro l. induction G as [|hd tl].
- simpl. contradiction.
- destruct hd as [ | | | |hd'|hd']; try (simpl; assumption).
  simpl. destruct (in_dec nnf_eqdec hd' l) as [Heq|Hneq].
  + assumption.
  + simpl. intros phi H. elim H.
    * intro H0. rewrite <- H0. assumption.
    * apply IHtl.
Qed.
