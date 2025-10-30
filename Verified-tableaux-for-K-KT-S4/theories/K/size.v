From Ksat Require Import defs.
From Ksat Require Import ops.

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Psatz.


(* Do not use map *)
Fixpoint sizeof (xi:nnf) : nat :=
  match xi with
  | var n       => 0
  | neg n       => 0
  | and phi psi => S ((sizeof phi) + (sizeof psi))
  | or phi psi  => S ((sizeof phi) + (sizeof psi))
  | box phi     => S (sizeof phi)
  | dia phi     => S (sizeof phi)
  end.

Fixpoint node_size (G : list nnf) : nat :=
  match G with
  | []          => 0
  | (phi :: Gtl)  => sizeof phi + node_size Gtl
  end.

Theorem node_size_cons (G : list nnf) (phi : nnf) :
  sizeof phi + node_size G = node_size (phi :: G).
Proof. simpl. reflexivity. Qed.

Lemma node_size_mono : forall phi G,
  node_size (remove_nnf phi G) <= node_size G.
Proof.
intros phi G. induction G as [|psi].
- simpl. apply le_n.
- simpl. destruct (nnf_eqdec phi psi); simpl; lia.
Qed.


Lemma size_remove_add_eq_size_sum {phi} : forall G : list nnf,
  In phi G -> node_size (remove_nnf phi G) + sizeof phi <= node_size G.
Proof.
induction G as [|psi G'].
- simpl. contradiction.
- intro H. simpl in H. destruct H as [H|H].
  * rewrite H. simpl. destruct (nnf_eqdec phi phi); try contradiction.
    rewrite Nat.add_comm. apply add_le_mono_l_proj_l2r.
    apply node_size_mono.
  * simpl. destruct (nnf_eqdec phi psi) as [Heq|Hneq].
    + rewrite <- Heq. specialize (IHG' H). lia.
    + simpl. rewrite <- Nat.add_assoc. apply add_le_mono_l_proj_l2r.
      apply IHG'. assumption.
Qed.

Theorem split_lt_and {phi psi} (G : list nnf) : In (and phi psi) G ->
  node_size (phi :: psi :: remove_nnf (and phi psi) G) < node_size G.
Proof.
intro H. simpl.
pose proof (@size_remove_add_eq_size_sum (and phi psi) G H) as H0.
simpl sizeof in H0. rewrite Nat.add_succ_r in H0.
rewrite Nat.add_assoc. rewrite Nat.add_comm. unfold lt.
rewrite H0. apply le_n.
Qed.

Theorem split_lt_or_left {phi psi} (G : list nnf) : In (or phi psi) G ->
  node_size (phi :: remove_nnf (or phi psi) G) < node_size G.
Proof.
intro H. simpl.
pose proof (@size_remove_add_eq_size_sum (or phi psi) G H) as H0.
simpl sizeof in H0. lia.
Qed.

Theorem split_lt_or_right {phi psi} (G : list nnf) : In (or phi psi) G ->
  node_size (psi :: remove_nnf (or phi psi) G) < node_size G.
Proof.
intro H. simpl.
pose proof (@size_remove_add_eq_size_sum (or phi psi) G H) as H0.
simpl sizeof in H0. lia.
Qed.


Theorem unbox_size_aux : forall {G}, node_size (unbox G) <= node_size G.
Proof.
induction G as [|phi G'].
- simpl. apply le_n.
- destruct phi; simpl; lia.
Qed.

Theorem unbox_size : forall {G phi}, In (dia phi) G ->
                     node_size (unbox G) + sizeof phi < node_size G.
Proof.
induction G as [|psi G'].
- simpl. contradiction.
- destruct psi as [ | | | |psi'|psi'];
  try (intros phi H; simpl in H; elim H;
    (discriminate || intro H0; simpl; pose proof (IHG' phi H0) as H1; lia)).
  intros phi H. simpl in H. elim H.
  * intro Hl. injection Hl. intro H0. rewrite H0. simpl.
    pose proof (@unbox_size_aux G') as H1. lia.
  * intro Hr. simpl. pose proof (IHG' phi Hr) as H0. lia.
Qed.

Theorem undia_size : forall {G phi}, In phi (undia G) ->
                     sizeof phi + node_size (unbox G) < node_size G.
Proof.
intros G phi H. rewrite Nat.add_comm. apply unbox_size. rewrite undia_iff. assumption.
Qed.