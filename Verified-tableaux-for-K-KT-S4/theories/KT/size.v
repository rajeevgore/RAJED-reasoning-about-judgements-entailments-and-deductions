From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import size.

From KTsat Require Import defs.

Require Import Arith.
Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Wellfounded.
Require Import Psatz.
Require Import Program.



Definition measure_lex {alpha : Type} : (alpha -> nat * nat) -> alpha -> alpha -> Prop :=
  MR (slexprod _ _ lt lt).

Theorem measure_lex_wf {alpha : Type} (f : alpha -> nat * nat) :
  well_founded (measure_lex f).
Proof.
unfold measure_lex. unfold MR.
apply wf_inverse_image. apply wf_slexprod; apply lt_wf.
Qed.



Fixpoint count_modal (xi : nnf) : nat :=
match xi with
| var n        => O
| neg n        => O
| and phi psi  => count_modal phi + count_modal psi
| or phi psi   => count_modal phi + count_modal psi
| box phi      => S (count_modal phi)
| dia phi      => S (count_modal phi)
end.

Definition modal_degree (G : list nnf) : nat := list_max (map count_modal G).

Theorem modal_degree_eq : forall {G}, list_max (map count_modal G) = modal_degree G.
Proof. unfold modal_degree. reflexivity. Qed.

Theorem cons_degree (phi : nnf) (G : list nnf) :
  modal_degree (phi :: G) = max (count_modal phi) (modal_degree G).
Proof.
unfold modal_degree. simpl. reflexivity.
Qed.

Theorem app_degree (G1 G2 : list nnf) :
  modal_degree (G1 ++ G2) = max (modal_degree G1) (modal_degree G2).
Proof.
unfold modal_degree. rewrite map_app.
rewrite list_max_app. reflexivity.
Qed.

Theorem le_of_mem_degree : forall (phi : nnf) (G : list nnf), In phi G ->
  count_modal phi <= modal_degree G.
Proof.
intros phi G H. induction G; try contradiction.
rewrite cons_degree. destruct H as [Hl|Hr].
- rewrite Hl. apply Nat.le_max_l.
- eapply Nat.le_trans.
  * apply IHG. assumption.
  * apply Nat.le_max_r.
Qed.

Lemma in_le_list_max : forall {x} {l}, In x l -> x <= list_max l.
Proof.
induction l.
- simpl. tauto.
- intro H. destruct H as [Hl|Hr].
  * rewrite <- Hl. simpl. apply Nat.le_max_l.
  * simpl. eapply Nat.le_trans.
    + apply IHl. assumption.
    + apply Nat.le_max_r.
Qed.

Lemma incl_le_list_max : forall {l1 l2 : list nat}, incl l1 l2 ->
  list_max l1 <= list_max l2.
Proof.
induction l1.
- simpl. auto with arith.
- intros l2 H. simpl. apply Nat.max_lub.
  * apply in_le_list_max. apply H. left. reflexivity.
  * apply IHl1. eapply incl_tran.
    2:{ apply H. }
    apply incl_tl, incl_refl.
Qed.

Lemma in_cons_degree_eq :
  forall phi G, In phi G -> modal_degree (phi :: G) = modal_degree G.
Proof.
induction G as [|psi G].
- simpl. tauto.
- intro H. destruct H as [H|H].
  * rewrite H. repeat rewrite cons_degree.
    rewrite Nat.max_assoc, Nat.max_id. reflexivity.
  * repeat rewrite cons_degree. rewrite Nat.max_assoc.
    rewrite (Nat.max_comm (count_modal phi) (count_modal psi)).
    rewrite <- Nat.max_assoc. rewrite <- cons_degree.
    rewrite IHG; try assumption. reflexivity.
Qed.
  
Theorem cons_remove_degree (phi : nnf) (G : list nnf) : In phi G ->
  modal_degree (phi :: remove_nnf phi G) = modal_degree G.
Proof.
induction G as [|psi G].
- simpl. tauto.
- intro H. simpl. destruct (nnf_eqdec phi psi) as [Heq|Hneq].
  * rewrite <- Heq.
    destruct (in_dec nnf_eqdec phi G) as [Hin|Hnin].
    + rewrite IHG; try assumption. apply eq_sym.
      apply in_cons_degree_eq. assumption.
    + unfold remove_nnf. rewrite (notin_remove _ _ _ Hnin). reflexivity.
  * destruct H; try (apply eq_sym in H; contradiction).
    repeat (rewrite cons_degree).
    rewrite Nat.max_assoc. rewrite Nat.max_comm with (n:=(count_modal phi)).
    rewrite <- Nat.max_assoc. rewrite <- cons_degree.
    rewrite IHG; try assumption. reflexivity.
Qed.

Theorem le_degree_of_subset : forall {l1 l2 : list nnf}, incl l1 l2 ->
  modal_degree l1 <= modal_degree l2.
Proof.
unfold modal_degree. intros l1 l2 H. apply incl_le_list_max.
apply incl_map. assumption.
Qed.

Definition seqt_size (s : seqt) : nat * nat :=
  (modal_degree (s.(main) ++ s.(hdld)), node_size s.(main)).

(* Lemma size_remove_add_eq_size_sum {phi} : forall G : list nnf,
  In phi G -> node_size (remove_nnf phi G) + sizeof phi = node_size G.
Proof.
induction G as [|psi G'].
- simpl. contradiction.
- intro H. simpl in H. elim H.
  * intro H0. rewrite H0. simpl. destruct (nnf_eqdec phi phi); try contradiction.
    apply Nat.add_comm.
  * intro H0. simpl. destruct (nnf_eqdec psi phi) as [heq|hneq].
    + rewrite heq. apply Nat.add_comm.
    + simpl. apply IHG' in H0. rewrite <- H0. rewrite Nat.add_assoc. reflexivity.
Qed. *)

Theorem split_lt_and_size {phi psi} (G : list nnf) : In (and phi psi) G ->
  node_size (phi :: psi :: remove_nnf (and phi psi) G) < node_size G.
Proof.
intro H. simpl. pose proof (@size_remove_add_eq_size_sum (and phi psi) G H) as H0.
simpl sizeof in H0. rewrite Nat.add_succ_r in H0.
rewrite Nat.add_assoc. rewrite Nat.add_comm. unfold lt. rewrite H0. apply le_n.
Qed.

Theorem split_le_and_degree {phi psi} (G : list nnf) : In (and phi psi) G ->
  modal_degree (phi :: psi :: remove_nnf (and phi psi) G) <= modal_degree G.
Proof.
intro H. repeat (rewrite cons_degree). rewrite Nat.max_assoc.
apply Nat.max_lub.
- eapply Nat.le_trans.
  2:{ apply in_le_list_max. apply in_map. apply H. }
  apply Nat.max_lub; simpl; [apply Nat.le_add_r|apply Nat.le_add_l].
- apply incl_le_list_max. apply incl_map. apply remove_subset.
Qed.

Theorem split_lt_and_seqt {phi psi} (G : seqt) (h : In (and phi psi) G.(main)) :
  measure_lex seqt_size (and_child G h) G.
Proof.
unfold measure_lex. unfold MR. unfold and_child. unfold seqt_size. simpl.
assert (modal_degree (phi :: psi :: remove_nnf (and phi psi) (main G) ++ hdld G)
  <= modal_degree (main G ++ hdld G)) as Hmle.
- repeat (rewrite app_comm_cons). repeat (rewrite app_degree).
  apply Nat.max_le_compat_r. apply split_le_and_degree. assumption.
- pose proof (le_lt_eq_dec _ _ Hmle) as Hmltoreq.
  destruct Hmltoreq as [Hmlt|Hmeq].
  * apply left_slex. assumption.
  * rewrite Hmeq. apply right_slex. repeat (rewrite node_size_cons).
    apply split_lt_and_size. assumption.
Qed.

Theorem split_lt_or_size_left {phi psi} (G : list nnf) : In (or phi psi) G ->
  node_size (phi :: remove_nnf (or phi psi) G) < node_size G.
Proof.
intro H. simpl. pose proof (@size_remove_add_eq_size_sum (or phi psi) G H) as H0.
simpl sizeof in H0. lia.
Qed.

Theorem split_lt_or_size_right {phi psi} (G : list nnf) : In (or phi psi) G ->
  node_size (psi :: remove_nnf (or phi psi) G) < node_size G.
Proof.
intro H. simpl. pose proof (@size_remove_add_eq_size_sum (or phi psi) G H) as H0.
simpl sizeof in H0. lia.
Qed.

Theorem split_le_or_degree_left {phi psi} (G : list nnf) : In (or phi psi) G ->
  modal_degree (phi :: remove_nnf (or phi psi) G) <= modal_degree G.
Proof.
intro H. rewrite cons_degree. apply Nat.max_lub.
- eapply Nat.le_trans.
  2:{ apply in_le_list_max. apply in_map. apply H. }
  simpl. apply Nat.le_add_r.
- apply incl_le_list_max. apply incl_map. apply remove_subset.
Qed.

Theorem split_le_or_degree_right {phi psi} (G : list nnf) : In (or phi psi) G ->
  modal_degree (psi :: remove_nnf (or phi psi) G) <= modal_degree G.
Proof.
intro H. rewrite cons_degree. apply Nat.max_lub.
- eapply Nat.le_trans.
  2:{ apply in_le_list_max. apply in_map. apply H. }
  simpl. apply Nat.le_add_l.
- apply incl_le_list_max. apply incl_map. apply remove_subset.
Qed.

Theorem split_lt_or_seqt_left {phi psi} (G : seqt) (h : In (or phi psi) (main G)) :
  measure_lex seqt_size (or_child_left G h) G.
Proof.
unfold measure_lex. unfold MR. unfold seqt_size. simpl.
assert (modal_degree (phi :: remove_nnf (or phi psi) (main G) ++ hdld G)
  <= modal_degree (main G ++ hdld G)) as Hmle.
- rewrite app_comm_cons. repeat (rewrite app_degree).
  apply Nat.max_le_compat_r. apply split_le_or_degree_left. assumption.
- pose proof (le_lt_eq_dec _ _ Hmle) as Hmltoreq.
  destruct Hmltoreq as [Hmlt|Hmeq].
  * apply left_slex. assumption.
  * rewrite Hmeq. apply right_slex. rewrite node_size_cons.
    apply split_lt_or_size_left. assumption.
Qed.

Theorem split_lt_or_seqt_right {phi psi} (G : seqt) (h : In (or phi psi) (main G)) :
  measure_lex seqt_size (or_child_right G h) G.
Proof.
unfold measure_lex. unfold MR. unfold seqt_size. simpl.
assert (modal_degree (psi :: remove_nnf (or phi psi) (main G) ++ hdld G)
  <= modal_degree (main G ++ hdld G)) as Hmle.
- rewrite app_comm_cons. repeat (rewrite app_degree).
  apply Nat.max_le_compat_r. apply split_le_or_degree_right. assumption.
- pose proof (le_lt_eq_dec _ _ Hmle) as Hmltoreq.
  destruct Hmltoreq as [Hmlt|Hmeq].
  * apply left_slex. assumption.
  * rewrite Hmeq. apply right_slex. rewrite node_size_cons.
    apply split_lt_or_size_right. assumption.
Qed.

Theorem copy_lt_size {phi} (G : list nnf) : In (box phi) G ->
  node_size (phi :: remove_nnf (box phi) G) < node_size G.
Proof.
intro H. simpl. eapply Nat.lt_le_trans;
try apply (@size_remove_add_eq_size_sum (box phi) G H).
simpl. lia.
Qed.

Theorem copy_eq_degree {phi} (G L: list nnf) : In (box phi) G ->
  modal_degree ((phi :: remove_nnf (box phi) G) ++ (box phi :: L)) = modal_degree (G ++ L).
Proof.
intro H. rewrite <- app_comm_cons. rewrite cons_degree.
rewrite Nat.max_r.
- repeat (rewrite app_degree). rewrite cons_degree.
  rewrite Nat.max_assoc.
  rewrite Nat.max_comm with (n:=modal_degree (remove_nnf (box phi) G)).
  rewrite <- cons_degree. rewrite cons_remove_degree by assumption.
  reflexivity.
- rewrite app_degree. eapply Nat.le_trans.
  2:{ apply Nat.le_max_r. }
  rewrite cons_degree. eapply Nat.le_trans.
  2:{ apply Nat.le_max_l. }
  simpl. apply le_S. apply le_n.
Qed.

Theorem copy_lt_seqt {phi} (G : seqt) (h : In (box phi) (main G)) :
  measure_lex seqt_size (box_child G h) G.
Proof. 
unfold measure_lex. unfold MR. unfold seqt_size. simpl. rewrite app_comm_cons.
rewrite copy_eq_degree by assumption. apply right_slex.
rewrite node_size_cons. apply copy_lt_size. assumption.
Qed.
