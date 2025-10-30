From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import size.

From S4sat Require Import closure.
From S4sat Require Import data.

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Wellfounded.
Require Import Psatz.
Require Import Program.


Definition lexnat3 : nat * nat * nat -> nat * nat * nat -> Prop :=
  slexprod _ _ (slexprod _ _ lt lt) lt.

Theorem lexnat3_wf {alpha} (f : alpha -> nat * nat * nat) :
  well_founded (MR lexnat3 f).
Proof.
unfold lexnat3. unfold MR.
apply wf_inverse_image. apply wf_slexprod.
- apply wf_slexprod; apply lt_wf.
- apply lt_wf.
Qed.

Definition seqt_size (s : seqt) : nat * nat * nat :=
  (length (closure (s_R s)) - length (s_S s),
   length (closure (s_R s)) - length (s_H s),
   node_size (s_G s)).

Theorem size_remove_add_le_size_sum {phi G} :
  In phi G -> node_size (remove_nnf phi G) + sizeof phi <= node_size G.
Proof.
induction G as [|psi G'].
- simpl. contradiction.
- intro H. simpl in H. destruct H as [H|H].
  + rewrite H. simpl. destruct (nnf_eqdec phi phi); try contradiction.
    rewrite Nat.add_comm. apply add_le_mono_l_proj_l2r.
    apply node_size_mono.
  + simpl. destruct (nnf_eqdec phi psi) as [Heq|Hneq].
    * rewrite Heq. rewrite Nat.add_comm.
      apply add_le_mono_l_proj_l2r. apply node_size_mono.
    * simpl. rewrite <- (Nat.add_assoc). apply add_le_mono_l_proj_l2r.
      apply IHG'. assumption.
Qed.

Theorem unmodal_seqt_size (sse : sseqt) :
  forall i, In i (unmodal_seqt (`sse)) ->
  MR lexnat3 seqt_size i (`sse).
Proof.
intros i Hi. unfold unmodal_seqt in Hi.
pose proof Hi as Hex.
apply (in_map_iff _ _ i) in Hex.
destruct Hex as [phi [Heqi Hphi]].
apply eq_sym in Heqi.
pose proof (unmodal_pseqt sse i Hi) as pi.
unfold MR. constructor 1.
rewrite Heqi. unfold dia_child. simpl.
constructor 2.
pose proof (nodup_H pi) as H.
pose proof (H_incl_R pi) as H0.
pose proof (NoDup_incl_length H H0) as H1.
rewrite map_length in H1.
rewrite Heqi in H1. unfold dia_child in H1. simpl in H1.
lia.
Qed.

Theorem split_lt_and_seqt [phi psi s]
  (Hin : In (and phi psi) (s_G s)) :
  MR lexnat3 seqt_size (and_child phi psi s) s.
Proof.
constructor 2. simpl.
pose proof (size_remove_add_le_size_sum Hin) as H.
simpl in H. lia.
Qed.

Theorem split_lt_or_seqt_left [phi psi s]
  (Hin : In (or phi psi) (s_G s)) :
  MR lexnat3 seqt_size (or_child_left phi psi s) s.
Proof.
constructor 2. simpl.
pose proof (size_remove_add_le_size_sum Hin) as H.
simpl in H. lia.
Qed.

Theorem split_lt_or_seqt_right [phi psi s]
  (Hin : In (or phi psi) (s_G s)) :
  MR lexnat3 seqt_size (or_child_right phi psi s) s.
Proof.
constructor 2. simpl.
pose proof (size_remove_add_le_size_sum Hin) as H.
simpl in H. lia.
Qed.

Theorem split_lt_box_seqt_dup [phi s]
  (Hin1: In (box phi) (s_G s)) (Hin2: In (box phi) (s_S s)) :
  MR lexnat3 seqt_size (box_child_dup phi s) s.
Proof.
constructor 2. simpl.
pose proof (size_remove_add_le_size_sum Hin1) as H.
simpl in H. lia.
Qed.

Theorem split_lt_box_seqt_new [phi] [sse : sseqt]
  (Hin1: In (box phi) (s_G (`sse))) (Hin2: ~ In (box phi) (s_S (`sse))) :
  MR lexnat3 seqt_size (box_child_new phi (`sse)) (`sse).
Proof.
constructor 1. simpl. constructor 1.
pose proof (box_child_new_pseqt Hin1 Hin2) as pboxse.
remember (box_child_new phi (`sse)) as boxse.
pose proof (nodup_S pboxse) as H.
pose proof (S_incl_R pboxse) as H0.
pose proof (NoDup_incl_length H H0) as H1.
rewrite Heqboxse in H1. simpl in H1. lia.
Qed.
