Require Import utils.
Require Import nnf.
Require Import closure.
Require Import seqt.

Require Import Arith.
Require Import List.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Wellfounded.
Require Import Lia.
Require Import Program.



Definition lexnat2 : nat * nat  -> nat * nat -> Prop :=
  slexprod _ _ lt lt.

Theorem lexnat2_wf [alpha] (f : alpha -> nat * nat) :
  well_founded (MR lexnat2 f).
Proof.
unfold lexnat2. unfold MR.
apply wf_inverse_image. apply wf_slexprod; apply lt_wf.
Qed.

Fixpoint red_size (xi : nnf) : nat :=
  match xi with
  | var n       => 1
  | neg n       => 1
  | and phi psi => 1 + red_size phi + red_size psi
  | or phi psi  => 1 + red_size phi + red_size psi
  | bef phi psi => 2 + red_size phi + red_size psi
  | unt phi psi => 2 + red_size phi + red_size psi
  | next phi    => 0
  end.

Lemma red_size_neg_eq {phi} : red_size (neg_nnf phi) = red_size phi.
Proof. induction phi; try (simpl; lia). Qed.

Lemma red_size_alpha1_lt {phi} :
  nnf_isalpha phi -> red_size (nnf_alpha1 phi) < red_size phi.
Proof.
intro H. destruct phi; try contradiction; simpl; try lia.
rewrite red_size_neg_eq. lia.
Qed.

Lemma red_size_alpha2_lt {phi} :
  nnf_isalpha phi -> red_size (nnf_alpha2 phi) < red_size phi.
Proof.
intro H. destruct phi; try contradiction; simpl; try lia.
Qed.

Lemma red_size_beta1_lt {phi} :
  nnf_isbeta phi -> red_size (nnf_beta1 phi) < red_size phi.
Proof.
intro H. destruct phi; try contradiction; simpl; try lia.
Qed.

Lemma red_size_beta2_lt {phi} :
  nnf_isbeta phi -> red_size (nnf_beta2 phi) < red_size phi.
Proof.
intro H. destruct phi; try contradiction; simpl; try lia.
Qed.

Definition red_size_list := fold_right (fun phi n => red_size phi + n) 0.

Lemma red_size_list_mono : forall phi G,
  red_size_list (remove_nnf phi G) <= red_size_list G.
Proof.
intros phi G. induction G as [|psi].
- simpl. apply le_n.
- simpl. destruct (nnf_eqdec phi psi); simpl; lia.
Qed.

Definition seqt_size (s : doseqt) : nat * nat :=
  (length (power_set (cl_list (s_R s))) - length (s_H s),
   red_size_list (s_G s)).


Lemma size_remove_add_le_size_sum [phi G] : In phi G ->
red_size_list (remove_nnf phi G) + red_size phi <= red_size_list G.
Proof.
induction G as [|psi G'].
- simpl. contradiction.
- intro H. simpl in H. destruct H as [H|H].
  + rewrite H. simpl. destruct (nnf_eqdec phi phi); try contradiction.
    rewrite Nat.add_comm. apply add_le_mono_l_proj_l2r.
    apply red_size_list_mono.
  + simpl. destruct (nnf_eqdec phi psi) as [Heq|Hneq].
    * rewrite Heq. rewrite Nat.add_comm.
      apply add_le_mono_l_proj_l2r. apply red_size_list_mono.
    * simpl. rewrite <- (Nat.add_assoc). apply add_le_mono_l_proj_l2r.
      apply IHG'. assumption.
Qed.

Theorem alpha_child_decr_size [phi s] :
  nnf_isalpha phi -> In phi (s_G s) -> MR lexnat2 seqt_size (alpha_child phi s) s.
Proof.
intros Hphi Hin. simpl in Hin. constructor 2.
pose proof (size_remove_add_le_size_sum Hin) as H.
destruct phi; try contradiction.
- simpl. simpl in H. lia.
- simpl. simpl in H. rewrite (red_size_neg_eq). lia.
Qed.

Theorem beta1_child_decr_size [phi s] :
  nnf_isbeta phi -> In phi (s_G s) -> MR lexnat2 seqt_size (beta1_child phi s) s.
Proof.
intros Hphi Hin. simpl in Hin. constructor 2. 
pose proof (size_remove_add_le_size_sum Hin) as H.
destruct phi; try contradiction.
- simpl. simpl in H. lia.
- simpl. simpl in H. lia.
Qed.

Theorem beta2_child_decr_size [phi s] :
  nnf_isbeta phi -> In phi (s_G s) -> MR lexnat2 seqt_size (beta2_child phi s) s.
Proof.
intros Hphi Hin. simpl in Hin. constructor 2. 
pose proof (size_remove_add_le_size_sum Hin) as H.
destruct phi; try contradiction.
- simpl. simpl in H. lia.
- simpl. simpl in H. lia.
Qed.

Theorem jump_child_decr_size {ss : rdoseqt} (sc : state_conditions (`ss))
  (nb : not_blocked_seqt (`ss)) :
  MR lexnat2 seqt_size (jump_child (`ss)) (`ss).
Proof.
constructor 1. simpl.
pose proof (jump_child_pseqt ss sc nb) as psec.
set (sec := jump_child (`ss)).
pose proof (nodup_H psec) as ND.
assert (length (map snd (s_H sec)) <=
length (power_set (cl_list (s_R sec)))) as Hle.
{ apply (NoDupA_set_incl_length nnf_eqdec ND).
intros l Hl. rewrite InA_alt in Hl.
destruct Hl as [sndh [Heqs Hin]].
apply eqset_sym in Heqs.
apply (InA_eqA (eqset_equivalence nnf) Heqs).
apply (incl_inset_power_set nnf_eqdec).
apply (H_incl_R psec). assumption. }
simpl in Hle. rewrite map_length in Hle.
lia.
Qed.
