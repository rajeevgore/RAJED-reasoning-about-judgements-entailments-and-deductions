From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import semantics.

From S4sat Require Import closure.
From S4sat Require Import data.
From S4sat Require Import defs.
From S4sat Require Import ops.

Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Program.


Set Implicit Arguments.

Definition satable_S4_seqt (s : seqt) := satable_S4 (s_G s ++ s_S s).

Definition unsatable_S4_seqt (s : seqt) := unsatable_S4 (s_G s ++ s_S s).

Section PropositionalPart.

  Variables phi psi : nnf.

  Theorem unsat_contra_seqt {D : seqt} {n} :
    In (var n) (s_G D) -> In (neg n) (s_G D) ->
    unsatable_S4 ((s_G D) ++ (s_S D)).
  Proof.
  intros H H0 M w Hsat.
  apply (@unsat_contra (s_G D) n H H0 M w).
  apply (append_sat_l Hsat).
  Qed.

  Theorem unsat_and_of_unsat_split_seqt {G D} :
    In (and phi psi) D ->
    unsatable_S4 ((phi :: psi :: remove_nnf (and phi psi) D) ++ G) ->
    unsatable_S4 (D ++ G).
  Proof.
  intros H H0 M w Hsat.
  apply (H0 M w).
  intros xi Hxi.
  apply in_app_iff in Hxi.
  destruct Hxi as [Hxil|Hxir].
  - apply append_sat_l in Hsat.
    simpl in Hxil. destruct Hxil as [Hxil1 | [Hxil2 | Hxil3]].
    + rewrite <- Hxil1. specialize (Hsat (and phi psi) H).
      rewrite sat_of_and in Hsat. tauto.
    + rewrite <- Hxil2. specialize (Hsat (and phi psi) H).
      rewrite sat_of_and in Hsat. tauto.
    + generalize Hxil3. generalize xi.
      fold (@sat M w (remove_nnf (and phi psi) D)).
      eapply sat_subset.
      2:{ apply Hsat. }
      intro. apply in_remove.
  - apply (append_sat_r Hsat). assumption.
  Qed.

  Theorem sat_and_of_sat_split_seqt {G D} (M : S4) w :
          sat M w ((phi :: psi :: remove_nnf (and phi psi) D) ++ G) ->
          sat M w (D ++ G).
  Proof.
  intro H. intros xi Hxi. apply in_app_iff in Hxi.
  destruct Hxi as [Hxil|Hxir].
  - generalize Hxil. generalize xi.
    fold (sat M w D).
    apply sat_and_of_sat_split with phi psi.
    eapply sat_subset; [idtac|apply H].
    apply incl_appl, incl_refl.
  - generalize Hxir. generalize xi.
    fold (sat M w G).
    eapply sat_subset; [idtac|apply H].
    apply incl_appr, incl_refl.
  Qed.

  Theorem sat_split_of_sat_and_seqt {G D} (M : S4) w :
    In (and phi psi) D -> sat M w (D ++ G) ->
    sat M w ((phi :: psi :: remove_nnf (and phi psi) D) ++ G).
  Proof.
  intros H H0. apply sat_append.
  - apply append_sat_l in H0.
    + intros xi Hxi. simpl in Hxi.
      destruct Hxi as [Hxi1|[Hxi2|Hxi3]].
      * rewrite <- Hxi1. specialize (H0 (and phi psi) H).
        rewrite sat_of_and in H0. tauto.
      * rewrite <- Hxi2. specialize (H0 (and phi psi) H).
        rewrite sat_of_and in H0. tauto.
      * generalize Hxi3. generalize xi.
        fold (@sat M w (remove_nnf (and phi psi) D)).
        eapply sat_subset.
        2:{ apply H0. }
        intro. apply in_remove.
  - apply (append_sat_r H0).
  Qed.

  Theorem unsat_or_of_unsat_split_seqt {G D} :
    In (or phi psi) D ->
    unsatable_S4 (phi :: remove_nnf (or phi psi) D ++ G) ->
    unsatable_S4 (psi :: remove_nnf (or phi psi) D ++ G) ->
    unsatable_S4 (D ++ G).
  Proof.
  intros H H0 H1. intros M w Hsat.
  assert (force M w (or phi psi)) as H2.
  - apply Hsat. apply in_or_app. left. assumption.
  - destruct H2.
    + apply (H0 M w). apply sat_subset with (phi :: D ++ G).
      * intros xi Hxi. simpl in Hxi. destruct Hxi as [Hxil|Hxir].
       -- left. assumption.
       -- apply in_app_iff in Hxir.
          simpl. right. apply in_or_app.
          destruct Hxir as [Hxir1|Hxir2].
         ++ left. eapply (in_remove nnf_eqdec). apply Hxir1.
         ++ right. assumption.
      * intros xi Hxi. destruct Hxi as [Hxil|Hxir].
       -- rewrite <- Hxil. assumption.
       -- apply Hsat. assumption.
    + apply (H1 M w). apply sat_subset with (psi :: D ++ G).
      * intros xi Hxi. simpl in Hxi. destruct Hxi as [Hxil|Hxir].
       -- left. assumption.
       -- apply in_app_iff in Hxir.
          simpl. right. apply in_or_app.
          destruct Hxir as [Hxir1|Hxir2].
         ++ left. eapply (in_remove nnf_eqdec). apply Hxir1.
         ++ right. assumption.
      * intros xi Hxi. destruct Hxi as [Hxil|Hxir].
       -- rewrite <- Hxil. assumption.
       -- apply Hsat. assumption.
  Qed.

  Theorem sat_or_of_sat_split_left {D} (M : S4) w :
          sat M w (phi :: remove_nnf (or phi psi) D) ->
          sat M w D.
  Proof.
  intros H. intros xi Hxi. destruct (nnf_eqdec xi (or phi psi)) as [Heq|Hneq].
  - rewrite Heq. simpl. left. apply (H phi). simpl. tauto.
  - apply H. simpl. right.
    apply (in_in_remove nnf_eqdec _ Hneq Hxi).
  Qed.

  Theorem sat_or_of_sat_split_right {D} (M : S4) w :
          sat M w (psi :: remove_nnf (or phi psi) D) ->
          sat M w D.
  Proof.
  intros H. intros xi Hxi. destruct (nnf_eqdec xi (or phi psi)) as [Heq|Hneq].
  - rewrite Heq. simpl. right. apply (H psi). simpl. tauto.
  - apply H. simpl. right.
    apply (in_in_remove nnf_eqdec _ Hneq Hxi).
  Qed.


  (* S4 specific lemmas *)

  Theorem force_of_force_box (M : S4) w :
  force M w (box phi) -> force M w phi.
  Proof.
  intro H. apply H. apply refl_rel.
  Qed.

  Theorem force_box_box_of_force_box (M : S4) w :
  force M w (box phi) -> force M w (box (box phi)).
  Proof.
  intros H s1 Hs1 s2 Hs2. apply H. apply (trans_rel M w s1 s2 Hs1 Hs2).
  Qed.

  Theorem unsat_of_unsat_box_new {G D} :
    In (box phi) G ->
    unsatable_S4 ((phi :: remove_nnf (box phi) G) ++ box phi :: D) ->
    unsatable_S4 (G ++ D).
  Proof.
  intros Hin Hunsat. intros M w Hsat.
  pose proof (Hunsat M w) as Hcont. contradict Hcont.
  intros xi Hxi. apply in_app_iff in Hxi.
  destruct Hxi as [[Hxi|Hxi]|[Hxi|Hxi]].
  - rewrite <- Hxi. apply force_of_force_box. apply Hsat.
    apply in_app_iff. left. assumption.
  - apply Hsat. apply in_app_iff. left.
    apply (in_remove nnf_eqdec _ _ _ Hxi).
  - rewrite <- Hxi. apply Hsat. apply in_app_iff.
    left. assumption.
  - apply Hsat. apply in_app_iff. right. assumption.
  Qed.

  Theorem unsat_of_unsat_box_dup {G D} :
    In (box phi) G ->
    unsatable_S4 ((phi :: remove_nnf (box phi) G) ++ D) ->
    unsatable_S4 (G ++ D).
  Proof.
  intros Hin Hunsat. intros M w Hsat.
  pose proof (Hunsat M w) as Hcont. contradict Hcont.
  intros xi Hxi. apply in_app_iff in Hxi.
  destruct Hxi as [[Hxi|Hxi]|Hxi].
  - rewrite <- Hxi. apply force_of_force_box. apply Hsat.
    apply in_app_iff. left. assumption.
  - apply Hsat. apply in_app_iff. left.
    apply (in_remove nnf_eqdec _ _ _ Hxi).
  - apply Hsat. apply in_app_iff. right. assumption.
  Qed.

End PropositionalPart.

Unset Implicit Arguments.

Theorem unsat_of_closed_and_seqt [phi psi w]
  (Hin : In (and phi psi) (s_G w)) :
  unsatable_S4_seqt (and_child phi psi w) ->
  unsatable_S4_seqt w.
Proof.
intro H. apply (unsat_and_of_unsat_split_seqt Hin). assumption.
Qed.

Theorem unsat_of_closed_or_seqt [phi psi w]
  (Hin : In (or phi psi) (s_G w)) :
  unsatable_S4_seqt (or_child_left phi psi w) ->
  unsatable_S4_seqt (or_child_right phi psi w) ->
  unsatable_S4_seqt w.
Proof.
intros Hl Hr. apply (unsat_or_of_unsat_split_seqt Hin); assumption.
Qed.

Theorem unsat_of_closed_box_new_seqt [phi w]
  (Hin1 : In (box phi) (s_G w)) :
  unsatable_S4_seqt (box_child_new phi w) ->
  unsatable_S4_seqt w.
Proof.
apply unsat_of_unsat_box_new. assumption.
Qed.

Theorem unsat_of_closed_box_dup_seqt [phi w]
  (Hin1 : In (box phi) (s_G w)) :
  unsatable_S4_seqt (box_child_dup phi w) ->
  unsatable_S4_seqt w.
Proof.
apply unsat_of_unsat_box_dup. assumption.
Qed.

Theorem unsat_of_unsat_unmodal (ss : sseqt) : forall i : seqt,
  In i (unmodal_seqt (`ss)) /\ unsatable_S4_seqt i -> unsatable_S4_seqt (`ss).
Proof.
intros i Hi. destruct Hi as [Hi1 Hi2].
pose proof Hi1 as Hex. apply in_map_iff in Hex.
destruct Hex as [phi [Heqi Hphi]].
apply eq_sym in Heqi.
pose proof (mem_filter_dia_right_aux Hphi) as Hdia.
intros M w Hsat.
assert (force M w (dia phi)) as Hfor.
1:{
apply Hsat. eapply incl_appl; [apply incl_refl | assumption].
}
simpl in Hfor. destruct Hfor as [w' [Hrel Hfor]].
apply (Hi2 M w'). rewrite Heqi. simpl.
intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
- rewrite <- Hpsi. assumption.
- destruct ss as [s ps]. simpl in *. assert (In psi (s_S s) -> force M w' psi) as H.
  1:{
  intro Hpsi0. destruct psi; try
  (destruct (box_only_S ps _ Hpsi0); discriminate).
  assert (force M w (box (box psi))) as Hbb.
  1:{
  apply force_box_box_of_force_box.
  apply Hsat. eapply incl_appr; [apply incl_refl | assumption].
  }
  remember (box psi) as xi. apply Hbb. assumption.
  }
  apply in_app_or in Hpsi.
  destruct Hpsi as [Hpsi|Hpsi]; apply (H Hpsi).
Qed.
