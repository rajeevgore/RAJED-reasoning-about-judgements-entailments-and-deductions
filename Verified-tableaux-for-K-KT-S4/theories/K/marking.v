From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import ops.
From Ksat Require Import semantics.
From Ksat Require Import model.

Require Import List.
Require Import ListSet.
Import ListNotations.


Definition pmark (G m : list nnf) :=
  forall D, (forall d, In d D -> ~ In d m) -> sublist D G ->
  unsatable (diff_nnf G D).

Definition mark_and (phi:nnf) (m : list nnf) : list nnf :=
  match phi with
  | and phi1 phi2 =>
    if in_dec nnf_eqdec phi1 m then phi :: m
    else
      if in_dec nnf_eqdec phi2 m then phi :: m
      else m
  | _ => m
  end.

Definition mark_or (phi:nnf) (ml : list nnf) (mr : list nnf) : list nnf :=
  match phi with
  | or phi1 phi2 =>
      if in_dec nnf_eqdec phi1 ml then phi :: (ml++mr)
      else
        if in_dec nnf_eqdec phi2 mr then phi :: (ml++mr)
        else ml ++ mr
  | _ => ml ++ mr
  end.

Definition mark_modal (G i m : list nnf) : list nnf :=
  dia (hd_nnf i) :: rebox (inter_nnf (tl i) m).

Theorem box_mem_of_mark_modal {phi} (G i m : list nnf) :
  In phi m -> In phi i -> phi = hd_nnf i \/
  In (box phi) (mark_modal G i m).
Proof.
intros H H0. destruct (nnf_eqdec phi (hd_nnf i)) as [heq|hneq].
- left. assumption.
- right. simpl. right. apply rebox_iff.
  pose proof (mem_tail_of_ne_head H0 hneq) as H1.
  apply set_inter_intro; assumption.
Qed.

Theorem subset_mark_and {phi G} : incl G (mark_and phi G).
Proof.
destruct phi; simpl; try (apply incl_refl).
destruct (in_dec nnf_eqdec phi1 G). apply incl_tl, incl_refl.
destruct (in_dec nnf_eqdec phi2 G). apply incl_tl, incl_refl.
apply incl_refl.
Qed.

Theorem unsat_mark_and {phi G} :
  unsatable G -> unsatable (mark_and phi G).
Proof.
apply unsat_subset. apply subset_mark_and.
Qed.

Theorem subset_mark_or_left {phi G1 G2} : incl G1 (mark_or phi G1 G2).
Proof.
destruct phi; simpl; try (apply incl_appl, incl_refl).
destruct (in_dec nnf_eqdec phi1 G1). apply incl_tl, incl_appl, incl_refl.
destruct (in_dec nnf_eqdec phi2 G2). apply incl_tl, incl_appl, incl_refl.
apply incl_appl, incl_refl.
Qed.

Theorem subset_mark_or_right {phi G1 G2} : incl G2 (mark_or phi G1 G2).
Proof.
destruct phi; simpl; try (apply incl_appr, incl_refl).
destruct (in_dec nnf_eqdec phi1 G1). apply incl_tl, incl_appr, incl_refl.
destruct (in_dec nnf_eqdec phi2 G2). apply incl_tl, incl_appr, incl_refl.
apply incl_appr, incl_refl.
Qed.

Theorem unsat_mark_or_left {phi G1 G2} :
  unsatable G1 -> unsatable (mark_or phi G1 G2).
Proof.
apply unsat_subset, subset_mark_or_left.
Qed.

Theorem unsat_mark_or_right {phi G1 G2} :
  unsatable G2 -> unsatable (mark_or phi G1 G2).
Proof.
apply unsat_subset, subset_mark_or_right.
Qed.



(* unsatable D is actually not required *)

Definition pmark_of_closed_and {G D} (i : and_instance G D) m :
  unsatable D -> pmark D m -> {x | pmark G x}.
Proof.
intros H p. destruct i as [phi psi Hin].
remember (phi :: psi :: remove_nnf (and phi psi) G) as D.
exists (mark_and (and phi psi) m).
remember (mark_and (and phi psi) m) as x.
intros D' HD' Hsub.
assert ((x = (and phi psi) :: m) ->
unsatable (diff_nnf G D')) as Hlem.
- intro Hxand. assert (unsatable (diff_nnf D D')) as HunDD'. apply p.
  * intros d H1 H2. apply (HD' d H1). rewrite Hxand. simpl. now right.
  * apply (sublist_remove nnf_eqdec (and phi psi)) in Hsub as Hsub'.
    assert (~ In (and phi psi) D').
    intro H0. apply (HD' (and phi psi) H0).
    rewrite Hxand. simpl. now left.
    rewrite (notin_remove nnf_eqdec _ _ H0) in Hsub'.
    rewrite HeqD. repeat constructor. assumption.
  * intros k s Hsat. apply (HunDD' k s).
    eapply sat_subset. rewrite HeqD. apply subset_cons_diff.
    eapply sat_subset. apply cons_subset_cons. apply subset_cons_diff.
    assert (In (and phi psi) (diff_nnf G D')).
    + apply mem_diff_of_mem.
     -- assumption.
     -- intro H0. apply (HD' _ H0). rewrite Hxand. simpl. now left.
    + apply Hsat in H0. rewrite sat_of_and in H0.
      intros xi Hinxi. simpl in Hinxi. destruct Hinxi.
     -- rewrite <- H1. tauto.
     -- destruct H1.
       ** rewrite <- H1. tauto.
       ** generalize H1. clear H1. generalize xi. clear xi.
          fold (sat k s (diff nnf_eqdec (erase_nnf (and phi psi) G) D')).
          eapply sat_sublist.
          apply sublist_diff_remove_of_diff. assumption.
- destruct (in_dec nnf_eqdec phi m) as [hinphi|hninphi] eqn:Indecphi.
  * apply Hlem. rewrite Heqx.
    simpl. rewrite Indecphi. reflexivity.
  * destruct (in_dec nnf_eqdec psi m) as [hinpsi|hninpsi] eqn:Indecpsi.
    + apply Hlem. rewrite Heqx. simpl. rewrite Indecphi, Indecpsi. reflexivity.
    + simpl in Heqx. rewrite Indecphi, Indecpsi in Heqx. rewrite Heqx in HD'.
      remember (phi :: psi :: remove_nnf (and phi psi) D') as D'' eqn:HeqD''.
      assert (unsatable (diff_nnf D D'')) as HunDD''.
      apply p.
     -- intros d HinD''. rewrite HeqD'' in HinD''. simpl in HinD''.
        destruct HinD'' as [HinD''l|HinD''r].
       ** rewrite <- HinD''l. assumption.
       ** destruct HinD''r as [HinD''rl|HinD''rr].
         ++ rewrite <- HinD''rl. assumption.
         ++ apply in_remove, proj1 in HinD''rr. apply HD'. assumption.
     -- rewrite HeqD'', HeqD. repeat (constructor 3).
        apply sublist_remove. assumption.
     -- intros k s Hsat. specialize (HunDD'' k s). apply HunDD''.
        eapply sat_sublist.
       ** rewrite HeqD, HeqD''. simpl.
          destruct (nnf_eqdec phi phi); try contradiction. simpl.
          destruct (nnf_eqdec psi psi); try contradiction.
          apply remove_diff_remove_sublist_of_sublist. assumption.
       ** assumption.
Defined.

Theorem unsat_of_jump {G1 G2 D : list nnf} (i : or_instance D G1 G2) (m : list nnf) :
  unsatable G1 -> pmark G1 m -> ~ In (left_prcp i) m -> unsatable D.
Proof.
intros H H0 H1. destruct i as [phi psi Hin]. simpl in H1.
remember (phi :: remove_nnf (or phi psi) D) as G1 eqn:HeqG1.
apply (@unsat_sublist (diff_nnf G1 [phi])).
- rewrite HeqG1. simpl.
  destruct (nnf_eqdec phi phi); try contradiction.
  apply remove_sublist.
- apply H0.
  * intros d Hind. simpl in Hind. destruct Hind as [Hindl|]; try contradiction.
    rewrite <- Hindl. assumption.
  * rewrite HeqG1. constructor 3. apply sublist_nil_l.
Qed.

Definition pmark_of_jump {G1 G2 D : list nnf} (i : or_instance D G1 G2) (m : list nnf) :
  unsatable G1 -> pmark G1 m -> ~ In (left_prcp i) m -> {x | pmark D x}.
Proof.
intros H H0 H1.
destruct i as [phi psi Hin]. simpl in H1.
remember (phi :: remove_nnf (or phi psi) D) as G1 eqn:HeqG1.
exists m.
intros B HBm HBsub k s Hsat.
assert (unsatable (diff_nnf G1 (phi :: remove_nnf (or phi psi) B))) as Hlem.
- apply H0.
  * intros d Hind. simpl in Hind. destruct Hind as [Hindl|Hindr].
    + rewrite <- Hindl. assumption.
    + apply in_remove, proj1 in Hindr. apply HBm. assumption.
  * rewrite HeqG1. constructor 3. apply sublist_remove. assumption.
- specialize (Hlem k s). apply Hlem. rewrite HeqG1.
  eapply sat_sublist.
  * simpl. destruct (nnf_eqdec phi phi); try contradiction.
    apply remove_diff_remove_sublist_of_sublist. assumption.
  * assumption.
Defined.

Definition pmark_of_closed_or {G1 G2 D : list nnf} {m1 m2 : list nnf}
  (i : or_instance D G1 G2) : unsatable G1 -> pmark G1 m1 ->
  unsatable G2 -> pmark G2 m2 -> {x | pmark D x}.
Proof.
intros HunG1 HpG1m1 HunG2 HpG2m2. destruct i as [phi psi Hin].
remember (phi :: remove_nnf (or phi psi) D) as G1 eqn:HeqG1.
remember (psi :: remove_nnf (or phi psi) D) as G2 eqn:HeqG2.
remember (mark_or (or phi psi) m1 m2) as x eqn:Heqx.
exists x.
intros D' HD' Hsub.
pose proof (@subset_mark_or_left  (or phi psi) m1 m2) as Hm1x. rewrite <- Heqx in Hm1x.
pose proof (@subset_mark_or_right (or phi psi) m1 m2) as Hm2x. rewrite <- Heqx in Hm2x.
assert (In (or phi psi) x -> unsatable (diff_nnf D D')) as Hlem.
- intros Hinorx k s HsatDD'. assert (In (or phi psi) (diff_nnf D D')) as HinorDD'.
  * apply mem_diff_of_mem.
    + assumption.
    + intro HinorD'. apply (HD' (or phi psi)); assumption.
  * pose proof (HsatDD' _ HinorDD') as Hforceor.
    simpl in Hforceor. destruct Hforceor as [Hforcephi|Hforcepsi].
    + assert (unsatable (diff_nnf G1 D')) as HunG1D'.
     -- apply HpG1m1.
       ** intros d HindD' Hindm1. apply (HD' d).
         ++ assumption.
         ++ apply Hm1x. assumption.
       ** rewrite HeqG1. constructor 2.
      rewrite <- (notin_remove nnf_eqdec D' (or phi psi)).
         ++ apply sublist_remove. assumption.
         ++ intro HinorD'. apply (HD' (or phi psi)); assumption.
     -- apply (HunG1D' k s). eapply sat_subset.
       ** rewrite HeqG1. apply subset_cons_diff.
       ** intros xi Hinxi. simpl in Hinxi. destruct Hinxi as [Hinxil|Hinxir].
         ++ rewrite <- Hinxil. assumption.
         ++ generalize Hinxir. clear Hinxir.
            rename xi into xi'. generalize xi' as xi. clear xi'.
            fold diff_nnf (sat k s (diff_nnf (erase_nnf (or phi psi) D) D')).
            eapply sat_sublist.
          --- apply sublist_diff_remove_of_diff.
          --- assumption.
    + assert (unsatable (diff_nnf G2 D')) as HunG2D'.
     -- apply HpG2m2.
       ** intros d HindD' Hindm2. apply (HD' d).
         ++ assumption.
         ++ apply Hm2x. assumption.
       ** rewrite HeqG2. constructor 2.
      rewrite <- (notin_remove nnf_eqdec D' (or phi psi)).
         ++ apply sublist_remove. assumption.
         ++ intro HinorD'. apply (HD' (or phi psi)); assumption.
     -- apply (HunG2D' k s). eapply sat_subset.
       ** rewrite HeqG2. apply subset_cons_diff.
       ** intros xi Hinxi. simpl in Hinxi. destruct Hinxi as [Hinxil|Hinxir].
         ++ rewrite <- Hinxil. assumption.
         ++ generalize Hinxir. clear Hinxir.
            rename xi into xi'. generalize xi' as xi. clear xi'.
            fold diff_nnf (sat k s (diff_nnf (remove_nnf (or phi psi) D) D')).
            eapply sat_sublist.
          --- apply sublist_diff_remove_of_diff.
          --- assumption.
- pose proof Heqx as Heqxalt. simpl in Heqxalt.
  destruct (in_dec nnf_eqdec phi m1) as [Hinphim1|Hninphim1].
  * apply Hlem. rewrite Heqxalt. simpl. left. reflexivity.
  * intros k s HsatDD'.
    remember (phi :: remove_nnf (or phi psi) D') as D'phi eqn:HeqD'phi.
    assert (unsatable (diff_nnf G1 D'phi)) as HunG1D'phi.
    + apply HpG1m1.
     -- intros d HindD'phi. rewrite HeqD'phi in HindD'phi.
        simpl in HindD'phi. destruct HindD'phi as [Hphid|HinderD'].
       ** rewrite <- Hphid. assumption.
       ** intro Hindm1. apply (HD' d).
         ++ eapply in_remove. exact HinderD'.
         ++ rewrite Heqx. apply (subset_mark_or_left d Hindm1).
     -- rewrite HeqD'phi, HeqG1. constructor 3.
        apply sublist_remove. assumption.
    + apply (HunG1D'phi k s).
      eapply sat_sublist.
     -- rewrite HeqG1, HeqD'phi. simpl.
        destruct (nnf_eqdec phi phi); try contradiction.
        apply remove_diff_remove_sublist_of_sublist.
        assumption.
     -- assumption.
Defined.

Theorem unbox_sublist_of_unmodal (G : list nnf) : forall (i : list nnf),
  In i (unmodal G) -> (forall D, D <+ G -> unbox D <+ i).
Proof.
apply (@mapp _ _ (fun i => forall D : list nnf, D <+ G -> unbox D <+ i)).
intros phi H D HD. constructor 2.
apply unbox_sublist. assumption.
Qed.

Theorem modal_pmark {G} `(ma : modal_applicable G) i m :
  In i (unmodal G) /\ unsatable i -> pmark i m -> pmark G (mark_modal G i m).
Proof.
intros Hi Hpim.
destruct Hi as [HiG Huni].
generalize HiG.
apply (@mappeq _ _ (fun i => (pmark G (mark_modal G i m)))).
intros phi Heqi Hinphi.
intros D HD Hsub k s Hsats.
assert (~ In (dia (hd_nnf i)) D) as HnindiaD.
- intro HindiaD. apply (HD (dia (hd_nnf i))).
  * assumption.
  * simpl. left. reflexivity.
- pose proof (unmodal_jump _ i HiG D Hsats HnindiaD) as Hexsat.
  remember (remove_nnf (hd_nnf i) (unbox D)) as B eqn:HeqB.
  destruct Hexsat as [t Hsatt].
  assert (B <+ i) as HsubBi.
  * eapply sublist_trans.
    + rewrite HeqB. apply remove_sublist.
    + eapply sublist_trans.
     -- eapply unbox_sublist. exact Hsub.
     -- rewrite Heqi. constructor 2. apply sublist_refl.
  * refine (Hpim B _ _ k t _).
    + intros d HindB Hindm.
      pose proof ((sublist_incl HsubBi) d HindB) as Hindi.
      pose proof (box_mem_of_mark_modal G i m Hindm Hindi) as H.
      destruct H as [Hl|Hr].
     -- rewrite Hl in HindB. rewrite HeqB in HindB. rewrite Heqi in HindB.
        simpl in HindB. contradict HindB. apply remove_In.
     -- apply (HD (box d)).
       ** apply unbox_iff.
          assert (B <+ (unbox D)) as HsubBD.
         ++ rewrite HeqB. apply remove_sublist.
         ++ apply (sublist_incl HsubBD). assumption.
       ** assumption.
    + assumption.
    + assumption.
Qed.