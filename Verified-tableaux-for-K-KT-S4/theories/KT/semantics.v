From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import ops.
From Ksat Require Import semantics.

From KTsat Require Import defs.
From KTsat Require Import size.
From KTsat Require Import ops.

Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Program.



Set Implicit Arguments.

Section PropositionalPart.

  Variables (phi psi : nnf).

  Theorem unsat_contra_seqt {D : seqt} {n} :
    In (var n) D.(main) -> In (neg n) D.(main) -> unsatable_KT (D.(main) ++ D.(hdld)).
  Proof.
  intros H H0 M w Hsat.
  apply (@unsat_contra D.(main) n H H0 M w).
  apply (append_sat_l Hsat).
  Qed.

  Theorem unsat_and_of_unsat_split_seqt {G D} :
    In (and phi psi) D ->
    unsatable_KT ((phi :: psi :: remove_nnf (and phi psi) D) ++ G) ->
    unsatable_KT (D ++ G).
  Proof.
  intros H H0 M w Hsat.
  apply (H0 M w).
  intros xi Hxi.
  apply in_app_iff in Hxi.
  destruct Hxi as [Hxil|Hxir].
  - apply append_sat_l in Hsat.
    simpl in Hxil. destruct Hxil as [Hxil1 | [Hxil2 | Hxil3]].
    * rewrite <- Hxil1. specialize (Hsat (and phi psi) H).
      rewrite sat_of_and in Hsat. tauto.
    * rewrite <- Hxil2. specialize (Hsat (and phi psi) H).
      rewrite sat_of_and in Hsat. tauto.
    * generalize Hxil3. generalize xi.
      fold (@sat M w (remove_nnf (and phi psi) D)).
      eapply sat_subset.
      2:{ apply Hsat. }
      apply remove_subset.
  - apply (append_sat_r Hsat). assumption.
  Qed.

  Theorem sat_and_of_sat_split_seqt {G D} (M : kripke) (w : world M) :
          sat M w ((phi :: psi :: remove_nnf (and phi psi) D) ++ G) ->
          sat M w (D ++ G).
  Proof.
  intro H. intros xi Hxi. apply in_app_iff in Hxi.
  destruct Hxi as [Hxil|Hxir].
  - generalize Hxil. generalize xi.
    fold (@sat M w D).
    apply (@sat_and_of_sat_split _ _ _ phi psi).
    eapply sat_subset.
    2:{ apply H. }
    apply incl_appl, incl_refl.  - generalize Hxir. generalize xi.
    fold (@sat M w G).
    eapply sat_subset.
    2:{ apply H. }
    apply incl_appr, incl_refl.
  Qed.

  Theorem sat_split_of_sat_and_seqt {G D} (M : kripke) (w : world M) :
    In (and phi psi) D -> sat M w (D ++ G) ->
    sat M w ((phi :: psi :: remove_nnf (and phi psi) D) ++ G).
  Proof.
  intros H H0. apply sat_append.
  - apply append_sat_l in H0.
    * intros xi Hxi. simpl in Hxi.
      destruct Hxi as [Hxi1|[Hxi2|Hxi3]].
      + rewrite <- Hxi1. specialize (H0 (and phi psi) H).
        rewrite sat_of_and in H0. tauto.
      + rewrite <- Hxi2. specialize (H0 (and phi psi) H).
        rewrite sat_of_and in H0. tauto.
      + generalize Hxi3. generalize xi.
        fold (@sat M w (remove_nnf (and phi psi) D)).
        eapply sat_subset.
        2:{ apply H0. }
        apply remove_subset.
  - apply (append_sat_r H0).
  Qed.

  Theorem unsat_or_of_unsat_split_seqt {G D} :
    In (or phi psi) D ->
    unsatable_KT (phi :: remove_nnf (or phi psi) D ++ G) ->
    unsatable_KT (psi :: remove_nnf (or phi psi) D ++ G) ->
    unsatable_KT (D ++ G).
  Proof.
  intros H H0 H1. intros M w Hsat.
  assert (force M w (or phi psi)) as H2.
  - apply Hsat. apply in_or_app. left. assumption.
  - destruct H2.
    * apply (H0 M w). apply (@sat_subset _ _ (phi :: D ++ G)).
      + intros xi Hxi. simpl in Hxi. destruct Hxi as [Hxil|Hxir].
      -- left. assumption.
      -- apply in_app_iff in Hxir.
          simpl. right. apply in_or_app.
          destruct Hxir as [Hxir1|Hxir2].
        ** left. eapply (in_remove nnf_eqdec). apply Hxir1.
        ** right. assumption.
      + intros xi Hxi. destruct Hxi as [Hxil|Hxir].
      -- rewrite <- Hxil. assumption.
      -- apply Hsat. assumption.
    * apply (H1 M w). apply (@sat_subset _ _ (psi :: D ++ G)).
      + intros xi Hxi. simpl in Hxi. destruct Hxi as [Hxil|Hxir].
      -- left. assumption.
      -- apply in_app_iff in Hxir.
          simpl. right. apply in_or_app.
          destruct Hxir as [Hxir1|Hxir2].
        ** left. eapply (in_remove nnf_eqdec). apply Hxir1.
        ** right. assumption.
      + intros xi Hxi. destruct Hxi as [Hxil|Hxir].
      -- rewrite <- Hxil. assumption.
      -- apply Hsat. assumption.
  Qed.



  (* KT-specific lemmas *)

  Theorem force_of_force_box (M : KT) (w : world M) :
    force M w (box phi) -> force M w phi.
  Proof.
  intro H. simpl in H. apply H. apply M.(refl_rel).
  Qed.

  Theorem unsat_copy_of_unsat_box {D L} :
          In (box phi) D ->
          unsatable_KT ((phi :: remove_nnf (box phi) D) ++ box phi :: L) ->
          unsatable_KT (D ++ L).
  Proof.
  intros H H0 M w Hsat.
  apply append_sat_both in Hsat.
  destruct Hsat as [HsatD HsatL].
  apply (H0 M w).
  intros xi Hxi.
  apply in_app_iff in Hxi. simpl in Hxi.
  destruct Hxi as [[Hxi1|Hxi2]|[Hxi3|Hxi4]].
  - rewrite <- Hxi1. apply force_of_force_box.
    apply HsatD. assumption.
  - apply (@sat_subset _ (remove_nnf (box phi) D)) in HsatD.
    * apply HsatD. assumption.
    * apply remove_subset.
  - rewrite <- Hxi3. apply HsatD. assumption.
  - apply HsatL. assumption.
  Qed.

  Theorem sat_copy_of_sat_box {D L} (M : KT) (w : world M) :
          In (box phi) D ->
          sat M w ((phi :: remove_nnf (box phi) D) ++ box phi :: L) ->
          sat M w (D ++ L).
  Proof.
  intros H H0. intros xi Hxi.
  apply in_app_iff in Hxi.
  destruct Hxi as [HxiD|HxiL].
  - apply H0.
    destruct (nnf_eqdec xi (box phi)) as [Heq|Hneq].
    * apply in_app_iff. right. left. rewrite Heq. reflexivity.
    * apply in_app_iff. left. right.
      apply (in_in_remove nnf_eqdec D Hneq).
      assumption.
  - apply H0. apply in_app_iff. right. right. assumption.
  Qed.

  Theorem sat_box_of_sat_copy {D L} (M : KT) (w : world M) :
          In (box phi) D ->
          sat M w (D ++ L) ->
          sat M w ((phi :: remove_nnf (box phi) D) ++ box phi :: L).
  Proof.
  intros H H0.
  apply append_sat_both in H0.
  destruct H0 as [HsatD HsatL].
  intros xi Hxi. apply in_app_iff in Hxi.
  destruct Hxi as [[Hxi1|Hxi2]|[Hxi3|Hxi4]].
  - rewrite <- Hxi1. apply force_of_force_box.
    apply HsatD. assumption.
  - apply HsatD. apply (in_remove nnf_eqdec _ _ _ Hxi2).
  - rewrite <- Hxi3. apply HsatD. assumption.
  - apply HsatL. assumption.
  Qed.

End PropositionalPart.

Unset Implicit Arguments.


Definition unmodal_seqt (G : seqt) : list seqt.
Proof.
refine (
map
(fun d =>
  {|main  := d :: (unbox (main G ++ hdld G));
    hdld  := [];
    pmain := _;
    phdld := box_only_nil|})
(undia (main G ++ hdld G))).
unfold srefl. simpl. tauto.
Defined.

Definition unmodal_nil_hdld (G : seqt) : forall (i : seqt),
  In i (unmodal_seqt G) -> hdld i = [].
Proof.
apply mapp. auto.
Defined.

Definition unmodal_seqt_size (G : seqt) : forall (i : seqt),
  In i (unmodal_seqt G) -> measure_lex seqt_size i G.
Proof.
apply mapp. intros phi H.
unfold measure_lex, MR. apply left_slex.
simpl. rewrite app_nil_r.
apply undia_degree. assumption.
Defined.

Definition unmodal_mem_box (G : seqt) : forall (i : seqt), In i (unmodal_seqt G) ->
  (forall phi, In (box phi) (main G ++ hdld G) -> In phi (main i)).
Proof.
apply (@mapp _ _
(fun i => forall phi : nnf, In (box phi) (main G ++ hdld G) -> In phi (main i))).
intros phi H psi Hpsi. simpl. right. apply unbox_iff. assumption.
Defined.

Definition unmodal_sat_of_sat (G : seqt) : forall (i : seqt), In i (unmodal_seqt G) ->
  (forall  (M : KT) w D
  (H1 : forall phi, In (box phi) (main G ++ hdld G) -> In (box phi) D)
  (H2 : forall phi, In (dia phi) (main G ++ hdld G) -> In (dia phi) D),
  sat M w D -> exists w', sat M w' (main i)).
Proof.
apply (@mapp _ _ (fun i =>
forall (M : KT) (w : world M) (D : list nnf),
(forall phi : nnf, In (box phi) (main G ++ hdld G) -> In (box phi) D) ->
(forall phi : nnf, In (dia phi) (main G ++ hdld G) -> In (dia phi) D) ->
sat M w D -> exists w', sat M w' (main i))).
intros phi Hmem M w D H1 H2 H.
simpl. apply undia_iff in Hmem.
apply H2 in Hmem. apply H in Hmem.
simpl in Hmem. destruct Hmem as [t Hmem]. destruct Hmem as [Hmeml Hmemr].
exists t. intros psi Hpsi. destruct Hpsi as [Hpsil|Hpsir].
- rewrite <- Hpsil. assumption.
- apply unbox_iff in Hpsir. apply H1 in Hpsir. apply H in Hpsir.
  simpl in Hpsir. apply Hpsir. assumption.
Defined.

Definition unsat_of_unsat_unmodal {G : seqt} `(ma : modal_applicable G) (i : seqt) :
  In i (unmodal_seqt G) /\ unsatable_KT (main i ++ hdld i) ->
  unsatable_KT (main G ++ hdld G).
Proof.
intros H M w Hsat. destruct H as [Hl Hr].
assert (exists w', sat M w' (main i)) as Hex.
- apply (unmodal_sat_of_sat G i Hl M w (main G ++ hdld G)); try auto.
- destruct Hex as [t H0]. apply (Hr M t).
  rewrite (unmodal_nil_hdld G i Hl). rewrite app_nil_r. assumption.
Defined.


(* Part of the soundness *)

Theorem unsat_of_closed_and {G D} (i : and_instance G D) :
  unsatable D -> unsatable G.
Proof.
destruct i. apply unsat_and_of_unsat_split. assumption.
Qed.

Theorem unsat_of_closed_and_seqt {G D} (i : and_instance_seqt G D) :
  unsatable_KT (main D ++ hdld D) -> unsatable_KT (main G ++ hdld G).
Proof.
destruct i. apply unsat_and_of_unsat_split_seqt. assumption.
Qed.

Theorem unsat_of_closed_or_seqt {G1 G2 D} (i : or_instance_seqt D G1 G2) :
  unsatable_KT (main G1 ++ hdld G1) ->
  unsatable_KT (main G2 ++ hdld G2) ->
  unsatable_KT (main D ++ hdld D).
Proof.
destruct i. apply unsat_or_of_unsat_split_seqt. assumption.
Qed.


(* Tree models *)

Inductive batch_sat_seqt : list model -> list seqt -> Prop :=
| bs_nil : batch_sat_seqt [] []
| bs_cons {m} {G} {l1} {l2} : sat builder m (main G ++ hdld G) ->
                              batch_sat_seqt l1 l2 ->
                              batch_sat_seqt (m::l1) (G::l2).


Theorem bs_ex_seqt : forall l G, batch_sat_seqt l G ->
  forall m, In m l -> exists i, In i G /\ sat builder m (main i ++ hdld i).
Proof.
intros l G H. induction H.
- simpl. tauto.
- intros n Hn. simpl in Hn. destruct Hn.
  * exists G. split.
    + simpl. tauto.
    + rewrite <- H1. assumption.
  * pose proof (IHbatch_sat_seqt n H1) as H2. destruct H2 as [l].
    exists l. simpl. tauto.
Qed.

Theorem bs_forall_seqt : forall l G, batch_sat_seqt l G ->
  forall i, In i G -> exists m, In m l /\ sat builder m (main i ++ hdld i).
Proof.
intros l G H. induction H.
- simpl. tauto.
- intros i Hi. destruct Hi.
  * exists m. simpl. rewrite <- H1. tauto.
  * pose proof (IHbatch_sat_seqt i H1) as H2.
    destruct H2 as [n]. exists n. simpl. tauto.
Qed.

Theorem sat_of_batch_sat_main : forall l G `(h : modal_applicable G),
  batch_sat_seqt l (unmodal_seqt G) -> sat builder (mcons vc_atoms l) (main G).
Proof.
intros l G sa vc ma Hbs phi Hphi.
induction phi.
- simpl. apply vc_hypatoms. assumption.
- simpl. intro H. apply vc_hypatoms in H.
  contradict Hphi. apply vc_no_contra. assumption.
- contradict Hphi. apply sa_no_and.
- contradict Hphi. apply sa_no_or.
- contradict Hphi. apply vc_no_box.
- apply undia_iff in Hphi.
  assert (In phi (undia (main G ++ hdld G))) as H.
  * eapply undia_incl; [apply incl_appl, incl_refl | assumption].
  * pose proof (eq_refl (unmodal_seqt G)) as Htemp.
    unfold unmodal_seqt at 2 in Htemp.
    pose proof (in_map_alt Htemp phi H) as H0.
    clear Htemp. simpl in H0.
    pose proof (bs_forall_seqt _ _ Hbs _ H0) as H1.
    simpl in H1. simpl. destruct H1 as [m Hm].
    destruct Hm as [Hml Hmr].
    exists m. split; try tauto. apply Hmr. now left.
Qed.

Theorem sat_of_batch_sat_box : forall l G `(h : modal_applicable G),
  batch_sat_seqt l (unmodal_seqt G) -> forall m, In m l ->
  forall phi, In (box phi) (hdld G) -> force builder m phi.
Proof.
intros l G sa vc ma Hbs m Hm phi Hphi.
pose proof (bs_ex_seqt _ _ Hbs _ Hm) as H.
destruct H as [i [Hil Hir]].
assert (In (box phi) (main G ++ hdld G)) as H.
- eapply incl_appr; [apply incl_refl | apply Hphi].
- assert (sat builder m (main i)) as H0.
  * eapply sat_subset; [apply incl_appl, incl_refl | apply Hir].
  * apply H0. apply (unmodal_mem_box _ _ Hil _ H).
Qed.

Theorem sat_of_batch_sat : forall l G `(h : modal_applicable G),
  batch_sat_seqt l (unmodal_seqt G) ->
  sat builder (mcons vc_atoms l) (main G ++ hdld G).
Proof.
intros l G sa vc ma Hbs.
assert (sat builder (mcons vc_atoms l) (main G)) as Hsatmain.
- apply sat_of_batch_sat_main; assumption.
- assert (forall psi : nnf, In (box psi) (hdld G) ->
  forall w : model, In w l -> force builder w psi) as Hboxhdld.
  * intros psi Hpsi m Hm. apply (sat_of_batch_sat_box _ _ _ Hbs); assumption.
  * apply sat_append; try assumption.
    pose proof (phdld G) as Hboxonly. destruct Hboxonly.
    destruct bo_no_literals. destruct bo_saturated.
    intros phi Hphi. destruct phi; try (contradict Hphi; auto; fail).
    simpl. intros m Hm. destruct Hm as [Hml|Hmr].
    + apply (sat_of_batch_sat_box _ _ _ Hbs); assumption.
    + rewrite <- Hmr. apply (pmain G); assumption.
Qed.
