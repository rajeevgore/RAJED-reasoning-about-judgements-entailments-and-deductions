From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import size.
From Ksat Require Import ops.

Require Import Arith.
Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Require Import Classical.


Fixpoint force (M : kripke) (w : world M) (xi : nnf) : Prop :=
  match xi with
  | var p       => val M w p
  | neg p       => ~ val M w p
  | and phi psi => (force M w phi) /\ (force M w psi)
  | or  phi psi => (force M w phi) \/ (force M w psi)
  | box phi     => forall w', rel M w w' -> force M w' phi
  | dia phi     => exists w', rel M w w' /\ force M w' phi
  end.

Definition sat (M : kripke) (w : world M) (G : list nnf) : Prop :=
  forall phi, In phi G -> force M w phi.

Definition satable (G : list nnf) : Prop :=
  exists (M : kripke) w, sat M w G.

Definition unsatable (G : list nnf) : Prop :=
  forall (M : kripke) w, ~ (sat M w G).

Theorem unsat_singleton {phi} (h : unsatable [phi]) :
  forall (M : kripke) w, ~ force M w phi.
Proof.
intros M w hf. apply (h M w).
intros psi hpsi. apply eq_of_mem_singleton in hpsi.
rewrite <- hpsi in hf. assumption.
Qed.

Theorem sat_of_empty (M : kripke) (w : world M) : sat M w [].
Proof fun phi h => absurd (force M w phi) h (in_nil (a:=phi)).

Theorem ne_empty_of_unsat {G} (h : unsatable G): G <> [].
Proof.
intro heq. rewrite heq in h. unfold unsatable, not in h.
apply (h inhabited_kripke 0). apply sat_of_empty.
Qed.



(* unbox and undia take a list of formulas, and
   get rid of the outermost box or diamond of each formula respectively *)
Definition unmodal (Gamma : list nnf) : list (list nnf) := 
  map (fun d => d :: (unbox Gamma)) (undia Gamma).

Theorem unmodal_size (G : list nnf) :
  forall (i : list nnf), In i (unmodal G) -> (node_size i < node_size G).
Proof.
apply mapp. intros phi H. simpl. apply (undia_size H).
Qed.

Theorem unmodal_mem_box : forall (G i : list nnf),
  In i (unmodal G) -> (forall psi, In (box psi) G -> In psi i).
Proof.
intro G. apply (@mapp _ _ (fun i => forall psi : nnf,
In (box psi) G -> In psi i)).
intros phi H psi H0. simpl. right. apply unbox_iff. exact H0.
Qed.

Theorem unmodal_sat_of_sat (G : list nnf) : forall (i : list nnf),
In i (unmodal G) ->
(forall (M : kripke) w D,
  (forall phi, In (box phi) G -> In (box phi) D) ->
  (forall phi, In (dia phi) G -> In (dia phi) D) ->
  sat M w D -> exists w', sat M w' i).
Proof.
apply (@mapp _ _ (fun i => forall (M : kripke)
(w : world M) (D : list nnf),
(forall phi : nnf, In (box phi) G -> In (box phi) D) ->
(forall phi : nnf, In (dia phi) G -> In (dia phi) D) ->
sat M w D -> exists w', sat M w' i)).
intros phi H M w D H0 H1 H2.
apply undia_iff in H. apply H1 in H. apply H2 in H. elim H.
intros t H3. elim H3. intros H3l H3r. exists t.
unfold sat. intros psi H4. simpl in H4. elim H4.
- intro H4l. rewrite <- H4l. assumption.
- intro H4r. apply unbox_iff in H4r. apply H0 in H4r.
  apply H2 in H4r. apply H4r. assumption.
Qed.

Theorem unmodal_mem_head (G : list nnf) : forall (i : list nnf),
  In i (unmodal G) -> In (dia (hd (var "") i)) G.
Proof.
apply mapp. simpl. apply (@undia_iff G).
Qed.

Theorem unmodal_unsat_of_unsat (G : list nnf) : forall (i : list nnf),
  In i (unmodal G) -> unsatable i ->
    unsatable (dia (hd (var "") i) :: rebox (unbox G)).
Proof.
apply (@mapp _ _ (fun i => unsatable i ->
unsatable (dia (hd (var "") i) :: rebox (unbox G)))).
intros phi H H0. simpl. intros M w Hsat.
pose proof (Hsat (dia phi)) as Hsat0.
pose proof (in_eq (dia phi)) as H1.
apply Hsat0 in H1. elim H1. intros w' H2.
elim H2. intros H2l H2r. apply (H0 M w').
intros psi H3. simpl in H3. elim H3.
- intro H3l. rewrite <- H3l. assumption.
- intro H3r. assert (force M w (box psi)) as H4.
  * apply (Hsat (box psi)). simpl. right. apply rebox_iff. assumption.
  * apply H4. assumption.
Qed.

Theorem mem_unmodal (G : list nnf) (phi:nnf) : In phi (undia G) ->
  In (phi :: unbox G) (unmodal G).
Proof.
apply (in_map (fun d : nnf => d :: unbox G)).
Qed.

Set Implicit Arguments.

Section PropositionalPart.

  Variable M : kripke.

  (* Does not require XM *)
  Lemma force_neg_not : forall w phi,
    force M w (neg_nnf phi) -> ~ force M w phi.
  Proof.
  intros w phi. revert w.
  induction phi as [p|p|phi1 IHphi1 phi2 IHphi2|
  phi1 IHphi1 phi2 IHphi2|phi0 IHphi0|phi0 IHphi0]; intro w; simpl.
  - tauto.
  - intros H H0. contradiction.
  - intro H. destruct H as [H|H].
    + apply IHphi1 in H. tauto.
    + apply IHphi2 in H. tauto.
  - intro H. destruct H as [H1 H2].
    apply IHphi1 in H1. apply IHphi2 in H2. tauto.
  - intros [w' [wRw' Hfw']] H. specialize (H w' wRw').
    contradict H. apply IHphi0. assumption.
  - intros H [w' [wRw' Hfw']]. contradict Hfw'.
    apply IHphi0. apply H. assumption.
  Qed.

  (* Requires XM *)
  Lemma force_not_neg : forall w phi,
    ~ force M w phi -> force M w (neg_nnf phi).
  Proof.
  intros w phi. revert w.
  induction phi as [p|p|phi1 IHphi1 phi2 IHphi2|
  phi1 IHphi1 phi2 IHphi2|phi0 IHphi0|phi0 IHphi0]; intro w; simpl.
  - tauto.
  - apply NNPP.
  - intro H. apply not_and_or in H. destruct H as [H|H].
    + left. apply IHphi1. assumption.
    + right. apply IHphi2. assumption.
  - intro H. apply not_or_and in H. destruct H as [H1 H2].
    split.
    + apply IHphi1. assumption.
    + apply IHphi2. assumption.
  - intro H. apply not_all_ex_not in H. destruct H as [w' H].
    apply imply_to_and in H. exists w'. split; try tauto.
    apply IHphi0. tauto.
  - intros H w' wRw'. pose proof (not_ex_all_not _ _ H w') as H0.
    apply not_and_or in H0. destruct H0 as [H0|H0]; try contradiction.
    apply IHphi0. assumption.
  Qed.

  Theorem force_neg_not_iff : forall w phi,
    force M w (neg_nnf phi) <-> ~ force M w phi.
  Proof.
  intros w phi. revert w.
  induction phi as [p|p|phi1 IHphi1 phi2 IHphi2|
  phi1 IHphi1 phi2 IHphi2|phi0 IHphi0|phi0 IHphi0];
  intro w; simpl; try tauto.
  - setoid_rewrite IHphi1. setoid_rewrite IHphi2. tauto.
  - setoid_rewrite IHphi1. setoid_rewrite IHphi2. tauto.
  - setoid_rewrite IHphi0. split.
    + intros [w' [wRw' Hfw']] H. specialize (H w' wRw').
      contradiction.
    + intro H. apply not_all_ex_not in H. destruct H as [w' H].
      apply imply_to_and in H. exists w'. split; tauto.
  - setoid_rewrite IHphi0. split.
    + intros H [w' [wRw' Hfw']]. contradict Hfw'.
      apply H. assumption.
    + intros H w' wRw'. pose proof (not_ex_all_not _ _ H w') as H0.
      apply not_and_or in H0. destruct H0 as [H0|H0]; try contradiction.
      assumption.
  Qed.

  Theorem sat_subset [G1 G2] w :
    incl G1 G2 -> sat M w G2 -> sat M w G1.
  Proof fun h1 h2 x hx => h2 _ (h1 x hx).

  Theorem sat_sublist [G1 G2] w :
    sublist G1 G2 -> sat M w G2 -> sat M w G1.
  Proof fun h1 => sat_subset (sublist_incl h1).

  Theorem sat_append [G1 G2] w :
    sat M w G1 -> sat M w G2 -> sat M w (G1 ++ G2).
  Proof.
  intros Hsat1 Hsat2. intros xi Hxi. apply in_app_iff in Hxi.
  destruct Hxi; [apply Hsat1 | apply Hsat2]; assumption.
  Qed.

  Theorem append_sat_l [G1 G2] w :
    sat M w (G1 ++ G2) -> sat M w G1.
  Proof.
  intro H. eapply sat_subset.
  2:{ apply H. } apply incl_appl, incl_refl.
  Qed.

  Theorem append_sat_r [G1 G2] w :
    sat M w (G1 ++ G2) -> sat M w G2.
  Proof.
  intro H. eapply sat_subset.
  2:{ apply H. } apply incl_appr, incl_refl.
  Qed.

  Theorem append_sat_both [G1 G2] w :
    sat M w (G1 ++ G2) -> sat M w G1 /\ sat M w G2.
  Proof.
  intro H. split; [eapply append_sat_l | eapply append_sat_r]; exact H.
  Qed.

  Theorem sat_of_and (w : world M) (phi psi : nnf) :
    force M w (and phi psi) <-> (force M w phi) /\ (force M w psi).
  Proof. simpl. tauto. Qed.

  Theorem sat_of_sat_erase [D] w phi :
    sat M w (remove_nnf phi D) -> force M w phi -> sat M w D.
  Proof.
  intros H H0. intros xi Hxi. destruct (nnf_eqdec xi phi) as [heq|hneq].
  - rewrite heq. assumption.
  - apply H. apply in_in_remove; assumption.
  Qed.

  Theorem sat_and_of_sat_split [D] w phi psi :
          sat M w (phi :: psi :: remove_nnf (and phi psi) D) ->
          sat M w D.
  Proof.
  intros H. intros xi Hxi.
  destruct (nnf_eqdec xi (and phi psi)) as [Heq|Hneq].
  - rewrite Heq. simpl. split; apply H; simpl; tauto.
  - apply H. simpl. right. right.
    apply (in_in_remove nnf_eqdec _ Hneq Hxi).
  Qed.

  Theorem sat_or_of_sat_split_left [D] w phi psi :
          sat M w (phi :: remove_nnf (or phi psi) D) ->
          sat M w D.
  Proof.
  intros H. intros xi Hxi. destruct (nnf_eqdec xi (or phi psi)) as [Heq|Hneq].
  - rewrite Heq. simpl. left. apply (H phi). simpl. tauto.
  - apply H. simpl. right.
    apply (in_in_remove nnf_eqdec _ Hneq Hxi).
  Qed.

  Theorem sat_or_of_sat_split_right [D] w phi psi:
          sat M w (psi :: remove_nnf (or phi psi) D) ->
          sat M w D.
  Proof.
  intros H. intros xi Hxi. destruct (nnf_eqdec xi (or phi psi)) as [Heq|Hneq].
  - rewrite Heq. simpl. right. apply (H psi). simpl. tauto.
  - apply H. simpl. right.
    apply (in_in_remove nnf_eqdec _ Hneq Hxi).
  Qed.

End PropositionalPart.

Theorem unsat_subset [G1 G2] : incl G1 G2 -> unsatable G1 ->
unsatable G2.
Proof fun h1 h2 M w h => (h2 M w (sat_subset h1 h)).

Theorem unsat_sublist [G1 G2] (h1 : sublist G1 G2) (h2 : unsatable G1) :
unsatable G2.
Proof fun M w h => h2 M w (sat_sublist h1 h).

Theorem unsat_contra {D p} : In (var p) D -> In (neg p) D -> unsatable D.
Proof.
intros H H0 M w Hsat. apply Hsat in H0. simpl in H0. contradict H0.
apply Hsat in H. simpl in H. exact H.
Qed.

Theorem unsat_and_of_unsat_split [D] phi psi :
        In (and phi psi) D ->
        unsatable (phi :: psi :: remove_nnf (and phi psi) D) ->
        unsatable D.
Proof.
intros H1 H2. intros M w H. apply (H2 M w). intro xi. intro Hxi.
simpl in Hxi. pose proof (H (and phi psi) H1) as H0.
rewrite sat_of_and in H0. elim Hxi.
- intro Hxi1. rewrite <- Hxi1. tauto.
- intro Hxi'. elim Hxi'.
  + intro Hxi2. rewrite <- Hxi2. tauto.
  + intro Hxi3. apply in_remove, proj1 in Hxi3. apply H. assumption.
Qed.

Theorem unsat_or_of_unsat_split [D] phi psi :
        In (or phi psi) D ->
        unsatable (phi :: remove_nnf (or phi psi) D) ->
        unsatable (psi :: remove_nnf (or phi psi) D) ->
        unsatable D.
Proof.
intros H H0 H1. intros M w Hsat.
pose proof (Hsat (or phi psi) H) as H2.
simpl in H2. elim H2.
- intro H2l. apply (H0 M w). intros xi Hxi. simpl in Hxi. elim Hxi.
  + intro Hxil. rewrite <- Hxil. assumption.
  + intro Hxir. apply in_remove, proj1 in Hxir. apply (Hsat xi Hxir).
- intro H2r. apply (H1 M w). intros xi Hxi. simpl in Hxi. elim Hxi.
  + intro Hxil. rewrite <- Hxil. assumption.
  + intro Hxir. apply in_remove, proj1 in Hxir. apply (Hsat xi Hxir).
Qed.



Theorem unmodal_jump (G : list nnf) : forall (i : list nnf),
  In i (unmodal G) -> forall D (M : kripke) w,
    sat M w (diff_nnf G D) -> ~ In (dia (hd_nnf i)) D ->
    exists w', sat M w' (diff_nnf i (remove_nnf (hd_nnf i) (unbox D))).
Proof.
apply (@mapp _ _ (fun i =>
forall (D : list nnf) (M : kripke) (w : world M),
sat M w (diff_nnf G D) ->
~ In (dia (hd_nnf i)) D ->
exists w', sat M w' (diff_nnf i (remove_nnf (hd_nnf i) (unbox D))))).
intros phi Hphi D M w Hsat Hdia.
simpl. unfold diff_nnf.
rewrite (cons_diff_of_not_mem nnf_eqdec phi (unbox G)
  (remove_nnf phi (unbox D)) (remove_In _ (unbox D) phi)).
simpl in Hdia. apply undia_iff in Hphi.
pose proof (mem_diff_of_mem nnf_eqdec (dia phi) G D Hphi Hdia) as H.
pose proof (Hsat (dia phi) H) as H1. simpl in H1. elim H1.
intros t H2. exists t. intros psi Hpsi.
simpl in Hpsi. elim Hpsi.
- intro Hpsil. rewrite <- Hpsil. tauto.
- intro Hpsir.
  pose proof (in_diff_remove_r nnf_eqdec psi phi
  (unbox G) (unbox D) Hpsir) as H3.
  elim H3.
  * intro H3l. rewrite H3l. tauto.
  * intro H3r. rewrite unbox_diff in H3r. apply unbox_iff in H3r.
    apply (Hsat (box psi) H3r). tauto.
Qed.



(* Part of the soundness *)

Theorem unsat_of_closed_and {G D} (i : and_instance G D) :
  unsatable D -> unsatable G.
Proof.
destruct i. apply unsat_and_of_unsat_split. assumption.
Qed.

Theorem unsat_of_closed_or {G1 G2 D : list nnf} (i : or_instance D G1 G2) :
  unsatable G1 -> unsatable G2 -> unsatable D.
Proof.
destruct i. apply unsat_or_of_unsat_split; repeat assumption.
Qed.
