Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Require Import ListSetNotations.
Require Import ListSet.
Require Import Arith.
Require Import Bool.
Require Import Datatypes.

Require Import Recdef.
Require Import Lia.
Require Import Wellfounded.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.

Require Import PL.
Import CPL.
Import CPLNotations.
Require Import Deletion.

Open Scope type_scope.
Open Scope list_scope.

Section Reduction.



(*   ∗-REDUCTION    *)

  Fixpoint outstreduc (X : structr) : structr :=
    match X with
    | ∗∗X0 => outstreduc X0
    | X0   => X0
    end.

  Fixpoint strStreduc (X : structr) : structr :=
    match X with
    | X1,, X2 => strStreduc X1,, strStreduc X2
    | ∗∗X0    => strStreduc X0
    | ∗X0     => ∗ (strStreduc X0)
    | X0      => X0
    end.

  Definition streduc (s : sequent) : sequent :=
    match s with X ⊢ Y => strStreduc X ⊢ strStreduc Y end.

  Definition ruleStreduc : rule -> rule := pscmap streduc.

  (* ∗-reducedness *)
  Fixpoint strStreduced (X : structr) : Prop :=
    match X with
    | X1,, X2 => strStreduced X1 /\ strStreduced X2
    | ∗∗X0    => False
    | ∗X0     => strStreduced X0
    | _       => True
    end.

  Definition seqStreduced (s : sequent) : Prop :=
    match s with X ⊢ Y => strStreduced X /\ strStreduced Y end.

  Definition ruleStreduced (r : rule) : Prop :=
    Forall seqStreduced (premsRule r) /\ seqStreduced (conclRule r).

  Lemma tog_invol : forall X, strStreduced X -> tog (tog X) = X.
  Proof.
    intros X H. destruct X; try reflexivity. simpl.
    destruct X; try reflexivity. contradiction.
  Qed.

  Lemma tog_strStreduced (X : structr) : strStreduced X -> strStreduced (tog X).
  Proof.
    intro H. destruct X; try assumption. simpl in H |- *.
    destruct X; try assumption. contradiction.
  Qed.

  Fixpoint strSize (X : structr) : nat :=
    match X with
    | X1,, X2 => 1 + (strSize X1 + strSize X2)
    | ∗X0     => 1 + strSize X0
    | _       => 0
    end.


  Lemma strStreduc_Starred_dec :
    forall (X : structr),
      {X0 | strStreduc X = X0 /\ strStreduc (∗X) = ∗X0} +
        {X0 | strStreduc X = ∗X0 /\ strStreduc (∗X) = X0}.
  Proof.
    intro X. induction X as [X IH] using (wf_nat_ind strSize).
    destruct X.
    - left. exists ($X). tauto.
    - left. exists (£A). tauto.
    - left. exists I. tauto.
    - simpl. destruct X as [ | | |X1|X1 X2] eqn:HeqX. 4:{ apply IH. simpl. lia. }
      all:
      right; destruct (IH X) as [res|res]; try (rewrite HeqX; simpl; lia);
      destruct res as [X' [HeqX' HeqX'']]; rewrite HeqX in HeqX'; try discriminate;
        exists X'; rewrite HeqX'; tauto.
    - left. simpl. exists (strStreduc X1,, strStreduc X2). split; reflexivity.
  Qed.


  Lemma str_stred_streduc : forall X, strStreduced (strStreduc X).
  Proof.
    induction X as [X IH] using (wf_nat_ind strSize).
    destruct X; simpl; try tauto.
    - destruct X; simpl; try tauto; try (split; (apply IH; simpl; lia)).
      apply IH. simpl. lia.
    - split; (apply IH; simpl; lia).
  Qed.

  Lemma seq_stred_streduc : forall s, seqStreduced (streduc s).
  Proof.
    destruct s. simpl. split; apply str_stred_streduc.
  Qed.


  Lemma str_streduc_fixpoint : forall X, strStreduced X -> strStreduc X = X.
  Proof.
    induction X; intro HstX; try reflexivity.
    - simpl in HstX |- *. destruct X; try contradiction;
      rewrite IHX; tauto.
    - simpl in HstX |- *. rewrite IHX1; try rewrite IHX2; tauto.
  Qed.

  Lemma seq_streduc_fixpoint : forall s, seqStreduced s -> streduc s = s.
  Proof.
    intros [X Y] [HstX HstY]. simpl. repeat (rewrite str_streduc_fixpoint); tauto.
  Qed.

  Lemma isPrim_strStred_tostar :
    forall (sX : sstructr), isPrim (snd sX) -> strStreduced (tostar sX).
  Proof.
    intros sX Hpr. destruct sX as [sgn X]. simpl in Hpr.
    destruct X; try contradiction; destruct sgn; tauto.
  Qed.

  Lemma st_pr_PR_eq_tostar :
    forall (X : structr) sX, strStreduced X -> isPrim (snd sX) ->
                                 strPR true X = [sX] -> X = tostar sX.
  Proof.
    intros X sX Hst Hpr HeqspX.
    destruct X; try destruct X; try contradiction; simpl in HeqspX;
      try (pose proof (nb_PR_ge1 X1 true);
           pose proof (nb_PR_ge1 X2 true);
           pose proof (nb_PR_ge1 X1 false);
           pose proof (nb_PR_ge1 X2 false);
           apply (f_equal (@length sstructr)) in HeqspX;
           rewrite app_length in HeqspX; simpl in HeqspX; lia);
    injection HeqspX; intro HeqsX; rewrite <- HeqsX; reflexivity.
  Qed.

  Lemma str_stred_sdel : forall X sY, strStreduced X -> strStreduced (strDel X sY).
  Proof.
    induction X; intros sY HstX; simpl in HstX |- *; try tauto.
    - destruct X; try contradiction; try (apply tog_strStreduced; apply IHX; assumption).   
    - destruct HstX as [HstX1 HstX2].
      specialize (IHX1 sY HstX1). specialize (IHX2 sY HstX2).
      destruct (bstrSub X1 sY); destruct (bstrNiso X1 sY);
      destruct (bstrSub X2 sY); destruct (bstrNiso X2 sY);
      simpl; tauto.   
  Qed.

  Lemma seq_stred_sdel : forall s sY, seqStreduced s -> seqStreduced (seqDel s sY).
  Proof.
    destruct s. intros sY Hsts. simpl in Hsts |- *.
    destruct Hsts as [HstX HstY].
    destruct (bstrNiso X (sws sY)); [|destruct (bstrNiso Y sY)].
    - simpl. split; [apply str_stred_sdel|]; assumption.
    - simpl. split; [|apply str_stred_sdel]; assumption.
    - simpl. split; assumption.
  Qed.



(*     DUPLICATE-REDUCTION      *)

  Function dreduc (s : sequent) {measure nb_PR s} : sequent :=
    if le_gt_dec (length (PR s)) 2 then s (* if length (PR s) = 2 *)
    else match find_dup (PR s) with (* if there is a duplicate sX in PR s *)
      | Some sX => dreduc (seqDel s sX)
      | None    => s
      end.
  Proof.
    intros s Hlen _ sZ Hdup. apply find_dup_is_dup in Hdup.
      apply seqgt2_del_decr_len; assumption.
  Defined.


  Definition reduc (s : sequent) : sequent := streduc (dreduc s).

  Definition ruleDreduc : rule -> rule := pscmap dreduc.

  Definition ruleReduc : rule -> rule := pscmap reduc.

  Inductive dreduced (l : list (sstructr)) : Prop :=
    | len2_dreduced : length l = 2 -> dreduced l
    | NoDup_dreduced : length l > 2 -> NoDup l -> dreduced l.

  Definition seqDreduced (s : sequent) : Prop := dreduced (PR s).

  Definition seqReduced (s : sequent) : Prop := seqStreduced s /\ seqDreduced s.

  Definition ruleDreduced (r : rule) : Prop :=
    Forall seqDreduced (premsRule r) /\ seqDreduced (conclRule r).
  
  Definition ruleReduced (r : rule) : Prop :=
    Forall seqReduced (premsRule r) /\ seqReduced (conclRule r).

  Inductive semidreduced (l : list (sstructr)) : Prop :=
    | dreduced_semidreduced : dreduced l -> semidreduced l
    | erase_semidreduced : length l > 2 -> forall sX, dreduced (erase sX l) -> semidreduced l.

  Definition seqSemidreduced (s : sequent) : Prop := semidreduced (PR s).

  Definition seqSemireduced (s : sequent) : Prop := seqStreduced s /\ seqSemidreduced s.

  Definition dtSemidreduced (dt : dertree) : Prop := allDT (fun d => seqSemidreduced (conclDT d)) dt.
  
  Definition dtSemireduced (dt : dertree) : Prop := allDT (fun d => seqSemireduced (conclDT d)) dt.

  Lemma ge2_NoDup_dreduced (l : list (sstructr)) :
    length l >= 2 -> NoDup l -> dreduced l.
  Proof.
    intros Hlen HND. destruct (le_lt_eq_dec _ _ Hlen) as [Hgt|Heq].
    - apply NoDup_dreduced; assumption.
    - apply len2_dreduced. apply eq_sym. assumption.
  Qed.

  Lemma seq_red_semireduced : forall s, seqReduced s -> seqSemireduced s.
  Proof.
    intros s [Hsts Hsps]. split; try assumption. apply dreduced_semidreduced. assumption.
  Qed.

  Lemma dreduced_lenge2 : forall E, dreduced E -> length E >= 2.
  Proof. intros E Hsp. destruct Hsp; lia. Qed.

  Lemma semidreduced_lenge2 : forall E, semidreduced E -> length E >= 2.
  Proof. intros E Hssp. destruct Hssp; try lia. destruct H; lia. Qed.
  
  Lemma len3_semidreduced : forall l, length l = 3 -> semidreduced l.
  Proof.
    intros l Hlen. destruct l as [|sX l'] eqn:Heql;
      try discriminate.
    apply erase_semidreduced with sX; try lia.
    apply len2_dreduced. simpl. destruct (sstructr_eq_dec sX sX);
      try contradiction.
    simpl in Hlen. lia.
  Qed.
  
  Lemma len3_seqSemidreduced : forall s, length (PR s) = 3 -> seqSemidreduced s.
  Proof.
    intro s. unfold seqSemidreduced. apply len3_semidreduced.
  Qed.


  Lemma seq_dreduced_dreduc : forall s, seqDreduced (dreduc s).
  Proof.
    intro s. functional induction dreduc s; try assumption.
    - apply len2_dreduced. pose proof (nb_seqPR_ge2 s). lia.
    - apply NoDup_dreduced; try assumption.
      + apply find_dup_NoDup. assumption.
  Qed.
  
  Lemma seq_semidreduced_dreduc : forall s, seqSemidreduced (dreduc s).
  Proof. intro s. apply dreduced_semidreduced, seq_dreduced_dreduc. Qed.

  Lemma seq_stred_dreduc : forall s, seqStreduced s -> seqStreduced (dreduc s).
  Proof.
    intros s Hsts. functional induction dreduc s; try assumption;
      apply IHs0; apply seq_stred_sdel; assumption.
  Qed.

  Lemma strStreduc_same_PR : forall (X : structr) b, strPR b X = strPR b (strStreduc X).
  Proof.
    induction X as [X IH] using (wf_nat_ind strSize).
    intro b. destruct X; try reflexivity.
    - simpl. destruct X; try (apply IH); try (simpl; lia).
      simpl. rewrite negb_involutive. apply IH. simpl. lia.
    - simpl. rewrite (IH X1), (IH X2); try reflexivity; simpl; lia.
  Qed.

  Lemma streduc_same_PR : forall (s : sequent), PR s = PR (streduc s).
  Proof.
    intros [X Y]. simpl.
    rewrite (strStreduc_same_PR X).
    rewrite (strStreduc_same_PR Y).
    reflexivity.
  Qed.

  Lemma seq_dreduced_streduc : forall s, seqDreduced s -> seqDreduced (streduc s).
  Proof.
    intros s Hsp. unfold seqDreduced in Hsp |- *.
    rewrite <- streduc_same_PR. assumption.
  Qed.

  Lemma seq_semidreduced_streduc : forall s, seqSemidreduced s -> seqSemidreduced (streduc s).
  Proof.
    intros s Hssp. unfold seqSemidreduced in Hssp |- *.
    rewrite <- streduc_same_PR. assumption.
  Qed.

  Lemma seq_semidreduced_reduc : forall s, seqSemidreduced (reduc s).
  Proof. intro s. unfold reduc. apply seq_semidreduced_streduc, seq_semidreduced_dreduc. Qed.

  Lemma seq_red_reduc : forall s, seqReduced (reduc s).
  Proof.
    intro s. unfold reduc.
    split; try apply seq_stred_streduc.
    apply seq_dreduced_streduc, seq_dreduced_dreduc.
  Qed.

  Lemma listseq_red_reduc : forall l, Forall seqReduced (map reduc l).
  Proof.
    induction l; simpl; constructor.
    apply seq_red_reduc. assumption.
  Qed.

  Lemma rule_red_reduc : forall r, ruleReduced (ruleReduc r).
  Proof.
    intros [l s]. unfold ruleReduced. simpl.
    split; [apply listseq_red_reduc | apply seq_red_reduc].
  Qed.
    

  Lemma seq_dreduc_fixpoint : forall s, seqDreduced s -> dreduc s = s.
  Proof.
    intros s Hreds. functional induction dreduc s; try reflexivity;
      inversion Hreds; try lia.
    - contradict H0. apply (find_dup_not_NoDup _ _ e0).
  Qed.

  Lemma seq_reduc_fixpoint : forall s, seqReduced s -> reduc s = s.
  Proof.
    intros s [Hsts Hsps]. unfold reduc.
    rewrite seq_dreduc_fixpoint; try assumption.
    apply seq_streduc_fixpoint. assumption.
  Qed.

  Lemma ruleReduc_decomp : forall r, ruleReduc r = ruleStreduc (ruleDreduc r).
  Proof.
    intro r. destruct r. simpl. rewrite map_map. reflexivity.
  Qed.

  Lemma listseq_streduc_fixpoint :
    forall (l : list (sequent)), Forall seqStreduced l -> map streduc l = l.
  Proof.
    induction l; try tauto.
    intro H. inversion H. simpl.
    rewrite seq_streduc_fixpoint; try assumption.
    rewrite IHl; tauto.
  Qed.

  Lemma rule_streduc_fixpoint : forall r, ruleReduced r -> ruleStreduc r = r.
  Proof.
    intros [l s] Hred. unfold ruleReduced, ruleStreduced, ruleDreduced in Hred.
    simpl in Hred |- *. unfold seqReduced in Hred.
    destruct Hred as [Hredl [Hsts _]]. apply Forall_and_inv in Hredl.
    rewrite listseq_streduc_fixpoint; try tauto.
    rewrite seq_streduc_fixpoint; tauto.
  Qed.

  Lemma mset_incl_dreduced : forall E F, length E >= 2 -> E ⫅ F -> dreduced F -> dreduced E.
  Proof.
    intros E F Hlen Hsub HsspF. destruct HsspF.
    - apply len2_dreduced. apply (mset_incl_length) in Hsub. lia.
    - destruct (le_lt_eq_dec _ _ Hlen) as [Hlenlt|Hleneq];
        try (apply len2_dreduced; apply eq_sym; assumption).
      apply NoDup_dreduced; try assumption;
        try apply (mset_incl_NoDup _ _ H0 Hsub).
  Qed.      

  Lemma mset_incl_semidreduced : forall E F, length E >= 2 -> E ⫅ F -> semidreduced F -> semidreduced E.
  Proof.
    intros E F Hlen Hsub HsspF. destruct HsspF.
    - apply dreduced_semidreduced. apply (mset_incl_dreduced E F); assumption.
    - destruct (le_lt_eq_dec _ _ Hlen) as [Hlenlt|Hleneq].
      + apply erase_semidreduced with sX; try assumption.
        apply (mset_incl_erase_erase _ _ sX) in Hsub.
        apply (mset_incl_dreduced _ (erase sX F)); try assumption.
        pose proof (erase_length_bound' E sX). lia.
      + apply dreduced_semidreduced, len2_dreduced. apply eq_sym. assumption.
  Qed.

  Lemma mset_incl_seqSemidreduced : forall s t, PR s ⫅ PR t -> seqSemidreduced t -> seqSemidreduced s.
  Proof.
    intros s t H. apply mset_incl_semidreduced; try assumption.
    apply nb_seqPR_ge2.
  Qed.

  Lemma mset_eq_semidreduced : forall E F, E ≡ F -> semidreduced F -> semidreduced E.
  Proof.
    intros E F Heq Hssp. apply (mset_incl_semidreduced E F); try assumption.
    - apply semidreduced_lenge2 in Hssp.
      apply mset_eq_length in Heq. rewrite Heq. assumption.
    - apply mset_eq_incl. assumption.
  Qed.

  Lemma bstrSub_bstrNiso : forall X sY, bstrSub X sY = false -> bstrNiso X sY = false.
  Proof.
    intros X sY Hsub. apply not_true_is_false.
    intro Hniso. apply diff_false_true.
    apply bstrNiso_bstrSub in Hniso.
    rewrite <- Hsub, <- Hniso. reflexivity.
  Qed.

  Lemma swsc_b_true : forall b X, swsc b (true, X) = (b, X).
  Proof. intros b X. destruct b; reflexivity. Qed.

  Lemma in_strPR_sub_iff' : forall {X sY} b, isPrim (snd sY) -> swsc b sY ∈ strPR b X <-> bstrSub X sY = true.
  Proof.
    intros X [q Y] b. intro H.
    split; [apply in_strPR_sub'|apply sub_in_PR'; assumption].
  Qed.

  Lemma in_strPR_sub_iff : forall X sY b,
      isPrim (snd sY) -> sY ∈ strPR b X <-> bstrSub X (swsc b sY) = true.
  Proof.
    intros X [q Y] b. intro H.
    split; [apply in_strPR_sub|apply sub_in_PR; assumption].
  Qed.

  Lemma not_strPR_not_sub : forall X sY b,
      isPrim (snd sY) -> sY ∉ strPR b X -> bstrSub X (swsc b sY) = false.
  Proof.
    intros X sY b Hpr Hnin. destruct (bstrSub X (swsc b sY)) eqn:Heq;
      try reflexivity.
    contradict Hnin. apply in_strPR_sub_iff; assumption.
  Qed.
  
  Lemma count_sws : forall X sZ b, count (strPR b X) (sws sZ) = count (strPR (negb b) X) sZ.
  Proof.
    intros X sZ b. rewrite <- (negb_involutive b) at 1.
    rewrite (PR_PR_negb_eq_imp _ _ _ eq_refl).
    rewrite count_map_inj; [reflexivity|].
    intros [b1 X1] [b2 X2] H. injection H.
    intros HeqX Heqb. apply ssrbool.negb_inj in Heqb.
    rewrite HeqX, Heqb. reflexivity.
  Qed.

  Lemma dreduc_PR_set_eq : forall s, PR (dreduc s) ≃ PR s.
  Proof.
    intro s. functional induction dreduc s; try apply set_eq_refl.
    eapply set_eq_tran; try apply IHs0.
    apply find_dup_is_dup in e0.
    assert (In sX (PR s)) as Hin by (rewrite count_In; lia).
    pose proof (seqPR_isPrim _ Hin) as HprX.
    pose proof (seqgt2_same_del_count _ _ _x e0) as Hcnt.
    assert (In sX (PR (seqDel s sX))) as Hindel by (rewrite count_In; lia).
    apply set_eq_double_incl. split;
      [apply mset_incl_incl; apply mset_incl_seqDel; assumption|].
    intros sY. destruct (eqdec sX sY) as [Heq|Hneq].
    rewrite <- Heq. tauto.
    intro H. apply seqDel_not_same_In_iff; assumption.
  Qed.


  Lemma str_streduc_PR_set_eq : forall X b, set_eq (strPR b (strStreduc X)) (strPR b X).
  Proof.
    induction X as [X IH] using (wf_nat_ind strSize).
    destruct X; intro b; simpl; try (apply set_eq_refl).
    - destruct X; try (apply IH; simpl; lia).
      simpl. rewrite negb_involutive. apply IH. simpl. lia.
    - apply set_eq_app_app; apply IH; simpl; lia.
  Qed.

  Lemma seq_streduc_PR_set_eq : forall s, set_eq (PR (streduc s)) (PR s).
  Proof.
    intros [X Y]. simpl. apply set_eq_app_app; apply str_streduc_PR_set_eq.
  Qed.

  Lemma reduc_PR_set_eq : forall s, set_eq (PR (reduc s)) (PR s).
  Proof.
    intro s. unfold reduc.
    eapply set_eq_tran.
    - apply seq_streduc_PR_set_eq.
    - apply dreduc_PR_set_eq.
  Qed.


  Theorem exact_rep_PR (lX : list sstructr) (b : bool) :
    lX <> [] -> Forall (fun sX => isPrim (snd sX)) lX ->
      {X : structr | strPR b X ≡ lX}.
  Proof.
    revert b. induction lX as [|sX lX IH];
      intros b Hnnil Hpr; try contradiction.
    destruct lX as [|sY lX].
    - exists (tostar (swsc b sX)). rewrite PR_tostar_eq.
      + rewrite swsc_invol. apply mset_eq_refl.
      + rewrite snd_swsc_eq. rewrite Forall_forall in Hpr.
        apply Hpr. left. reflexivity.
    - pose proof (Forall_inv Hpr) as HprsX.
      pose proof (Forall_inv_tail Hpr) as HprlX.
      destruct (IH b) as [X HPRX];
        try (contradict Hnin; now right); try assumption; try discriminate.
      exists (tostar (swsc b sX),, X). simpl.
      rewrite PR_tostar_eq;
        try (rewrite snd_swsc_eq; assumption).
      rewrite swsc_invol.
      fold ([sX] ++ (sY :: lX)). apply mset_eq_app_app;
        [apply mset_eq_refl | assumption].
  Defined.    
  
  Theorem NoDup_rep_PR (lX : list sstructr) (b : bool) :
    lX <> [] -> Forall (fun sX => isPrim (snd sX)) lX ->
      {X : structr | strPR b X ≃ lX /\ NoDup (strPR b X)}.
  Proof.
    revert b. induction lX as [|sX lX IH];
      intros b Hnnil Hpr; try contradiction.
    destruct lX as [|sY lX].
    - exists (tostar (swsc b sX)). rewrite PR_tostar_eq. split.
      + rewrite swsc_invol. apply set_eq_refl.
      + apply NoDup_cons; [tauto|apply NoDup_nil].
      + rewrite snd_swsc_eq. rewrite Forall_forall in Hpr.
        apply Hpr. left. reflexivity.
    - pose proof (Forall_inv Hpr) as HprsX.
      pose proof (Forall_inv_tail Hpr) as HprlX.
      destruct (IH b) as [X [HNIX HNDX]];
        try (contradict Hnin; now right); try assumption; try discriminate.
      destruct (in_dec sstructr_eq_dec sX (sY :: lX)) as [Hin|Hnin].
      + exists X. split; try assumption. intros sZ. split.
        * intro HinsZ. right. apply HNIX. assumption.
        * intro HinsZ. destruct HinsZ as [HeqsX|HinsZ].
          rewrite <- HeqsX. apply HNIX. assumption.
          apply HNIX. assumption.
      + exists (tostar (swsc b sX),, X). simpl.
        rewrite PR_tostar_eq;
          try (rewrite snd_swsc_eq; assumption).
        rewrite swsc_invol. split.
        * fold ([sX] ++ (sY :: lX)).
          apply set_eq_app_app; try assumption.
          apply set_eq_refl.
        * simpl. constructor; try assumption.
          contradict Hnin. apply HNIX. assumption.
  Defined.

  

End Reduction.
