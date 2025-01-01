Require Import String.
Open Scope string_scope.
Require Import List SetoidList.
Import ListNotations.
Require Import ListSetNotations.
Require Import ListSet.
Require Import Arith.
Require Import Bool.
Require Import Datatypes.
Require Import Permutation.

Require Import Recdef.
Require Import Lia.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.
Require Import Derivability.
Require Import Deletion.
Require Import Reduction.

Require Import PL.
Import CPL.
Import CPLNotations.


Open Scope type_scope.
Open Scope list_scope.


Section Finiteness.

  Definition remove_lsstr := remove (list_eq_dec sstructr_eq_dec).

  Definition Comma_combins (lX1 lX2 : list (structr)) : list structr :=
    fold_right (fun X => app (map (Comma X) lX2)) [] lX1.

  Definition SCN_combins (lX1 lX2 : list (structr)) : list structr :=
    fold_right (fun X => app (map (fun Y => ∗(tog X,, tog Y)) lX2)) [] lX1.

  Theorem finite_prim_strStreduced (ls : list (sstructr)) :
    Forall (fun sX => isPrim (snd sX)) ls ->
    {lX : list structr |
      forall X, In X lX <-> (strStreduced X /\ mset_eq (strPR true X) ls)}.
  Proof.
    induction ls as [ls IH] using (wf_nat_ind (@length sstructr)). intro Hallpr.
    destruct (length ls) as [|n] eqn:Heqlen; [idtac | destruct n].
    - exists []. apply length_zero_iff_nil in Heqlen. rewrite Heqlen.
      intro X. split; try contradiction. intros [_ H].
      apply mset_eq_length in H. simpl in H.
      pose proof (nb_PR_ge1 X true). lia.
    - destruct ls as [|sZ ls]; try discriminate.
      pose proof (Forall_inv Hallpr) as HprZ. simpl in HprZ.
      destruct ls; try discriminate. exists [tostar sZ].
      destruct sZ as [sgn Z]. intro X. split.
      + intro HinX. destruct HinX as [HeqX|]; try contradiction.
        rewrite <- HeqX. split;
          try now apply isPrim_strStred_tostar.
        rewrite PR_tostar_eq; try assumption.
        apply mset_eq_refl.
      + intros [HstX Hmeq]. left. apply eq_sym.
        apply st_pr_PR_eq_tostar; try assumption.
        apply mset_eq_singl_eq. assumption.
    - assert (ForallT (fun y => {plX : (list structr) * (list structr) |
        (forall X : structr, In X (fst plX) <-> strStreduced X /\ mset_eq (strPR true X) y) /\
        (forall X : structr, In X (snd plX) <-> strStreduced X /\ mset_eq (strPR true X) (mset_compl y ls))})
      (nt_power_mset ls)) as Hall.
      apply ForallT_forall. intros l Hinl. apply (@In_InA _ mset_eq _) in Hinl.
      apply nt_power_mset_all in Hinl.
      destruct Hinl as [Hinclls [Hlenl0 Hlenlls]].
      pose proof (mset_incl_length _ _ Hinclls) as Hlenlle.
      destruct (IH l) as [flX HflX].
      rewrite <- Heqlen. lia.
      eapply incl_Forall. apply mset_incl_incl. eassumption. assumption.
      destruct (IH (mset_compl l ls)) as [slX HslX].
      rewrite (mset_compl_length _ _ Hinclls), <- Heqlen. lia.
      eapply incl_Forall. apply mset_incl_incl.
      apply mset_compl_mset_incl. assumption. assumption.
      exists (flX, slX). split; assumption.

      apply ForallT_sig_elim in Hall.
      destruct Hall as [ll Hll].
      set (lCom := fold_right (fun pl => app (Comma_combins (fst pl) (snd pl))) [] ll).
      set (lSCN := fold_right (fun pl => app (SCN_combins (fst pl) (snd pl))) [] ll).
      exists (lCom ++ lSCN).

      intro X. split.
      + intro HinX. rewrite in_app_iff in HinX. destruct HinX as [HinX|HinX].
        * apply In_fold_right_app_iff in HinX.
          destruct HinX as [l [Hlinll Hl]].
          apply In_fold_right_app_iff in Hl.
          destruct Hl as [Y [HinY HinX]].
          apply in_map_iff in HinX.
          destruct HinX as [Z [HeqX HinZ]].
          pose proof (Forall2_sig_l Hll _ Hlinll) as [ls0 [Hinls0 [Hls0 Hcls0]]].
          specialize (Hls0 Y). destruct Hls0 as [Hls0 _].
          specialize (Hls0 HinY). destruct Hls0 as [HstrY HmeqY].
          specialize (Hcls0 Z). destruct Hcls0 as [Hcls0 _].
          specialize (Hcls0 HinZ). destruct Hcls0 as [HstrZ HmeqZ].
          rewrite <- HeqX. simpl. split; try tauto.
          apply (@In_InA _ mset_eq _) in Hinls0. apply nt_power_mset_all in Hinls0.
          destruct Hinls0 as [Hincls0ls [Hlenls0 Hlenls0ls]].
          eapply mset_eq_tran; [idtac | apply (mset_compl_ppty _ _ Hincls0ls)].
          apply mset_eq_app_app; assumption.
        * apply In_fold_right_app_iff in HinX.
          destruct HinX as [l [Hlinll Hl]].
          apply In_fold_right_app_iff in Hl.
          destruct Hl as [Y [HinY HinX]].
          apply in_map_iff in HinX.
          destruct HinX as [Z [HeqX HinZ]].
          pose proof (Forall2_sig_l Hll _ Hlinll) as [ls0 [Hinls0 [Hls0 Hcls0]]].
          specialize (Hls0 Y). destruct Hls0 as [Hls0 _].
          specialize (Hls0 HinY). destruct Hls0 as [HstrY HmeqY].
          specialize (Hcls0 Z). destruct Hcls0 as [Hcls0 _].
          specialize (Hcls0 HinZ). destruct Hcls0 as [HstrZ HmeqZ].
          rewrite <- HeqX. simpl. split.
          split; apply tog_strStreduced; assumption.
          apply (@In_InA _ mset_eq _) in Hinls0. apply nt_power_mset_all in Hinls0.
          destruct Hinls0 as [Hincls0ls [Hlenls0 Hlenls0ls]].
          eapply mset_eq_tran; [idtac | apply (mset_compl_ppty _ _ Hincls0ls)].
          rewrite ! PR_tog. apply mset_eq_app_app; assumption.
      + intros [HstX HPRX].
        destruct X; try
        (apply mset_eq_length in HPRX; rewrite Heqlen in HPRX;
          simpl in HPRX; lia).
        * simpl in HPRX, HstX.
          pose proof (mset_eq_length _ _ HPRX) as HlenPRX.
          rewrite Heqlen in HlenPRX.
          destruct X; try (simpl in HlenPRX; lia).
          rewrite in_app_iff. right.
          apply In_fold_right_app_iff.
          simpl in HPRX. simpl in HstX. destruct HstX as [HstX1 HstX2].
          rewrite <- (negb_involutive false) in HPRX.
          simpl (negb false) in HPRX. rewrite <- ! PR_tog in HPRX.
          pose proof (mset_eq_app_mset_compl _ _ _ HPRX) as Heqcompl.
          assert (InA mset_eq (strPR true (tog X1)) (nt_power_mset ls)) as HInA.
          apply nt_power_mset_all. split.
          eapply mset_incl_tran; [idtac | apply mset_eq_incl; eassumption].
          apply mset_incl_appl, mset_incl_refl. split.
          pose proof (nb_PR_ge1 (tog X1) true). lia.
          apply mset_eq_length in HPRX. rewrite app_length in HPRX.
          pose proof (nb_PR_ge1 (tog X2) true). lia.
          apply InA_alt in HInA. destruct HInA as [l1 [Hmeq1 Hin1]].
          destruct (Forall2_sig_r Hll l1 Hin1) as [l [Hinl [Hfl Hsl]]].
          exists l. split; try assumption.
          apply In_fold_right_app_iff.
          exists (tog X1). split. apply Hfl.
          apply tog_strStreduced in HstX1. tauto.
          rewrite in_map_iff.
          exists (tog X2). rewrite ! tog_invol; try assumption.
          split. reflexivity. apply Hsl.
          split; try now apply tog_strStreduced.
          eapply mset_eq_tran; try eassumption.
          apply mset_compl_mset_eq_l.
          eapply mset_incl_tran; [idtac | apply mset_eq_incl; eassumption].
          apply mset_incl_appl, mset_incl_refl. assumption.
        * simpl in HPRX, HstX.
          pose proof (mset_eq_app_mset_compl _ _ _ HPRX) as Heqcompl.
          rewrite in_app_iff. left.
          apply In_fold_right_app_iff.
          assert (InA mset_eq (strPR true X1) (nt_power_mset ls)) as HInA.
          apply nt_power_mset_all. split.
          eapply mset_incl_tran; [idtac | apply mset_eq_incl; eassumption].
          apply mset_incl_appl, mset_incl_refl. split.
          pose proof (nb_PR_ge1 X1 true). lia.
          apply mset_eq_length in HPRX. rewrite app_length in HPRX.
          pose proof (nb_PR_ge1 X2 true). lia.
          apply InA_alt in HInA. destruct HInA as [l1 [Hmeq1 Hin1]].
          destruct (Forall2_sig_r Hll l1 Hin1) as [l [Hinl [Hfl Hsl]]].
          exists l. split; try assumption.
          apply In_fold_right_app_iff.
          exists X1. split. apply Hfl. tauto.
          apply in_map_iff. exists X2. split; try reflexivity.
          apply Hsl. split; try tauto.
          eapply mset_eq_tran; try eassumption.
          apply mset_compl_mset_eq_l.
          eapply mset_incl_tran; [idtac | apply mset_eq_incl; eassumption].
          apply mset_incl_appl, mset_incl_refl. assumption.
  Defined.

  Theorem finite_strStreduced (ls : list (sstructr)) :
    {lX : list structr |
      forall X, In X lX <-> (strStreduced X /\ mset_eq (strPR true X) ls)}.
  Proof.
    destruct (Forall_Exists_dec _ (fun sX => isPrim_dec (snd sX)) ls) as [Hall|Hexn];
      try now apply finite_prim_strStreduced.
    exists []. intro X. simpl. split; try contradiction.
    intros [_ H]. apply Exists_exists in Hexn.
    destruct Hexn as [sX [Hin Hnpr]]. contradict Hnpr.
    apply (PR_isPrim X true). apply mset_eq_set_eq in H.
    apply H. assumption.
  Defined.    
    

  

  Fixpoint strToSeq (l : list (structr)) : list sequent :=
    match l with
    | []     => []
    | Z :: l' =>
        match Z with
        | X,, Y => tog X ⊢ Y :: strToSeq l'
        | _     => strToSeq l'
        end
    end.

  Lemma strToSeq_In :
    forall l, Forall strStreduced l ->
         forall X Y, In (X ⊢ Y) (strToSeq l) <-> (seqStreduced (X ⊢ Y) /\ In (tog X,, Y) l).
  Proof.
    induction l as [|Z l]; simpl; try tauto. intros Hst X Y.    
    pose proof (Forall_inv Hst) as HstZ.
    pose proof (Forall_inv_tail Hst) as Hstl.
    split.
    - intro HinXY. destruct Z; try (destruct HinXY as [HeqXY|HinXY]);
        try (rewrite IHl in HinXY; try assumption; simpl in HinXY; tauto).
      simpl in HstZ. injection HeqXY.
      intros HeqY HeqX. rewrite <- HeqX, <- HeqY. split.
      + split; try tauto. apply tog_strStreduced. tauto.
      + left. rewrite tog_invol; tauto.
    - intros [[HstX HstY] [HeqZ|Hin]].
      + destruct Z; try discriminate.
        injection HeqZ. intros HeqZ2 HeqZ1. left.
        rewrite HeqZ1, HeqZ2. rewrite tog_invol; tauto. 
      + destruct Z; try right;
          apply IHl; try assumption; simpl; tauto.
  Qed.


  Theorem finite_seqStreduced (ls : list (sstructr)) :
    {lu : list sequent |
      forall s, In s lu <-> (seqStreduced s /\ mset_eq (PR s) ls)}.
  Proof.
    destruct (finite_strStreduced ls) as [lX HlX].
    exists (strToSeq lX). intro s. destruct s. rewrite strToSeq_In.
    rewrite HlX. simpl. rewrite PR_tog. split.
    - intro H. repeat (split; try tauto).
    - intro H. repeat (split; try tauto). apply tog_strStreduced; tauto.
    - apply Forall_forall. intros Z HZ. apply HlX. assumption.
  Defined.

  Theorem finite_seqStreduced_multi (llX : list (list (sstructr))) :
    {ls : list sequent |
      forall s, In s ls <-> (seqStreduced s /\ InA mset_eq (PR s) llX)}.
  Proof.
    exists (fold_right (fun l => app (proj1_sig (finite_seqStreduced l))) [] llX).
    intro s. rewrite In_fold_right_app_iff. split.
    - intros [l [Hinl Hins]]. apply (proj2_sig (finite_seqStreduced l)) in Hins.
      destruct Hins as [Hsts Hmeq]. split; try assumption.
      rewrite InA_alt. exists l. tauto.
    - intros [Hsts HInA]. rewrite InA_alt in HInA.
      destruct HInA as [l [Hmeq Hinl]].
      exists l. split; try assumption.
      apply (proj2_sig (finite_seqStreduced l)). tauto.
  Defined.



  Theorem finite_seqSemireduced (lX : list (sstructr)) :
    {ls : list sequent |
      forall s, In s ls <-> (seqSemireduced s /\ incl (PR s) lX)}.
  Proof.
    rename lX into lX'.
    set (lX := nodup sstructr_eq_dec lX').
    assert (NoDup lX) as HNDlX by apply NoDup_nodup.
    destruct (all_msets_len lX 2) as [lX2 HlX2].
    set (lXp := power_mset lX).
    pose proof (power_mset_all lX) as HlXp.
    fold mset_incl in HlXp. fold mset_eq in HlXp. fold lXp in HlXp.
    destruct (all_msets_len lX 3) as [lX3 HlX3].
    set (lXs := fold_right (fun l => app (map (fun sX => sX :: l) lX)) [] lXp).
    pose proof (In_fold_right_app_iff' lXs eq_refl) as HlXs.
    destruct (finite_seqStreduced_multi (lX2 ++ lXp ++ lX3 ++ lXs)) as [ls Hls].
    exists ls.
    setoid_rewrite <- (set_eq_incl_r _ _ _ (nodup_In sstructr_eq_dec lX')).
    fold lX. intros s. pose proof (nb_seqPR_ge2 s) as Hlensprs. split.
    - intro Hins. rewrite Hls in Hins. destruct Hins as [Hstred Hinspr].
      repeat setoid_rewrite InA_app_iff in Hinspr.
      destruct Hinspr as [Hinspr|[Hinspr|[Hinspr|Hinspr]]];
        rewrite InA_alt in Hinspr; destruct Hinspr as [l [Heql Hinl]].
      + rewrite HlX2 in Hinl. destruct Hinl as [Hlenl Hincl].
        pose proof (mset_eq_length _ _ Heql) as HlenPR.
        fold (sstructr) in Hlenl.
        (* Set Printing All. to understand what's going on *)
        rewrite Hlenl in HlenPR. split.
        * split; try assumption. apply dreduced_semidreduced, len2_dreduced. assumption.
        * intros sX HinsX. apply Hincl. apply mset_eq_set_eq in Heql.
          apply Heql. assumption.
      + apply (In_InA Equivalence_mset_eq) in Hinl.
        rewrite <- HlXp in Hinl. apply (mset_eq_incl_l _ _ _ Heql) in Hinl.
        pose proof (mset_incl_NoDup _ _ HNDlX Hinl) as HNDspr.
        split.
        * split; try assumption. destruct (le_lt_eq_dec _ _ Hlensprs) as [Hlenlt|Hleneq];
            try (apply dreduced_semidreduced, len2_dreduced; now rewrite Hleneq).
          apply dreduced_semidreduced, ge2_NoDup_dreduced; assumption.
        * eapply incl_tran.
          apply (mset_incl_incl _ _ Hinl). apply incl_refl.
      + rewrite HlX3 in Hinl. destruct Hinl as [Hlenl Hincl].
        pose proof (mset_eq_length _ _ Heql) as HlenPR.
        fold (sstructr) in Hlenl.
        rewrite Hlenl in HlenPR. split.
        * split; try assumption. apply len3_semidreduced. assumption.
        * intros sX HinsX. apply Hincl.
          apply mset_eq_set_eq in Heql. apply Heql.
          assumption.
      + rewrite HlXs in Hinl. destruct Hinl as [l' [Hinl' Hinl]].
        apply (In_InA Equivalence_mset_eq) in Hinl'.
        rewrite <- HlXp in Hinl'. rewrite in_map_iff in Hinl.
        destruct Hinl as [sX [HeqsX HinsX]].
        pose proof (mset_incl_NoDup _ _ HNDlX Hinl') as HNDl'.
        assert (In sX (PR s)) as HinsXspr.
        { apply (mset_eq_set_eq Heql). rewrite <- HeqsX. now left. }
        pose proof (erase_In_length _ _ HinsXspr) as Hlener.
        fold erase in Hlener. split.
        * split; try assumption. destruct (le_lt_eq_dec _ _ Hlensprs) as [Hlenlt|Hleneq];
            try (apply dreduced_semidreduced, len2_dreduced; now rewrite Hleneq).
          apply erase_semidreduced with sX; try assumption.
          destruct (le_lt_eq_dec _ _ Hlenlt) as [Hlenlt3|Hleneq];
            try (apply len2_dreduced; lia). fold (sstructr) in *.
          apply ge2_NoDup_dreduced; try lia.
          rewrite NoDup_count.
          intro sY. destruct (sstructr_eq_dec sX sY) as [HeqsY|HneqsY].
           -- rewrite <- HeqsY. rewrite count_erase_same.
              specialize (Heql sX). rewrite Heql. rewrite <- HeqsX. simpl.
              destruct (sstructr_eq_dec sX sX); try contradiction.
              rewrite NoDup_count in HNDl'.
              specialize (HNDl' sX). lia.
           -- rewrite count_erase_not_same; try assumption.
              specialize (Heql sY). rewrite Heql. rewrite <- HeqsX. simpl.
              destruct (sstructr_eq_dec sX sY); try contradiction.
              rewrite NoDup_count in HNDl'. apply HNDl'.
        * intros sY HinsY. apply (mset_eq_set_eq Heql) in HinsY.
          rewrite <- HeqsX in HinsY. destruct HinsY as [HinsY|HinsY].
         -- rewrite <- HinsY. assumption.
         -- apply (mset_incl_incl _ _ Hinl'). assumption.

    - intros [[Hsts Hssps] Hincs]. destruct Hssps as
        [[Hlen2|Hlen2 HND]|Hlen2 sX [Hlen2'|Hlen2' HND]];
        apply Hls; split; try assumption; repeat setoid_rewrite InA_app_iff.
      4: destruct (in_dec sstructr_eq_dec sX (PR s)) as [HsXspr|HnsXspr].
      + left. rewrite InA_alt.
        exists (PR s). split; try apply mset_eq_refl.
        apply HlX2. split; try assumption. 
      + right. left. apply HlXp. apply (NoDup_l_mset_incl_iff _ _ HND).
        assumption.
      + right. right. left. rewrite InA_alt.
        exists (PR s). split; try apply mset_eq_refl.
        apply HlX3. split.
        * fold (sstructr).
          destruct (erase_or_length (PR s) sX); lia.
        * assumption.
      + right. right. right. rewrite InA_alt.
        pose proof Hincs as Hinces.
        apply (incl_tran (erase_incl (PR s) sX)) in Hinces.

        rewrite <- NoDup_l_mset_incl_iff in Hinces; try assumption.
        assert (mset_incl (erase sX (PR s)) lX) as Hincespr.
        { eapply mset_incl_tran; try eassumption. apply mset_incl_refl. }
        apply HlXp in Hincespr. rewrite InA_alt in Hincespr.
        destruct Hincespr as [le [Hmeqle Hinle]].
        exists (sX :: le). split; try now apply mset_eq_erase_cons.
        apply HlXs. exists le. split; try assumption.
        apply in_map_iff. exists sX. split; try reflexivity.
        apply Hincs. assumption.
      + rewrite (erase_not_In _ _ HnsXspr) in Hlen2', HND.
        right. left. apply HlXp. apply (NoDup_l_mset_incl_iff _ _ HND).
        assumption.
  Defined.

End Finiteness.
