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
Require Import Relations.
Require Import ssrbool.

Require Import Recdef.
Require Import Lia.
From AAC_tactics Require Import AAC.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.
Require Import Derivability.
Require Import BelnapAid.
Require Import Deletion.
Require Import Reduction.
Require Import Displequiv.
Require Import Decidability.

Require Import Rules.
Require Import PL.
Require Import CPLRules.
Import CPLRules.
Import CPLNotations.

Import ListSetNotations.

Open Scope list_scope.
Open Scope nat_scope.

Definition MDEICW : DISPCALC := MDE ++ ICW.

Definition CPL_DC' : @DISPCALC _ _ _ _ _ _ _ CPL :=
  MDEICW ++ [atrefl; Topr; Botl; Negl; Negr; Conl; Consr; Dissl; Disr; Impsl; Impr].

Lemma mset_eq_PR_deriv (s t : sequent) :
  PR s ≡ PR t -> deriv_rule_P MDEICW (fun u => PR u ≡ PR s) ([s], t).
Proof.
  intro Heq. apply (deriv_rule_P_incl_DC _ MDE).
  - apply incl_appl, incl_refl.
  - apply mset_eq_PR_Deriv_MDE_mset_eq. assumption.
Defined.

Lemma mset_eq_PR_Deriv (s t : sequent) :
  PR s ≡ PR t -> DerivRulePseq MDEICW (fun u => PR u ≡ PR s) ([s], t).
Proof.
  intro Heq. apply DerivRulePseq_iff_deriv_rule_P.
  apply mset_eq_PR_deriv. assumption.
Defined.


Lemma repeat_conts (s : sequent) (sX : sstructr) :
  forall n, n >= 2 -> count (PR s) sX >= n ->
       {t : sequent & DerivRulePseq MDEICW (fun u => PR u ⫅ PR s) ([s], t) &
              count (PR t) sX = n /\ forall sY, sY <> sX -> count (PR s) sY = count (PR t) sY}.
Proof.
  intros n Hnge2 HssXgen.
  assert (isPrim (snd sX)) as HprX.
  { apply (seqPR_isPrim s). rewrite count_In. lia. }
  remember (count (PR s) sX - n) as m.
  revert m s HssXgen Heqm.
  induction m; intros s HssXgen Heqm.
  - exists s. unshelve eexists. confirm_derr (Unf s).
    simpl. apply mset_incl_refl. split; lia.
  - set (lX := listerase (PR s) [sX; sX]).
    destruct (exact_rep_PR lX true) as [Y HY].
    { pose proof (count_bound sX lX) as H.
      unfold lX in H at 1. rewrite count_listerase in H.
      rewrite ! count_cons_eq in H; try reflexivity.
      simpl in H. intro Hnil.
      apply length_zero_iff_nil in Hnil. lia. }
    { eapply incl_Forall; try apply listerase_incl.
      apply Forall_forall. apply seqPR_isPrim. }
    set (s0 := ∗ tostar sX,, ∗ tostar sX ⊢ Y).
    assert (PR s ≡ PR s0) as Heqss0.
    { simpl. rewrite PR_tostar_eq; try assumption.
      simpl swsc. change (([id sX] ++ [id sX])%list) with [sX; sX].
      eapply mset_eq_tran; try apply mset_eq_app_comm.
      eapply mset_eq_tran; try apply mset_eq_app_app;
      try apply mset_eq_sym, HY; try apply mset_eq_refl.
      apply mset_eq_sym, listerase_app_mset_eq.
      intro sZ. simpl.
      destruct (sstructr_eq_dec sX sZ) as [Heq|Hneq];
        try rewrite <- Heq; lia. }
    pose proof (mset_eq_PR_Deriv s s0 Heqss0) as Hders0.
    set (s1 := ∗ tostar sX ⊢ Y).
    assert (count (PR s1) sX = count (PR s) sX - 1) as HsXs1s.
    { rewrite Heqss0. simpl. rewrite PR_tostar_eq; try assumption.
      simpl swsc. simpl app. rewrite ! count_cons_eq; reflexivity. }
    destruct (IHm s1) as [s2 Hders2 [HsXs2 Hs2]]; try lia.
    assert (PR s1 ⫅ PR s) as Hincs1s.
    { eapply (mset_incl_tran _ (PR s0)).
      simpl. rewrite <- app_assoc.
      apply mset_incl_appr, mset_incl_refl.
      apply mset_eq_incl, mset_eq_sym. assumption. }
    exists s2. eapply (DerivRulePseq_tran _ _ _ [s1]).
    constructor; try constructor.
    eapply (DerivRulePseq_tran _ _ _ [s0]).
    constructor; try constructor.
    eapply DerivRulePseq_imp; try eassumption.
    intros u Hu. apply mset_eq_incl. assumption.
    unshelve eexists. confirm_derr (Der s1 Contl [Unf s0]).
    simpl.
    change (strPR true (tostar sX) ++ strPR true Y) with (PR s1).
    change ((strPR true (tostar sX) ++ strPR true (tostar sX)) ++ strPR true Y) with (PR s0).
    split; try assumption. split; try tauto.
    apply mset_eq_incl, mset_eq_sym. assumption.
    eapply DerivRulePseq_imp; try eassumption.
    intros u Hu. eapply mset_incl_tran; try eassumption. assumption.
    split; try assumption.
    intros sZ Hneq.
    eapply eq_trans; try apply Hs2; try assumption.
    eapply eq_trans; try apply Heqss0.
    simpl. rewrite PR_tostar_eq; try assumption.
    simpl swsc. simpl app. apply not_eq_sym in Hneq.
    rewrite ! count_cons_neq; tauto.
Defined.
    

Lemma contraction_phase' (s t : sequent) :
  PR s ⊆ PR t -> forall l, l ⊆ PR t ->
    {s' & DerivRulePseq MDEICW (fun u => PR u ⫅ PR s \/ PR u ⫅ PR t) ([s], s') &
       forall sX, sX ∈ l -> count (PR s') sX <= count (PR t) sX}.
Proof.
  intros Hincst l Hinct. induction l as [|sX l].
  - exists s. unshelve eexists. confirm_derr (Unf s).
    simpl. left. apply mset_incl_refl.
    intros. contradiction.
  - destruct IHl as [s0 Hders0 Hs0].
    eapply incl_tran; try eassumption.
    apply incl_tl, incl_refl.
    assert (sX ∈ PR t) as HinsXt.
    { apply Hinct. now left. }
    pose proof (seqPR_isPrim _ HinsXt) as HprsX.
    pose proof HinsXt as HcsXt.
    apply count_In in HcsXt.
    destruct (le_gt_dec (count (PR s0) sX) (count (PR t) sX)) as [HsXle|HsXgt].
    + exists s0. assumption.
      intros sY HsY. destruct HsY as [HsY|HsY].
      * rewrite <- HsY. assumption.
      * apply Hs0. assumption.
    + destruct (le_lt_eq_dec _ _ HcsXt) as [HcsXtlt|HcsXteq].
      * destruct (repeat_conts s0 sX (count (PR t) sX) HcsXtlt)
          as [s1 Hders1 [Hs1t Hs0s1]]; try lia.
        exists s1. eapply DerivRulePseq_tran.
        constructor 2; try constructor 1.
        eassumption.
        eapply DerivRulePseq_imp; try eassumption.
        intros u Hu.
        destruct (DerivRulePseq_Proot _ Hders0).
       -- left. eapply mset_incl_tran; try eassumption. assumption.
       -- right. eapply mset_incl_tran; try eassumption. assumption.
       -- intros sY HsY. destruct (eqdec sY sX) as [Heq|Hneq].
         ++ rewrite Heq. rewrite Hs1t. apply le_n.
         ++ destruct HsY as [HsY|HsY]; try (apply eq_sym in HsY; contradiction).
            rewrite <- Hs0s1; try assumption. apply Hs0. assumption.
      * rewrite <- HcsXteq in HsXgt.
        assert (PR s0 ⫅ PR s) as Hincs0s.
        { destruct (DerivRulePseq_Proot _ Hders0) as [H|H];
            try assumption.
          specialize (H sX). lia. }
        destruct (repeat_conts s0 sX 2 (le_n 2) HsXgt)
          as [s1 Hders1 [Hs1t Hs0s1]]; try lia.
        set (lX := listerase (PR s1) [sX; sX]).
        destruct (length lX) eqn:HlenlX.
       -- destruct (count_ltlen_ex sX (PR t)) as [sZ [HneqsZ HinsZ]].
          rewrite <- HcsXteq. apply nb_seqPR_ge2. 
          assert ([sZ; sX] ⫅ PR t) as HincZXt.
          { intro sW.
            destruct (eqdec sW sZ) as [HeqZ|HneqZ];
             [idtac | destruct (eqdec sW sX) as [HeqX|HneqX]].
            - rewrite HeqZ.
              rewrite count_cons_eq; try reflexivity.
              rewrite count_cons_neq; try now apply not_eq_sym.
              simpl. rewrite count_In in HinsZ. lia.
            - rewrite HeqX.
              rewrite count_cons_neq; try assumption.
              rewrite count_cons_eq; try reflexivity.
              simpl. assumption.
            - rewrite count_cons_neq; try now apply not_eq_sym.
              rewrite count_cons_neq; try now apply not_eq_sym.
              simpl. apply Nat.le_0_l. }
          pose proof HlenlX as HlXnil.
          apply length_zero_iff_nil in HlXnil.
          set (s2 := ∗ tostar sX ⊢ tostar sX).
          assert (PR s1 ≡ PR s2) as Heqs1s2.
          { simpl. rewrite PR_tostar_eq; try assumption.
            simpl. apply listerase_nil_mset_eq; try assumption. 
            intro sW. destruct (eqdec sW sX) as [Heq|Hneq].
            - rewrite Heq. rewrite ! count_cons_eq; try reflexivity.
              rewrite Hs1t. apply le_n.
            - rewrite ! count_cons_neq; try now apply not_eq_sym.
              simpl. apply Nat.le_0_l. }
          pose proof (mset_eq_PR_Deriv s1 s2 Heqs1s2) as Hders2.
          pose proof (seqPR_isPrim _ HinsZ) as HprsZ.
          set (s3 := ∗ tostar sZ ⊢ tostar sX).
          exists s3. eapply DerivRulePseq_tran.
          constructor 2; try constructor 1. eassumption.
          eapply DerivRulePseq_tran.
          constructor 2; try constructor 1.
          eapply DerivRulePseq_imp; try eassumption.
          intros u Hu. left. simpl in Hu.
          eapply mset_incl_tran; eassumption.
          eapply DerivRulePseq_tran.
          constructor 2; try constructor 1.
          eapply DerivRulePseq_imp; try eassumption.
          intros u Hu. simpl in Hu. left.
          eapply mset_incl_tran; try eassumption.
          eapply mset_incl_tran. apply mset_eq_incl. eassumption.
          apply (DerivRulePseq_Proot _ Hders1).
          unshelve eexists.
          confirm_derr (Der s3 ContWkls [Unf s2]).
          simpl. rewrite ! PR_tostar_eq; try assumption.
          simpl. split; try split; try tauto.
        ++ left. intro sW. simpl.
           destruct (sstructr_eq_dec (id sX) sW) as [Heq|Hneq];
             try rewrite <- Heq; try lia.
           eapply Nat.le_trans; try apply Hincs0s. unfold id. lia.
        ++ intros sW HsW. simpl. rewrite ! PR_tostar_eq; try assumption.
           simpl swsc. simpl app. apply HincZXt.
      -- destruct (exact_rep_PR lX true) as [Y HY].
         { intro Hnil. apply length_zero_iff_nil in Hnil. lia. }
         { eapply incl_Forall; try apply listerase_incl.
           apply Forall_forall. apply seqPR_isPrim. }
         set (s2 := ∗ tostar sX,, ∗ tostar sX ⊢ Y).
         assert (PR s1 ≡ PR s2) as Heqs1s2.
         { simpl. rewrite PR_tostar_eq; try assumption.
           simpl swsc. change (([id sX] ++ [id sX])%list) with [sX; sX].
           eapply mset_eq_tran; try apply mset_eq_app_comm.
           eapply mset_eq_tran; try apply mset_eq_app_app;
             try (apply mset_eq_sym; rewrite HY); try apply mset_eq_refl.
           apply mset_eq_sym, listerase_app_mset_eq.
           intro sZ. simpl.
           destruct (sstructr_eq_dec sX sZ) as [Heq|Hneq];
             try rewrite <- Heq; lia. }
         pose proof (mset_eq_PR_Deriv s1 s2 Heqs1s2) as Hders2.
         set (s3 := ∗ tostar sX ⊢ Y).
         pose proof (DerivRulePseq_Proot _ Hders1) as Hincs1s0.
         simpl in Hincs1s0.
         pose proof (mset_incl_tran _ _ _ Hincs1s0 Hincs0s) as Hincs1s.
         pose proof (proj1 (mset_eq_incl_l _ _ _ Heqs1s2) Hincs1s0) as Hincs2s0.
         pose proof (proj1 (mset_eq_incl_l _ _ _ Heqs1s2) Hincs1s) as Hincs2s.
         assert (PR s3 ⫅ PR s0) as Hincs3s0.
         { eapply mset_incl_tran; try apply Hincs2s0.
           simpl. rewrite <- app_assoc.
           apply mset_incl_appr, mset_incl_refl. }
         pose proof (mset_incl_tran _ _ _ Hincs3s0 Hincs0s) as Hincs3s.
         exists s3. eapply DerivRulePseq_tran.
         constructor 2; try constructor 1. eassumption.
         eapply DerivRulePseq_tran.
         constructor 2; try constructor 1.
         eapply DerivRulePseq_imp; try eassumption.
         intros u Hu. simpl in Hu. left.
         eapply mset_incl_tran; try eassumption.
         eapply DerivRulePseq_tran.
         constructor 2; try constructor 1.
         eapply DerivRulePseq_imp; try eassumption.
         intros u Hu. simpl in Hu. left.
         apply (mset_eq_incl_l _ _ _ Hu). assumption.
         unshelve eexists.
         confirm_derr (Der s3 Contl [Unf s2]).
         simpl. tauto.
         intros sW [HsW|HsW].
        ++ rewrite <- HsW. simpl. rewrite <- HcsXteq.
           rewrite PR_tostar_eq; try assumption.
           simpl app. rewrite count_cons_eq; try reflexivity.
           rewrite HY. unfold lX. rewrite count_listerase.
           rewrite Hs1t.
           rewrite ! count_cons_eq; reflexivity.
        ++ eapply Nat.le_trans; try apply Hs0; try assumption.
           apply Hincs3s0.
Defined.


Lemma contraction_phase'' (s t : sequent) :
  PR s ⊆ PR t ->
    {s' & DerivRulePseq MDEICW (fun u => PR u ⫅ PR s \/ PR u ⫅ PR t) ([s], s') &
       PR s' ⫅ PR t}.
Proof.
  intro Hincst.
  destruct (contraction_phase' s t Hincst (PR t) (incl_refl _)) as [s' Hders' Hs'].
  exists s'. assumption.
  pose proof (DerivRulePseq_Proot _ Hders') as HP.
  destruct HP as [HP|HP]; try assumption.
  intro sX. destruct (in_dec sstructr_eq_dec sX (PR t)) as [Hint|Hnint].
  - apply Hs'. assumption.
  - pose proof Hnint as Hnins'.
    apply (contra_not (Hincst sX)) in Hnins'.
    apply (contra_not (mset_incl_incl _ _ HP sX)) in Hnins'.
    apply count_not_In in Hnint, Hnins'.
    rewrite Hnint, Hnins'. apply le_n.
Defined.

Lemma contraction_phase (s t : sequent) :
  PR s ⊆ PR t ->
    {s' & deriv_rule_P MDEICW (fun u => PR u ⫅ PR s \/ PR u ⫅ PR t) ([s], s') &
       PR s' ⫅ PR t}.
Proof.
  intro H. destruct (contraction_phase'' _ _ H) as [s' Hs' Hs'0].
  exists s'; try assumption. apply DerivRulePseq_iff_deriv_rule_P. assumption.
Defined.


Lemma weakening_phase (s t : sequent) :
  PR s ⫅ PR t ->
       {s' & deriv_rule_P MDEICW (fun u => PR u ⫅ PR t) ([s], s') & PR s' ≡ PR t}.
Proof.
  intro Hminc. set (l := listerase (PR t) (PR s)).
  destruct (eqdec l []) as [Heq|Hneq].
  - apply listerase_nil_mset_eq in Heq; try assumption.
    exists s; try assumption. apply deriv_prseq_P_refl; try assumption.
    apply mset_eq_sym. assumption.
  - pose proof (listerase_app_mset_eq _ _ Hminc) as Hmeq.
    destruct (exact_rep_PR l true) as [Z HPRZ]; try assumption.
    eapply incl_Forall. apply listerase_incl.
    apply Forall_forall, seqPR_isPrim.
    destruct s as [X Y].
    assert (PR (X ⊢ Y,, Z) ≡ PR t) as HPReq.
    { eapply mset_eq_tran; try eassumption.
      simpl. eapply mset_eq_tran. rewrite app_assoc.
      apply mset_eq_app_comm.
      apply mset_eq_app_app; [assumption | apply mset_eq_refl]. }
    exists (X ⊢ Y,, Z).
    + apply (deriv_prseq_P_ext _ _ _ [X ⊢ Y] _ Wkr).
      * auto_in.
      * auto_ruleInst.
      * apply mset_eq_incl. assumption.
      * constructor; [|constructor]. apply deriv_prseq_P_refl.
        assumption.
    + assumption.
Defined.


Theorem incl_PR_deriv (s t : sequent) :
  PR s ⊆ PR t ->
    deriv_rule_P MDEICW
      (fun u => PR u ⫅ PR s \/ PR u ⫅ PR t \/ length (PR u) = 2) ([s], t).
Proof.
  intro Hincst.
  destruct (contraction_phase s t Hincst) as [s0 Hder0 Hincs0].
  destruct (weakening_phase s0 t Hincs0) as [s1 Hder1 Hmeqs1t].
  pose proof (mset_eq_PR_deriv s1 t Hmeqs1t) as Hdert.
  eapply deriv_prseq_P_tran.
  2:{
  eapply deriv_prseq_P_imp; try eassumption.
  intros u Hu. simpl in Hu. right. left.
  eapply mset_incl_tran. all: try apply mset_eq_incl.
  eassumption. assumption. }
  apply deriv_prseqs_P_cons; [|apply deriv_prseqs_P_nil].
  eapply deriv_prseq_P_tran.
  2:{
  eapply deriv_prseq_P_imp; try eassumption.
  intros u Hu. simpl in Hu. tauto. }
  apply deriv_prseqs_P_cons; [|apply deriv_prseqs_P_nil].
  eapply deriv_prseq_P_imp; try eassumption.  
  intros u Hu. simpl in Hu. destruct Hu as [Hu|Hu]; try tauto.
Defined.

Theorem incl_PR_Deriv (s t : sequent) :
  PR s ⊆ PR t ->
    DerivRulePseq MDEICW
      (fun u => PR u ⫅ PR s \/ PR u ⫅ PR t \/ length (PR u) = 2) ([s], t).
Proof.
  intros. apply DerivRulePseq_iff_deriv_rule_P.
  apply incl_PR_deriv. assumption.
Defined.

Corollary SDR_incl_PR_Deriv_MDEICW (s t : sequent) :
  seqSemidreduced s -> seqSemidreduced t -> PR s ⊆ PR t -> DerivRuleSDR MDEICW ([s], t).
Proof.
  intros Hssps Hsspt Hincl. apply DerivRuleSDR_iff_deriv_rule_sdr.
  pose proof (incl_PR_deriv s t Hincl) as Hder.
  eapply deriv_prseq_P_imp; try eassumption.
  intros u Hu. destruct Hu as [Hu|[Hu|Hu]];
    try (eapply mset_incl_seqSemidreduced; eassumption).
  apply dreduced_semidreduced, len2_dreduced. assumption.
Defined.

Lemma MDEICW_incl_CPL_DC' : MDEICW ⊆ CPL_DC'.
Proof. unfold CPL_DC'. apply incl_appl, incl_refl. Qed.

Corollary SDR_incl_PR_Deriv (s t : sequent) :
  seqSemidreduced s -> seqSemidreduced t -> PR s ⊆ PR t -> DerivRuleSDR CPL_DC' ([s], t).
Proof.
  intros. apply DerivRuleSDR_iff_deriv_rule_sdr.
  apply (deriv_rule_P_incl_DC _ MDEICW).
  apply MDEICW_incl_CPL_DC'. apply DerivRuleSDR_iff_deriv_rule_sdr.
  apply SDR_incl_PR_Deriv_MDEICW; assumption.
Defined.

Corollary SDR_incl_PR_deriv (s t : sequent) :
  seqSemidreduced s -> seqSemidreduced t -> PR s ⊆ PR t -> deriv_rule_sdr CPL_DC' ([s], t).
Proof.
  intros. apply DerivRuleSDR_iff_deriv_rule_sdr.
  apply SDR_incl_PR_Deriv; assumption.
Defined.


Corollary set_eq_PR_Deriv_MDEICW : forall s s', PR s ≃ PR s' -> DerivRule MDEICW ([s], s').
Proof.
  intros s t HeqPR. apply incl_PR_Deriv.
  apply set_eq_incl. assumption.
Defined.


Corollary set_eq_PR_Deriv : forall s s', PR s ≃ PR s' -> DerivRule CPL_DC' ([s], s').
Proof.
  intros.  apply (SubDC_SubDer MDEICW). apply MDEICW_incl_CPL_DC'.
  apply set_eq_PR_Deriv_MDEICW; assumption.
Defined.


Ltac prep_DRRSDR :=
  let rs := fresh "ri" in let Hinst := fresh "Hinst" in
  let afs := fresh "afs" in let Heqri := fresh "Heqri" in
  constructor; intros ri Hinst; apply ruleInst_ruleSubst in Hinst;
  destruct Hinst as [afs Heqri]; simpl in Heqri; rewrite Heqri; simpl.



(* LOGICAL RULES *)

(* ¬ *)

#[export] Instance DerivRuleReducSDR_Negl : DerivRuleReducSDR CPL_DC' Negl.
Proof.
  prep_DRRSDR. set (X := snd afs "X").
  set (A := snd (fst afs) "A").
  destruct (NoDup_rep_PR (strPR true X) true)
    as [X' [HPRX' HNDX']].
  apply strPR_not_nil.
  apply Forall_forall. intros sX HsX.
  apply (PR_isPrim _ _ HsX).

  assert (seqSemidreduced (∗£A ⊢ X')) as Hssp0. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (true, £A).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  assert (seqSemidreduced (£ ¬ A ⊢ X')) as Hssp1. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (false, £ ¬ A).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  apply (DerivRuleSDR_tran _ _ [∗ £A ⊢ X']).
  constructor; try constructor.
  apply SDR_incl_PR_Deriv; try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_cons_cons, set_eq_incl, set_eq_sym. assumption.
  
  apply (DerivRuleSDR_tran _ _ [£ ¬ A ⊢ X']).
  constructor; try constructor.
  set (d := Der (£¬A ⊢ X') Negl [Unf (∗£A ⊢ X')]).
  unshelve eexists. confirm_derr d.
  unfold dtSemidreduced. simpl. tauto.

  apply SDR_incl_PR_Deriv; try assumption. apply seq_semidreduced_reduc.
  eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_cons_cons, set_eq_incl. assumption.
Defined.


#[export] Instance DerivRuleReducSDR_Negr : DerivRuleReducSDR CPL_DC' Negr.
Proof.
  prep_DRRSDR. set (X := snd afs "X").
  set (A := snd (fst afs) "A").
  destruct (NoDup_rep_PR (strPR false X) false)
    as [X' [HPRX' HNDX']].
  apply strPR_not_nil.
  apply Forall_forall. intros sX HsX.
  apply (PR_isPrim _ _ HsX).

  assert (seqSemidreduced (X' ⊢ ∗£A)) as Hssp0. {
  unfold seqSemidreduced. simpl. eapply mset_eq_semidreduced;
    try (apply mset_eq_app_comm).
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' false)) as [Hlengt1|Hleneq1].
  apply erase_semidreduced with (false, £A). simpl. lia.
  unfold app. rewrite erase_cons_eq.
  apply ge2_NoDup_dreduced; try lia; try assumption.
  apply dreduced_semidreduced, len2_dreduced. simpl. rewrite Hleneq1. reflexivity. }

  assert (seqSemidreduced (X' ⊢ £ ¬ A)) as Hssp1. {
  unfold seqSemidreduced. simpl. eapply mset_eq_semidreduced;
    try (apply mset_eq_app_comm).
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' false)) as [Hlengt1|Hleneq1].
  apply erase_semidreduced with (true, £¬A). simpl. lia.
  unfold app. rewrite erase_cons_eq.
  apply ge2_NoDup_dreduced; try lia; try assumption.
  apply dreduced_semidreduced, len2_dreduced. simpl. rewrite Hleneq1. reflexivity. }

  apply (DerivRuleSDR_tran _ _ [X' ⊢ ∗ £A]).
  constructor; try constructor.
  apply SDR_incl_PR_Deriv; try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_app_app.
  apply set_eq_incl, set_eq_sym. assumption.
  apply incl_refl.
  
  apply (DerivRuleSDR_tran _ _ [X' ⊢ £ ¬ A]).
  constructor; try constructor.
  set (d := Der (X' ⊢ £¬A) Negr [Unf (X' ⊢ ∗£A)]).
  unshelve eexists. confirm_derr d.
  unfold dtSemidreduced. simpl. tauto.

  apply SDR_incl_PR_Deriv; try assumption. apply seq_semidreduced_reduc.
  eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_app_app. apply set_eq_incl. assumption.
  apply incl_refl.
Defined.


(* ∧ *)

#[export] Instance DerivRuleReducSDR_Conl : DerivRuleReducSDR CPL_DC' Conl.
Proof.
  prep_DRRSDR. set (X := snd afs "X").
  set (A := snd (fst afs) "A"). set (B := snd (fst afs) "B").
  destruct (eqdec (listminus (strPR true X) [(false, £A); (false, £B)]) []) as [Heq|Hneq].
  1:{
  assert (seqSemidreduced (£A,, £B ⊢ I)) as Hssp0. {
  unfold seqSemidreduced. simpl.
  apply erase_semidreduced with (false, £A); [simpl; lia |].
  simpl PR. rewrite erase_cons_eq.
  apply ge2_NoDup_dreduced; simpl; try lia. NoDup_two. }
  assert (seqSemidreduced (£ A ∧ B ⊢ I)) as Hssp1. {
  unfold seqSemidreduced. simpl.
  apply dreduced_semidreduced.
  apply ge2_NoDup_dreduced; simpl; try lia. NoDup_two. }
  assert (seqSemidreduced (£ A ∧ B ⊢ I,, ∗ £ A ∧ B)) as Hssp2. {
  unfold seqSemidreduced. simpl.
  apply erase_semidreduced with (false, £ A ∧ B); [simpl; lia |].
  rewrite erase_cons_eq. apply ge2_NoDup_dreduced; simpl; try lia. NoDup_two. }
  assert (seqSemidreduced (£ A ∧ B ⊢ ∗ £ A ∧ B)) as Hssp3. {
  unfold seqSemidreduced. simpl.
  apply dreduced_semidreduced. apply len2_dreduced. simpl. lia. }

  pose proof (listminus_empty _ _ Heq) as Hinc.
  apply DerivRuleSDR_iff_deriv_rule_sdr.
  apply (deriv_prseq_P_tran _ _ _ [£A,, £B ⊢ I]).
  - constructor; [|constructor].
    apply SDR_incl_PR_deriv;
      [apply seq_semidreduced_reduc | assumption |].
    eapply set_eq_incl_l. apply reduc_PR_set_eq.
    simpl. apply incl_cons; [now left|].
    apply incl_cons; [now (right; left)|].
    eapply incl_tran; try eassumption. auto_incl.
  - apply (deriv_prseq_P_tran _ _ _ [£ A ∧ B ⊢ ∗ £ A ∧ B]).
    + constructor; [|constructor].
      apply DerivRulePseq_iff_deriv_prseq_P.
      set (d := Der (£ A ∧ B ⊢ ∗ £ A ∧ B) Idelr
               [Der (£ A ∧ B ⊢ I,, ∗ £ A ∧ B) Wkr
               [Der (£ (A ∧ B) ⊢ I) Conl
               [Unf (£ A,, £B ⊢ I)]]]).
      unshelve eexists. confirm_derr d.
      simpl. tauto.
    + apply SDR_incl_PR_deriv;
        [assumption | apply seq_semidreduced_reduc |].
      eapply set_eq_incl_r. apply reduc_PR_set_eq.
      simpl. eapply incl_tran; [|apply incl_cons_cons, incl_nil_l].
      auto_incl.
  }

  destruct (NoDup_rep_PR (listminus (strPR true X) [(false, £A); (false, £B)]) true)
    as [X' [HPRX' HNDX']]; try apply Forall_forall; try assumption.
  intros sX Hin. apply incl_listminus in Hin. apply (PR_isPrim _ _ Hin).

  assert (seqSemidreduced (£A,, £B ⊢ X')) as Hssp0. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (false, £A).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced; simpl; try lia.
      constructor; try assumption.
      unfold sstructr in *.
      rewrite (HPRX' (false, £B)).
      apply not_in_listminus. right. now left.
  - apply len3_semidreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  assert (seqSemidreduced (£(A ∧ B) ⊢ X')) as Hssp1. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (false, £(A ∧ B)).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  apply (DerivRuleSDR_tran _ _ [£ A,, £ B ⊢ X']).
  constructor; try constructor.
  apply SDR_incl_PR_Deriv; try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. change ((false, £ A) :: (false, £ B) :: strPR true X)
    with ([(false, £ A); (false, £ B)] ++ strPR true X).
  change ((false, £ A) :: (false, £ B) :: strPR true X')
    with ([(false, £ A); (false, £ B)] ++ strPR true X').
  eapply set_eq_incl_r. apply set_eq_app_Comm.
  eapply set_eq_incl_l. apply set_eq_app_Comm.
  eapply set_eq_incl_r. apply set_eq_app_app. eassumption. apply set_eq_refl.
  eapply set_eq_incl_r. apply listminus_recover.
  apply incl_refl.

  apply (DerivRuleSDR_tran _ _ [£(A ∧ B) ⊢ X']).
  constructor; try constructor.
  set (d := Der (£ (A ∧ B) ⊢ X') Conl [Unf (£ A,, £B ⊢ X')]).
  unshelve eexists. confirm_derr d.
  unfold dtSemidreduced. simpl. tauto.
  
  apply SDR_incl_PR_Deriv; try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_cons_cons.
  eapply set_eq_incl_l; try eassumption.
  apply incl_listminus.
Defined.



#[export] Instance DerivRuleReducSDR_Consr : DerivRuleReducSDR CPL_DC' Consr.
Proof.
  prep_DRRSDR. set (X := snd afs "X").
  set (A := snd (fst afs) "A"). set (B := snd (fst afs) "B").
  destruct (NoDup_rep_PR (strPR false X) false)
    as [X' [HPRX' HNDX']]; try (apply Forall_forall; intros sX HsX).
  apply strPR_not_nil. apply (PR_isPrim _ _ HsX).

  assert (seqSemidreduced (X' ⊢ £A)) as Hssp0. {
  unfold seqSemidreduced. simpl.
  eapply mset_eq_semidreduced. apply mset_eq_app_Comm. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' false)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (true, £A).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  assert (seqSemidreduced (X' ⊢ £B)) as Hssp1. {
  unfold seqSemidreduced. simpl.
  eapply mset_eq_semidreduced. apply mset_eq_app_Comm. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' false)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (true, £B).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  assert (seqSemidreduced (X' ⊢ £(A ∧ B))) as Hssp2. {
  unfold seqSemidreduced. simpl.
  eapply mset_eq_semidreduced. apply mset_eq_app_Comm. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' false)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (true, £(A ∧ B)).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  eapply DerivRuleSDR_tran. constructor 2; [idtac | constructor 2; [idtac | constructor 1]].
  { eapply (DerivRuleSDR_incl _ [reduc (X ⊢ £A)]); try auto_incl.
  apply (SDR_incl_PR_Deriv (reduc (X ⊢ £A)) (X' ⊢ £A)); try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_app_app; try apply incl_refl.
  apply set_eq_incl, set_eq_sym. assumption. }
  { eapply (DerivRuleSDR_incl _ [reduc (X ⊢ £B)]); try auto_incl.
  apply (SDR_incl_PR_Deriv (reduc (X ⊢ £B)) (X' ⊢ £B)); try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_app_app; try apply incl_refl.
  apply set_eq_incl, set_eq_sym. assumption. }

  apply (DerivRuleSDR_tran _ _ [X' ⊢ £(A ∧ B)]).
  constructor; try constructor.
  set (d := Der (X' ⊢ £ (A ∧ B)) Consr [Unf (X' ⊢ £ A); Unf (X' ⊢ £ B)]).
  unshelve eexists. confirm_derr d.
  unfold dtSemidreduced. simpl. tauto.

  apply SDR_incl_PR_Deriv; try assumption. apply seq_semidreduced_reduc.
  eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_app_app; try apply incl_refl. apply set_eq_incl. assumption.
Defined.


(* ∨ *)


#[export] Instance DerivRuleReducSDR_Dissl : DerivRuleReducSDR CPL_DC' Dissl.
Proof.
  prep_DRRSDR. set (X := snd afs "X").
  set (A := snd (fst afs) "A"). set (B := snd (fst afs) "B").
  destruct (NoDup_rep_PR (strPR true X) true)
    as [X' [HPRX' HNDX']]; try (apply Forall_forall; intros sX HsX).
  apply strPR_not_nil. apply (PR_isPrim _ _ HsX).

  assert (seqSemidreduced (£A ⊢ X')) as Hssp0. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (false, £A).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  assert (seqSemidreduced (£B ⊢ X')) as Hssp1. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (false, £B).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  assert (seqSemidreduced (£(A ∨ B) ⊢ X')) as Hssp2. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (false, £(A ∨ B)).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  eapply DerivRuleSDR_tran. constructor 2; [idtac | constructor 2; [idtac | constructor 1]].
  { eapply (DerivRuleSDR_incl _ [reduc (£A ⊢ X)]); try auto_incl.
  apply (SDR_incl_PR_Deriv (reduc (£A ⊢ X)) (£A ⊢ X')); try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_cons_cons, set_eq_incl, set_eq_sym. assumption. }
  { eapply (DerivRuleSDR_incl _ [reduc (£B ⊢ X)]); try auto_incl.
  apply (SDR_incl_PR_Deriv (reduc (£B ⊢ X)) (£B ⊢ X')); try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_cons_cons, set_eq_incl, set_eq_sym. assumption. }

  apply (DerivRuleSDR_tran _ _ [£(A ∨ B) ⊢ X']).
  constructor; try constructor.
  set (d := Der (£ (A ∨ B) ⊢ X') Dissl [Unf (£ A ⊢ X'); Unf (£ B ⊢ X')]).
  unshelve eexists. confirm_derr d.
  unfold dtSemidreduced. simpl. tauto.

  apply SDR_incl_PR_Deriv; try assumption. apply seq_semidreduced_reduc.
  eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_cons_cons, set_eq_incl. assumption.
Defined.


#[export] Instance DerivRuleReducSDR_Disr : DerivRuleReducSDR CPL_DC' Disr.
Proof.
  prep_DRRSDR. set (X := snd afs "X").
  set (A := snd (fst afs) "A"). set (B := snd (fst afs) "B").

  destruct (eqdec (listminus (strPR false X) [(true, £A); (true, £B)]) []) as [Heq|Hneq].
  1:{
  assert (seqSemidreduced (I ⊢ £A,, £B)) as Hssp0. {
  unfold seqSemidreduced. simpl.
  apply erase_semidreduced with (true, £A); [simpl; lia |].
  rewrite erase_cons_neq; try discriminate.
  rewrite erase_cons_eq. apply ge2_NoDup_dreduced; simpl; try lia. NoDup_two. }
  assert (seqSemidreduced (I ⊢ £ A ∨ B)) as Hssp1. {
  unfold seqSemidreduced. simpl.
  apply dreduced_semidreduced.
  apply ge2_NoDup_dreduced; simpl; try lia. NoDup_two. }
  assert (seqSemidreduced (∗ £ A ∨ B,, I ⊢ £ A ∨ B)) as Hssp2. {
  unfold seqSemidreduced. simpl.
  apply erase_semidreduced with (true, £ A ∨ B); [simpl; lia |].
  rewrite erase_cons_eq. apply ge2_NoDup_dreduced; simpl; try lia. NoDup_two. }
  assert (seqSemidreduced (∗ £ A ∨ B ⊢ £ A ∨ B)) as Hssp3. {
  unfold seqSemidreduced. simpl.
  apply dreduced_semidreduced. apply len2_dreduced. simpl. lia. }

  pose proof (listminus_empty _ _ Heq) as Hinc.
  apply DerivRuleSDR_iff_deriv_rule_sdr.
  apply (deriv_prseq_P_tran _ _ _ [I ⊢ £A,, £B]).
  - constructor; [|constructor].
    apply SDR_incl_PR_deriv;
      [apply seq_semidreduced_reduc | assumption |].
    eapply set_eq_incl_l. apply reduc_PR_set_eq.
    simpl. apply incl_tl, incl_app; [assumption | apply incl_refl].
  - apply (deriv_prseq_P_tran _ _ _ [∗ £ A ∨ B ⊢ £ A ∨ B]).
    + constructor; [|constructor].
      apply DerivRulePseq_iff_deriv_prseq_P.
      set (d := Der (∗ £ A ∨ B ⊢ £ A ∨ B) Idell
               [Der (∗ £ A ∨ B,, I ⊢ £ A ∨ B) Wkl
               [Der (I ⊢ £ A ∨ B) Disr
               [Unf (I ⊢ £A,, £B)]]]).
      unshelve eexists. confirm_derr d.
      simpl. tauto.
    + apply SDR_incl_PR_deriv;
        [assumption | apply seq_semidreduced_reduc |].
      eapply set_eq_incl_r. apply reduc_PR_set_eq.
      simpl. apply incl_appr. auto_incl.
  }

  destruct (NoDup_rep_PR (listminus (strPR false X) ([(true, £A); (true, £B)])) false)
    as [X' [HPRX' HNDX']]; try apply Forall_forall; try assumption.
  intros sX Hin. apply incl_listminus in Hin. apply (PR_isPrim _ _ Hin).

  assert (seqSemidreduced (X' ⊢ £A,, £B)) as Hssp0. {
  unfold seqSemidreduced. simpl.
  eapply mset_eq_semidreduced. apply mset_eq_app_Comm. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' false)) as [Hlengt1|Hleneq1].
  apply erase_semidreduced with (true, £A).
  - simpl. lia.
  - rewrite erase_cons_eq. apply ge2_NoDup_dreduced; simpl; try lia.
      constructor; try assumption.
      unfold sstructr in *.
      rewrite (HPRX' (true, £B)).
      apply not_in_listminus. right. now left.
  - apply len3_semidreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  assert (seqSemidreduced (X' ⊢ £(A ∨ B))) as Hssp1. {
  unfold seqSemidreduced. simpl. eapply mset_eq_semidreduced;
    try (apply mset_eq_app_comm).
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' false)) as [Hlengt1|Hleneq1].
  apply erase_semidreduced with (true, £(A ∨ B)). simpl. lia.
  unfold app. rewrite erase_cons_eq.
  apply ge2_NoDup_dreduced; try lia; try assumption.
  apply dreduced_semidreduced, len2_dreduced. simpl. rewrite Hleneq1. reflexivity. }

  eapply DerivRuleSDR_tran. constructor 2; try constructor 1.
  apply (SDR_incl_PR_Deriv _ (X' ⊢ £A,, £B)).
  apply seq_semidreduced_reduc. assumption.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. repeat rewrite <- app_assoc. simpl.
  eapply set_eq_incl_r.
  eapply set_eq_tran;
    [apply set_eq_app_app; [eassumption | apply set_eq_refl] |
     apply listminus_recover].
  apply incl_refl.

  apply (DerivRuleSDR_tran _ _ [X' ⊢ £(A ∨ B)]).
  constructor; try constructor.
  set (d := Der (X' ⊢ £(A ∨ B)) Disr [Unf (X' ⊢ £A,, £B)]).
  unshelve eexists. confirm_derr d.
  unfold dtSemidreduced. simpl. tauto.
  
  apply SDR_incl_PR_Deriv; try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_app_app; try apply incl_refl.
  eapply set_eq_incl_l; try eassumption.
  apply incl_listminus.
Defined.


#[export] Instance DerivRuleReducSDR_Impr : DerivRuleReducSDR CPL_DC' Impr.
Proof.
  prep_DRRSDR. set (X := snd afs "X").
  set (A := snd (fst afs) "A"). set (B := snd (fst afs) "B").

  destruct (eqdec (listminus (strPR false X) [(false, £A); (true, £B)]) []) as [Heq|Hneq].
  1:{
  assert (seqSemidreduced (I,, £A ⊢ £B)) as Hssp0. {
  unfold seqSemidreduced. simpl.
  apply erase_semidreduced with (false, £A); [simpl; lia |].
  rewrite erase_cons_neq; try discriminate.
  rewrite erase_cons_eq. apply ge2_NoDup_dreduced; simpl; try lia. NoDup_two. }
  assert (seqSemidreduced (I ⊢ £ A → B)) as Hssp1. {
  unfold seqSemidreduced. simpl.
  apply dreduced_semidreduced.
  apply ge2_NoDup_dreduced; simpl; try lia. NoDup_two. }
  assert (seqSemidreduced (∗ £ A → B,, I ⊢ £ A → B)) as Hssp2. {
  unfold seqSemidreduced. simpl.
  apply erase_semidreduced with (true, £ A → B); [simpl; lia |].
  rewrite erase_cons_eq. apply ge2_NoDup_dreduced; simpl; try lia. NoDup_two. }
  assert (seqSemidreduced (∗ £ A → B ⊢ £ A → B)) as Hssp3. {
  unfold seqSemidreduced. simpl.
  apply dreduced_semidreduced. apply len2_dreduced. simpl. lia. }

  pose proof (listminus_empty _ _ Heq) as Hinc.
  apply DerivRuleSDR_iff_deriv_rule_sdr.
  apply (deriv_prseq_P_tran _ _ _ [I,, £A ⊢ £B]).
  - constructor; [|constructor].
    apply SDR_incl_PR_deriv;
      [apply seq_semidreduced_reduc | assumption |].
    eapply set_eq_incl_l. apply reduc_PR_set_eq.
    simpl. apply incl_tl, incl_app; [apply incl_app; [assumption|] |]; auto_incl.
  - apply (deriv_prseq_P_tran _ _ _ [∗ £ A → B ⊢ £ A → B]).
    + constructor; [|constructor].
      apply DerivRulePseq_iff_deriv_prseq_P.
      set (d := Der (∗ £ A → B ⊢ £ A → B) Idell
               [Der (∗ £ A → B,, I ⊢ £ A → B) Wkl
               [Der (I ⊢ £ A → B) Impr
               [Unf (I,, £A ⊢ £B)]]]).
      unshelve eexists. confirm_derr d.
      simpl. tauto.
    + apply SDR_incl_PR_deriv;
        [assumption | apply seq_semidreduced_reduc |].
      eapply set_eq_incl_r. apply reduc_PR_set_eq.
      simpl. apply incl_appr. auto_incl.
  }


  destruct (NoDup_rep_PR (listminus (strPR false X) ([(false, £A); (true, £B)])) false)
    as [X' [HPRX' HNDX']]; try apply Forall_forall; try assumption.
  intros sX Hin. apply incl_listminus in Hin. apply (PR_isPrim _ _ Hin).

  assert (seqSemidreduced (X',, £A ⊢ £B)) as Hssp0. {
  unfold seqSemidreduced. simpl.
  eapply mset_eq_semidreduced. apply mset_eq_app_Comm. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' false)) as [Hlengt1|Hleneq1].
  apply erase_semidreduced with (false, £A).
  - simpl. rewrite app_length. lia.
  - rewrite erase_cons_neq; try discriminate.
    rewrite erase_app_not_in_l.
    2:{ rewrite (HPRX' (false, £A)). apply not_in_listminus. now left. }
    rewrite erase_cons_eq. apply ge2_NoDup_dreduced; simpl;
      try rewrite app_length; try lia. rewrite app_nil_r.
    constructor; try assumption.
    unfold sstructr in *.
    rewrite (HPRX' (true, £B)).
    apply not_in_listminus. right. now left.
  - apply len3_semidreduced.
    simpl. rewrite app_length. rewrite <- Hleneq1. reflexivity. }

  assert (seqSemidreduced (X' ⊢ £(A → B))) as Hssp1. {
  unfold seqSemidreduced. simpl. eapply mset_eq_semidreduced;
    try (apply mset_eq_app_comm).
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' false)) as [Hlengt1|Hleneq1].
  apply erase_semidreduced with (true, £(A → B)). simpl. lia.
  unfold app. rewrite erase_cons_eq.
  apply ge2_NoDup_dreduced; try lia; try assumption.
  apply dreduced_semidreduced, len2_dreduced. simpl. rewrite Hleneq1. reflexivity. }

  eapply DerivRuleSDR_tran. constructor 2; try constructor 1.
  apply (SDR_incl_PR_Deriv _ (X',, £A ⊢ £B)).
  apply seq_semidreduced_reduc. assumption.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. repeat rewrite <- app_assoc. simpl.
  eapply set_eq_incl_r.
  eapply set_eq_tran;
    [apply set_eq_app_app; [eassumption | apply set_eq_refl] |
     apply listminus_recover].
  apply incl_refl.

  apply (DerivRuleSDR_tran _ _ [X' ⊢ £(A → B)]).
  constructor; try constructor.
  set (d := Der (X' ⊢ £(A → B)) Impr [Unf (X',, £A ⊢ £B)]).
  unshelve eexists. confirm_derr d.
  unfold dtSemidreduced. simpl. tauto.
  
  apply SDR_incl_PR_Deriv; try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_app_app; try apply incl_refl.
  eapply set_eq_incl_l; try eassumption.
  apply incl_listminus.
Defined.


#[export] Instance DerivRuleReducSDR_Impsl : DerivRuleReducSDR CPL_DC' Impsl.
Proof.
  prep_DRRSDR. set (X := snd afs "X").
  set (A := snd (fst afs) "A"). set (B := snd (fst afs) "B").
  destruct (NoDup_rep_PR (strPR true X) true)
    as [X' [HPRX' HNDX']]; try (apply Forall_forall; intros sX HsX).
  apply strPR_not_nil. apply (PR_isPrim _ _ HsX).

  assert (seqSemidreduced (∗£A ⊢ X')) as Hssp0. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (true, £A).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  assert (seqSemidreduced (£B ⊢ X')) as Hssp1. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (false, £B).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  assert (seqSemidreduced (£(A → B) ⊢ X')) as Hssp2. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 X' true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (false, £(A → B)).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  eapply DerivRuleSDR_tran. constructor 2; [idtac | constructor 2; [idtac | constructor 1]].
  { eapply (DerivRuleSDR_incl _ [reduc (∗£A ⊢ X)]); try auto_incl.
  apply (SDR_incl_PR_Deriv (reduc (∗£A ⊢ X)) (∗£A ⊢ X')); try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_cons_cons, set_eq_incl, set_eq_sym. assumption. }
  { eapply (DerivRuleSDR_incl _ [reduc (£B ⊢ X)]); try auto_incl.
  apply (SDR_incl_PR_Deriv (reduc (£B ⊢ X)) (£B ⊢ X')); try assumption.
  apply seq_semidreduced_reduc.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_cons_cons, set_eq_incl, set_eq_sym. assumption. }

  apply (DerivRuleSDR_tran _ _ [£(A → B) ⊢ X']).
  constructor; try constructor.
  set (d := Der (£ (A → B) ⊢ X') Impsl [Unf (∗ £ A ⊢ X'); Unf (£ B ⊢ X')]).
  unshelve eexists. confirm_derr d.
  unfold dtSemidreduced. simpl. tauto.

  apply SDR_incl_PR_Deriv; try assumption. apply seq_semidreduced_reduc.
  eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac].
  simpl. apply incl_cons_cons, set_eq_incl. assumption.
Defined.    


#[export] Instance DerivRuleReducSDR_Idell : DerivRuleReducSDR CPL_DC' Idell.
Proof.
  prep_DRRSDR. set (X := snd afs "X"). set (Y := snd afs "Y").
  destruct (NoDup_rep_PR (strPR true (∗ X,, Y)) true)
    as [Z [HPRZ HNDZ]]; try (apply Forall_forall; intros sX HsX).
  apply strPR_not_nil. apply (PR_isPrim _ _ HsX).

  assert (seqSemidreduced (I ⊢ Z)) as Hssp0. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 Z true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (false, I).
    + simpl. lia.
    + rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    simpl. rewrite <- Hleneq1. reflexivity. }

  pose proof (hdPR_isPrim Z true) as Hprhd.
  pose proof (@hdPR_in_PR Z true) as Hhdin.

  assert (seqSemidreduced (∗ tostar (hdPR true Z),, I ⊢ strDel Z (hdPR true Z))) as Hssp1. {
  unfold seqSemidreduced.
  assert (length (PR (∗ tostar (hdPR true Z),, I ⊢ strDel Z (hdPR true Z))) > 2) as Hlen.
  { simpl. rewrite ! app_length.
    pose proof (nb_PR_ge1 (tostar (hdPR true Z)) true).
    pose proof (nb_PR_ge1 (strDel Z (hdPR true Z)) true).
    simpl. lia. }
  apply erase_semidreduced with (false, I); try assumption.
  eapply mset_incl_dreduced.
  destruct (erase_In_length (PR (∗ tostar (hdPR true Z),, I ⊢ strDel Z (hdPR true Z)))
              (false, I)).
  simpl. apply in_app_iff. left. apply in_app_iff. right. now left.
  lia.
  apply (mset_incl_erase_erase _ (PR (I,, ∗ tostar (hdPR true Z) ⊢ strDel Z (hdPR true Z)))).
  simpl. apply mset_eq_incl. rewrite <- app_assoc.
  rewrite (app_singl_eq_cons (strPR true (tostar (hdPR true Z)) ++ strPR true (strDel Z (hdPR true Z)))  (false, I)).
  apply mset_eq_app_swap_app.
  simpl. rewrite PR_tostar_eq; try assumption.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 Z true)) as [Hlengt1|Hleneq1].
  - pose proof (strgt1_Comma _ _ Hlengt1) as HCZ.
    apply ge2_NoDup_dreduced.
    simpl.
    pose proof (strPR_niso_t Hhdin HCZ) as Hnisohd.
    pose proof (niso_strDel_length _ _ true Hprhd Hnisohd) as Hlen'.
    lia.
    eapply mset_eq_NoDup; try eassumption.
    apply mset_eq_PR_hdPR_t. assumption.
  - apply len2_dreduced. rewrite app_length.
    rewrite iso_PR_del. rewrite <- Hleneq1. reflexivity.
    apply eq_sym in Hleneq1. apply noComma_1prim_inv in Hleneq1.
    apply PR_iso; assumption. }

  assert (seqSemidreduced (∗ tostar (hdPR true Z) ⊢ strDel Z (hdPR true Z))) as Hssp2. {
  unfold seqSemidreduced.
  simpl. rewrite PR_tostar_eq; try assumption.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 Z true)) as [Hlengt1|Hleneq1].
  - pose proof (strgt1_Comma _ _ Hlengt1) as HCZ.
    apply dreduced_semidreduced, ge2_NoDup_dreduced.
    simpl.
    pose proof (strPR_niso_t Hhdin HCZ) as Hnisohd.
    pose proof (niso_strDel_length _ _ true Hprhd Hnisohd) as Hlen'.
    lia.
    eapply mset_eq_NoDup; try eassumption.
    simpl. apply mset_eq_PR_hdPR_t. assumption.
  - apply dreduced_semidreduced, len2_dreduced. rewrite app_length.
    rewrite iso_PR_del. rewrite <- Hleneq1. reflexivity.
    apply eq_sym in Hleneq1. apply noComma_1prim_inv in Hleneq1.
    apply PR_iso; assumption. }
  
  apply DerivRuleSDR_iff_deriv_rule_sdr.
  eapply deriv_prseq_P_tran. constructor 2; [|constructor].
  apply (SDR_incl_PR_deriv _ (∗ tostar (hdPR true Z),, I ⊢ strDel Z (hdPR true Z))).
  apply seq_semidreduced_reduc. assumption.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. eapply set_eq_incl_r. apply mset_eq_set_eq.
  rewrite <- app_assoc. apply mset_eq_app_swap_app.
  eapply set_eq_incl_l. apply mset_eq_set_eq.
  rewrite <- app_assoc. apply mset_eq_app_swap_app.
  apply incl_app_app; [apply incl_refl|].
  eapply set_eq_incl_l. apply set_eq_sym. eassumption.
  apply PR_incl_hdPR_del.

  eapply (deriv_prseq_P_tran _ _ _ [∗ tostar (hdPR true Z) ⊢ strDel Z (hdPR true Z)]).
  constructor 2; [|constructor].

  {
  apply DerivRulePseq_iff_deriv_prseq_P.
  unshelve eexists.
  confirm_derr (Der (∗ tostar (hdPR true Z) ⊢ strDel Z (hdPR true Z)) Idell
               [Unf (∗ tostar (hdPR true Z),, I ⊢ strDel Z (hdPR true Z))]).
  simpl. tauto. }

  apply SDR_incl_PR_deriv. assumption.
  apply seq_semidreduced_reduc.
  simpl. rewrite PR_tostar_eq; try assumption.
  eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac].
  eapply set_eq_incl_r; [apply set_eq_sym; eassumption|].
  apply incl_app.
  - auto_incl.
  - apply mset_incl_incl. apply mset_incl_strDel. assumption.
Defined.


#[export] Instance DerivRuleReducSDR_Idelr : DerivRuleReducSDR CPL_DC' Idelr.
Proof.
  prep_DRRSDR. set (X := snd afs "X"). set (Y := snd afs "Y").
  destruct (NoDup_rep_PR (strPR true (∗ X,, Y)) true)
    as [Z [HPRZ HNDZ]]; try (apply Forall_forall; intros sX HsX).
  apply strPR_not_nil. apply (PR_isPrim _ _ HsX).

  assert (seqSemidreduced (∗ Z ⊢ I)) as Hssp0. {
  unfold seqSemidreduced. simpl.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 Z true)) as [Hlengt1|Hleneq1].
  - apply erase_semidreduced with (true, I).
    + rewrite app_length. simpl. lia.
    + eapply mset_incl_dreduced. apply le_S_n.
      rewrite (erase_In_length (strPR true Z ++ [(true, I)])
                  (true, I)). rewrite app_length. simpl. lia.
      apply in_app_iff. right. left. reflexivity.
      apply (mset_incl_erase_erase _ ((true, I) :: strPR true Z)).
      apply mset_eq_incl. apply mset_eq_sym, mset_eq_cons_append.      
      rewrite erase_cons_eq. apply ge2_NoDup_dreduced;
        try lia; try assumption.
  - apply dreduced_semidreduced, len2_dreduced.
    rewrite app_length. rewrite <- Hleneq1. reflexivity. }

  pose proof (hdPR_isPrim Z true) as Hprhd.
  pose proof (@hdPR_in_PR Z true) as Hhdin.

  assert (seqSemidreduced (∗ tostar (hdPR true Z) ⊢ I,, strDel Z (hdPR true Z))) as Hssp1. {
  unfold seqSemidreduced.
  assert (length (PR (∗ tostar (hdPR true Z) ⊢ I,, strDel Z (hdPR true Z))) > 2) as Hlen.
  { simpl. rewrite ! app_length.
    pose proof (nb_PR_ge1 (tostar (hdPR true Z)) true).
    pose proof (nb_PR_ge1 (strDel Z (hdPR true Z)) true).
    simpl. lia. }
  apply erase_semidreduced with (true, I); try assumption.
  eapply mset_incl_dreduced.
  destruct (erase_In_length (PR (∗ tostar (hdPR true Z) ⊢ I,, strDel Z (hdPR true Z)))
              (true, I)).
  simpl. apply in_app_iff. right. left. reflexivity. lia.
  apply (mset_incl_erase_erase _ (PR (∗ I,, ∗ tostar (hdPR true Z) ⊢ strDel Z (hdPR true Z)))).
  simpl. apply mset_eq_incl.
  rewrite app_singl_eq_cons.
  rewrite (app_singl_eq_cons (strPR true (tostar (hdPR true Z)) ++ strPR true (strDel Z (hdPR true Z))) (true, I)).
  apply mset_eq_app_swap_app.
  simpl. rewrite PR_tostar_eq; try assumption.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 Z true)) as [Hlengt1|Hleneq1].
  - pose proof (strgt1_Comma _ _ Hlengt1) as HCZ.
    apply ge2_NoDup_dreduced.
    simpl.
    pose proof (strPR_niso_t Hhdin HCZ) as Hnisohd.
    pose proof (niso_strDel_length _ _ true Hprhd Hnisohd) as Hlen'.
    lia.
    eapply mset_eq_NoDup; try eassumption.
    simpl. unfold id. apply mset_eq_PR_hdPR. assumption.
  - apply len2_dreduced. rewrite app_length.
    rewrite iso_PR_del. rewrite <- Hleneq1. reflexivity.
    apply eq_sym in Hleneq1. apply noComma_1prim_inv in Hleneq1.
    apply PR_iso; assumption. }

  assert (seqSemidreduced (∗ tostar (hdPR true Z) ⊢ strDel Z (hdPR true Z))) as Hssp2. {
  unfold seqSemidreduced.
  simpl. rewrite PR_tostar_eq; try assumption.
  destruct (le_lt_eq_dec _ _ (nb_PR_ge1 Z true)) as [Hlengt1|Hleneq1].
  - pose proof (strgt1_Comma _ _ Hlengt1) as HCZ.
    apply dreduced_semidreduced, ge2_NoDup_dreduced.
    simpl.
    pose proof (strPR_niso_t Hhdin HCZ) as Hnisohd.
    pose proof (niso_strDel_length _ _ true Hprhd Hnisohd) as Hlen'.
    lia.
    eapply mset_eq_NoDup; try eassumption.
    simpl. apply mset_eq_PR_hdPR_t. assumption.
  - apply dreduced_semidreduced, len2_dreduced. rewrite app_length.
    rewrite iso_PR_del. rewrite <- Hleneq1. reflexivity.
    apply eq_sym in Hleneq1. apply noComma_1prim_inv in Hleneq1.
    apply PR_iso; assumption. }
  
  apply DerivRuleSDR_iff_deriv_rule_sdr.
  eapply deriv_prseq_P_tran. constructor 2; [|constructor].
  apply (SDR_incl_PR_deriv _ (∗ tostar (hdPR true Z) ⊢ I,, strDel Z (hdPR true Z))).
  apply seq_semidreduced_reduc. assumption.
  eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac].
  simpl. eapply set_eq_incl_r. apply mset_eq_set_eq.
  rewrite app_singl_eq_cons. apply mset_eq_app_swap_app.
  eapply set_eq_incl_l. apply mset_eq_set_eq.
  rewrite app_singl_eq_cons. apply mset_eq_app_swap_app.
  apply incl_app_app; [apply incl_refl|].
  eapply set_eq_incl_l. apply set_eq_sym. eassumption.
  apply PR_incl_hdPR_del.

  eapply (deriv_prseq_P_tran _ _ _ [∗ tostar (hdPR true Z) ⊢ strDel Z (hdPR true Z)]).
  constructor 2; [|constructor].

  {
  apply DerivRulePseq_iff_deriv_prseq_P.
  unshelve eexists.
  confirm_derr (Der (∗ tostar (hdPR true Z) ⊢ strDel Z (hdPR true Z)) Idelr
               [Unf (∗ tostar (hdPR true Z) ⊢ I,, strDel Z (hdPR true Z))]).
  simpl. tauto. }

  apply SDR_incl_PR_deriv. assumption.
  apply seq_semidreduced_reduc.
  simpl. rewrite PR_tostar_eq; try assumption.
  eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac].
  eapply set_eq_incl_r; [apply set_eq_sym; eassumption|].
  apply incl_app.
  - auto_incl.
  - apply mset_incl_incl. apply mset_incl_strDel. assumption.
Defined.



Lemma alr_DerivRuleReducSDR (DC : DISPCALC) (r : rule) `{dr : DerivRuleReducSDR DC r} : DerivRuleReducSDR DC r.
Proof. assumption. Defined.

Ltac trivial_axiom_tree r :=
  let d := fresh "d" in
  simpl;
  match goal with
    |- _ _ (?prems, ?conc) => set (d := Der conc r [])
  end;
  unshelve eexists; confirm_derr d.

Lemma all_DerivRuleReducSDR : forall r, r ∈ CPL_DC' -> DerivRuleReducSDR CPL_DC' r.
Proof.
  intros r Hr. unfold CPL_DC', MDE, ICW in Hr. simpl app in Hr.
  dec_destruct_List_In rule_eq_dec r;
  rewrite Heq; try (apply (alr_DerivRuleReducSDR _ _)); prep_DRRSDR.
  all:
    try (apply SDR_incl_PR_Deriv;
         try apply seq_semidreduced_reduc;
         eapply set_eq_incl_l; [apply reduc_PR_set_eq | idtac];
         eapply set_eq_incl_r; [apply reduc_PR_set_eq | idtac];
         simpl).
  all: try (apply set_eq_incl; aac_reflexivity).
  - apply incl_app_app; [apply incl_appl, incl_refl | apply incl_refl].
  - apply incl_app_app; [apply incl_refl | apply incl_tl, incl_refl].
  - apply incl_app_app; [apply incl_appr, incl_refl | apply incl_refl].
  - apply incl_app_app; [apply incl_refl | apply incl_appl, incl_refl].
  - apply incl_app_app; [apply incl_app; apply incl_refl | apply incl_refl].
  - apply incl_appr, incl_app; apply incl_refl.
  - apply incl_appr, incl_app; apply incl_refl.
  - unfold reduc. simpl. trivial_axiom_tree atrefl.
    simpl. apply dreduced_semidreduced, len2_dreduced. reflexivity.
  - unfold reduc. simpl. trivial_axiom_tree Topr.
    simpl. apply dreduced_semidreduced, len2_dreduced. reflexivity.
  - unfold reduc. simpl. trivial_axiom_tree Botl.
    simpl. apply dreduced_semidreduced, len2_dreduced. reflexivity.
Defined.




Ltac remember_POC lX :=
  match lX with
  | [] => simpl
  | ?X :: ?lX' =>
      let SX := fresh "SX" in
      let HeqSX := fresh "Heq" SX in
      remember (∗X) as SX eqn:HeqSX; remember_POC lX';
      rewrite HeqSX in *
  end.

Ltac cases_POC lX :=
  match lX with
  | [] => idtac
  | ?X :: ?lX' =>
      let res := fresh "res" in
      let X0 := fresh "X0" in
      let HeqX0 := fresh "Heq" X0 in
      let HeqX0' := fresh "Heq" X0 "'" in
      destruct (strStreduc_Starred_dec X) as [res|res];
      destruct res as [X0 [HeqX0 HeqX0']]; rewrite HeqX0, HeqX0';
      cases_POC lX'
  end.

Ltac pre_POC lX := remember_POC lX; cases_POC lX.


Ltac trivialUnf_POC :=
  let d := fresh "d" in
  simpl;
  match goal with
    |- DerivRulePOC _ (?prems, ?conc) => set (d := Unf conc)
  end;
  unshelve eexists; confirm_derr d; simpl derr_dt; unfold d; simpl; tauto.

Ltac trivial_POC r :=
  let d := fresh "d" in
  simpl;
  match goal with
    |- DerivRulePOC _ (?prems, ?conc) => set (d := Der conc r (map Unf prems))
  end;
  unshelve eexists; confirm_derr d; simpl derr_dt; unfold d; simpl; tauto.


Lemma all_DerivRuleSTReducPOC : forall r, r ∈ CPL_DC' -> DerivRuleSTReducPOC CPL_DC' r.
Proof.
  intros r Hr. unfold CPL_DC', MDE, ICW in Hr. simpl app in Hr.
  dec_destruct_List_In rule_eq_dec r; rewrite Heq;
    intros r' Hinst; apply ruleInst_ruleSubst in Hinst;
    destruct Hinst as [afs Heqr']; simpl in Heqr'; rewrite Heqr';
    try match goal with [H : r = ?r0 |- _] => trivial_POC r0 end.
  - pre_POC [snd afs "X"].
    trivial_POC Mlln.
    trivial_POC Mlls.
  - pre_POC [snd afs "X"].
    trivial_POC Mlls.
    trivial_POC Mlln.
  - pre_POC [snd afs "Y"].
    trivial_POC Mlrn.
    trivial_POC Mlrs.
  - pre_POC [snd afs "Y"].
    trivial_POC Mlrs.
    trivial_POC Mlrn.
  - pre_POC [snd afs "Y"].
    trivial_POC Mrln.
    trivial_POC Mrls.
  - pre_POC [snd afs "Y"].
    trivial_POC Mrls.
    trivial_POC Mrln.
  - pre_POC [snd afs "Z"].
    trivial_POC Mrrn.
    trivial_POC Mrrs.
  - pre_POC [snd afs "Z"].
    trivial_POC Mrrs.
    trivial_POC Mrrn.
  - pre_POC [snd afs "X"; snd afs "Y"].
    trivial_POC Snn.
    trivial_POC Sns.
    trivial_POC Ssn.
    trivial_POC Sss.
  - pre_POC [snd afs "X"; snd afs "Y"].
    trivial_POC Sns.
    trivial_POC Snn.
    trivial_POC Sss.
    trivial_POC Ssn.
  - pre_POC [snd afs "X"; snd afs "Y"].
    trivial_POC Ssn.
    trivial_POC Sss.
    trivial_POC Snn.
    trivial_POC Sns.
  - pre_POC [snd afs "X"; snd afs "Y"].
    trivial_POC Sss.
    trivial_POC Ssn.
    trivial_POC Sns.
    trivial_POC Snn.
  - trivialUnf_POC.
  - trivialUnf_POC.
  - trivialUnf_POC.
  - trivialUnf_POC.
  - pre_POC [snd afs "X"].
    trivial_POC ContWkls.
    trivial_POC ContWkln.
  - pre_POC [snd afs "X"].
    trivial_POC ContWkln.
    trivial_POC ContWkls.
Defined.

Theorem DerivRule_SDR_SR :
  forall r, DerivRuleSDR CPL_DC' r -> DerivRuleSR CPL_DC' (ruleStreduc r).
Proof.
  intros [ps c] Hder.
  apply DerivRuleSDR_iff_deriv_rule_sdr in Hder.
  apply DerivRuleSR_iff_deriv_rule_sr.
  revert c Hder.
  apply (deriv_prseq_P_mut_rect _ _ _ _
           (fun cs => deriv_prseqs_P CPL_DC' seqSemireduced (map streduc ps) (map streduc cs))).
  - intros c Hc Hsdr. simpl.
    apply deriv_prseq_P_prem. apply in_map. assumption.
    unfold seqSemireduced. split.
    apply seq_stred_streduc.
    apply seq_semidreduced_streduc. assumption.
  - intros ss c r Hexr Hwfr Hsdr Hders IH.
    eapply deriv_prseq_P_tran; [eassumption|].
    pose proof (all_DerivRuleSTReducPOC r Hexr _ Hwfr) as HPOC.
    apply DerivRulePseq_iff_deriv_rule_P in HPOC.
    simpl in HPOC.
    eapply deriv_prseq_P_imp; [|eassumption].
    intros s [Hs|Hs].
    + rewrite Hs. split; try apply seq_stred_streduc.
      apply seq_semidreduced_streduc. assumption.
    + apply (deriv_prseqs_P_concl_P _ _ _ _ IH s Hs).
  - constructor.
  - intros. simpl. constructor; assumption.
Defined.

Theorem DerivRuleReduc_SDR_SR :
  forall r, r ∈ CPL_DC' -> DerivRuleReducSDR CPL_DC' r -> DerivRuleReducSR CPL_DC' r.
Proof.
  intros rs Hr Hder ri Hinst. destruct Hder as [Hder]. specialize (Hder ri Hinst).
  rewrite <- rule_streduc_fixpoint; try apply rule_red_reduc.
  apply DerivRule_SDR_SR. assumption.
Qed.


Lemma all_DerivRuleReducSR : forall r, r ∈ CPL_DC' -> DerivRuleReducSR CPL_DC' r.
Proof.
  intros r Hr. apply DerivRuleReduc_SDR_SR;
  try apply all_DerivRuleReducSDR; assumption.
Defined.


Lemma C1_holds : C1 CPL_DC'.
Proof. auto_C1. Qed.


Theorem CPL_DC'_Deriv_dec : forall s, Deriv CPL_DC' s + (Deriv CPL_DC' s -> False).
Proof.
  apply Deriv_dec.
  - apply C1_holds.
  - apply set_eq_PR_Deriv.
  - apply all_DerivRuleReducSR.
Defined.
