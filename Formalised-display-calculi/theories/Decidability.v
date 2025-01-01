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
Require Import Finiteness.

Require Import PL.
Import CPL.
Import CPLNotations.

Open Scope type_scope.
Open Scope list_scope.



Section Derivability.

  Context (DC : DISPCALC).

  Definition deriv_seq_sdr := deriv_seq_P DC seqSemidreduced.
  Definition deriv_seq_sr := deriv_seq_P DC seqSemireduced.

  Definition deriv_rule_sdr := deriv_rule_P DC seqSemidreduced.
  Definition deriv_rule_sr := deriv_rule_P DC seqSemireduced.

  Class DerivPseq (P : sequent -> Prop) (s : sequent) := {
    derpseq_der :: Deriv DC s;
    derpseq_allp : allDT (fun d => P (conclDT d)) (der_dt DC)}.

  Class DerivSDR (s : sequent) := {
    dersdr_der :: Deriv DC s;
    dersdr_semidreduced : dtSemidreduced (der_dt DC); }.

  Class DerivSR (s : sequent) := {
    dersr_der :: Deriv DC s;
    dersr_semireduced : dtSemireduced (der_dt DC); }.

  Lemma DerivSDR_Pseq : forall s, DerivSDR s <+> DerivPseq seqSemidreduced s.
  Proof. intro s. split; intro der; [exists dersdr_der | exists derpseq_der]; apply der. Defined.

  Lemma DerivSR_Pseq : forall s, DerivSR s <+> DerivPseq seqSemireduced s.
  Proof. intro s. split; intro der; [exists dersr_der | exists derpseq_der]; apply der. Defined.

  Class DerivISR (s : sequent) := {
    derisr_dersr :: DerivSR s;
    derisr_irredun : irredundant (der_dt DC); }.

  Class DerivCISR (ls : list sequent) (s : sequent) := {
    dercisr_derisr :: DerivISR s;
    dercisr_cont : allDT (fun d => In (conclDT d) ls) (der_dt DC) }.

  Class DerivRulePseq (P : sequent -> Prop) (r : rule) := {
    derrpseq_derr :: DerivRule DC r;
    derrpseq_allp : allDT (fun d => P (conclDT d)) (derr_dt DC) }.

  Definition DerivRulePOC (r : rule) :=
    DerivRulePseq (fun s => s = conclRule r \/ s ∈ premsRule r) r.

  Definition DerivRuleSTReducPOC (r : rule) :=
    forall r', ruleInst r r' -> DerivRulePOC (ruleStreduc r').
  
  Class DerivRuleSDR (r : rule) := {
    derrsdr_derr :: DerivRule DC r;
    derrsdr_semidreduced : dtSemidreduced (derr_dt DC); }.

  Class DerivRuleSR (r : rule) := {
    derrsr_derr :: DerivRule DC r;
    derrsr_semireduced : dtSemireduced (derr_dt DC); }.

  Class DerivRuleReducSDR (r : rule) := {
    allinst_derrsdr : forall r', ruleInst r r' -> DerivRuleSDR (ruleReduc r') }.

  Definition DerivRuleReducSR (r : rule) :=
    forall r', ruleInst r r' -> DerivRuleSR (ruleReduc r').

  Lemma DerivRuleSDR_Pseq : forall r, DerivRuleSDR r <+> DerivRulePseq seqSemidreduced r.
  Proof. intro r. split; intro der; [exists derrsdr_derr | exists derrpseq_derr]; apply der. Defined.

  Lemma DerivRuleSR_Pseq : forall s, DerivRuleSR s <+> DerivRulePseq seqSemireduced s.
  Proof. intro s. split; intro der; [exists derrsr_derr | exists derrpseq_derr]; apply der. Defined.


  Lemma ForallT_DerivPseq_sig (P : sequent -> Prop) :
    forall {ls}, ForallT (DerivPseq P) ls ->
    {ldt | Forall2 (fun s dt => proper DC dt /\ conclDT dt = s /\ allDT (fun d => P (conclDT d)) dt) ls ldt}.
  Proof.
    intros ls Hder. induction ls as [|s ls]; try (exists []; constructor).
    pose proof (ForallT_inv Hder) as Hders.
    pose proof (ForallT_inv_tail Hder) as Hderls.
    specialize (IHls Hderls). destruct IHls as [ldt Hldt].
    destruct Hders as [[dt Hpro Hconc] Hsr].
    exists (dt :: ldt). constructor; try assumption. tauto.
  Defined.

  Lemma ForallT_DerivRulePseq_sig (P : sequent -> Prop) :
    forall {prems ls}, ForallT (fun s => DerivRulePseq P (prems, s)) ls ->
    {ldt | Forall2 (fun s dt => semiproper DC dt /\ incl (premsDT dt) prems /\
                               conclDT dt = s /\ allDT (fun d => P (conclDT d)) dt) ls ldt}.
  Proof.
    intros prems ls Hder. induction ls as [|s ls]; try (exists []; constructor).
    pose proof (ForallT_inv Hder) as Hders.
    pose proof (ForallT_inv_tail Hder) as Hderls.
    specialize (IHls Hderls). destruct IHls as [ldt Hldt].
    destruct Hders as [[dt Hsp Hprems Hconc] Hsr].
    exists (dt :: ldt). constructor; try tauto.    
  Defined.
  
  Lemma ForallT_DerivISR_sig : forall {ls}, ForallT DerivISR ls ->
    {ldt | Forall2 (fun s dt => proper DC dt /\ conclDT dt = s /\ dtSemireduced dt /\
                     irredundant dt) ls ldt}.
  Proof.
    intros ls Hder. induction ls as [|s ls]; try (exists []; constructor).
    pose proof (ForallT_inv Hder) as Hders.
    pose proof (ForallT_inv_tail Hder) as Hderls.
    specialize (IHls Hderls). destruct IHls as [ldt Hldt].
    destruct Hders as [[[dt Hpro Hconc] Hsr] Hirr].
    exists (dt :: ldt). constructor; try assumption. tauto.
  Defined.
  
  Lemma ForallT_DerivCISR_sig : forall {lc ls}, ForallT (DerivCISR lc) ls ->
    {ldt | Forall2 (fun s dt => proper DC dt /\ conclDT dt = s /\ dtSemireduced dt /\
                     irredundant dt /\ allDT (fun d => In (conclDT d) lc) dt) ls ldt}.
  Proof.
    intros lc ls Hder. induction ls as [|s ls]; try (exists []; constructor).
    pose proof (ForallT_inv Hder) as Hders.
    pose proof (ForallT_inv_tail Hder) as Hderls.
    specialize (IHls Hderls). destruct IHls as [ldt Hldt].
    destruct Hders as [[[[dt Hpro Hconc] Hsr] Hirr] Hcont].
    exists (dt :: ldt). constructor; try assumption. tauto.
  Defined.

  Lemma DerivCISR_Up (ls : list sequent) (s : sequent) (dercisr : DerivCISR ls s) :
    forall t, In t (map conclDT (nextUp (der_dt DC))) -> DerivCISR (remove_seq s ls) t.
  Proof.
    intros t Hint. destruct dercisr as [[[[dt Hpro Hconc] Hsr] Hirr] Hcont]. simpl in *.
    destruct dt; try contradict (not_proper_Unf _ Hpro).
    simpl in Hconc. rewrite Hconc in *. clear Hconc.
    apply in_map_inv_sig in Hint.
    destruct Hint as [d [Hconcd Hind]].
    do 3 (try unshelve eexists). exists d; try assumption. all: simpl.
    apply (proper_Der_immUp Hpro Hind).
    apply (allDT_Der_immUp Hsr Hind).
    apply (allDT_Der_immUp Hirr Hind).
    rewrite allDT_in_tree. intros d0 Hind0.
    apply in_in_remove.
    - intro Heq. unfold irredundant in Hirr.
      rewrite allDT_in_tree in Hirr. apply (Hirr (Der s r l)); try constructor.
      constructor 1 with d; try assumption.
      apply (in_tree_seqInDT d0); try assumption.
      constructor 1. assumption.
    - rewrite allDT_in_tree in Hcont. apply Hcont.
      constructor 2 with d; assumption.
  Defined.

  Lemma DerivPseq_iff_deriv_seq_P (P : sequent -> Prop) (s : sequent) :
    DerivPseq P s <+> deriv_seq_P DC P s.
  Proof.
    split.
    - intros [[dt Hprop Hconc] HP]. simpl in HP. rewrite <- Hconc. clear s Hconc.
      induction dt as [|s r l IH]; try (contradict Hprop; apply not_proper_Unf).
      pose proof (proper_up_Forall DC Hprop) as Hpropup. apply Forall_ForallT in Hpropup.
      apply (ForallT_mp Hpropup) in IH. apply proper_root in Hprop.
      simpl in Hprop. destruct Hprop as [Hexr Hwfr].
      apply (deriv_seq_P_ext _ _ _ _ r Hexr Hwfr).
      + apply allDT_root in HP. assumption.
      + apply ForallT_deriv_seqs_P. apply ForallT_map.
        apply allDTUp, Forall_ForallT in HP. apply (ForallT_mp HP) in IH.
        assumption.
    - revert s. apply (deriv_seq_P_mut_rect _ _ (fun s => DerivPseq P s)
                         (fun ls => ForallT (DerivPseq P) ls)).
      + intros ps c r Hexr Hwfr HPc Hders HDers.
        apply ForallT_DerivPseq_sig in HDers.
        destruct HDers as [ldt Hldt].
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hpro Hldt].
        apply Forall2_Forall_r in Hpro.
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hconc HP].
        apply Forall2_flip in Hconc.
        rewrite Forall2_map_iff in Hconc. apply Forall2_eq_iff in Hconc.
        rewrite map_id in Hconc. rewrite <- Hconc in Hwfr.
        apply Forall2_Forall_r in HP.
        unshelve eexists. exists (Der c r ldt).
        apply proper_Der; try assumption. reflexivity.
        simpl. split; try assumption.
        apply Forall_fold_right. assumption.
      + apply ForallT_nil.
      + intros c cs Hder HDer Hders HDers.
        apply ForallT_cons; assumption.
  Defined.

  Lemma ForallT_DerivPseq_iff_deriv_seq_P (P : sequent -> Prop) (ls : list sequent) :
    ForallT (DerivPseq P) ls <+> ForallT (deriv_seq_P DC P) ls.
  Proof.
    apply ForallT_act_iff. intro s. apply DerivPseq_iff_deriv_seq_P.
  Defined.


  Lemma DerivSDR_iff_deriv_seq_sdr :
    forall s, DerivSDR s <+> deriv_seq_sdr s.
  Proof.
    intro s. rewrite DerivSDR_Pseq.
    apply DerivPseq_iff_deriv_seq_P.
  Defined.

  Lemma ForallT_DerivSDR_iff_deriv_seq_sdr :
    forall ls, ForallT DerivSDR ls <+> ForallT deriv_seq_sdr ls.
  Proof.
    intro ls. split.
    - intro H. apply ForallT_DerivPseq_iff_deriv_seq_P.
      revert H. apply ForallT_act_iff.
      intro s. split; apply DerivSDR_Pseq.
    - apply ForallT_act_iff. apply DerivSDR_iff_deriv_seq_sdr.
  Defined.


  Lemma DerivSR_iff_deriv_seq_sr :
    forall s, DerivSR s <+> deriv_seq_sr s.
  Proof.
    intro s. rewrite DerivSR_Pseq.
    apply DerivPseq_iff_deriv_seq_P.
  Defined.

  Lemma ForallT_DerivSR_iff_deriv_seq_sr :
    forall ls, ForallT DerivSR ls <+> ForallT deriv_seq_sr ls.
  Proof.
    intro ls. split.
    - intro H. apply ForallT_DerivPseq_iff_deriv_seq_P.
      revert H. apply ForallT_act_iff.
      intro s. split; apply DerivSR_Pseq.
    - apply ForallT_act_iff. apply DerivSR_iff_deriv_seq_sr.
  Defined.

  Lemma DerivRulePseq_iff_deriv_rule_P (P : sequent -> Prop) (r : rule) :
    DerivRulePseq P r <+> deriv_rule_P DC P r.
  Proof.
    destruct r as [ps c]. split.
    - intros [[dt Hsp Hprems Hconc] HP]. simpl in Hprems, Hconc.
      apply (deriv_prseq_P_weak _ _ (premsDT dt));
      try assumption. rewrite <- Hconc.
      simpl in HP. clear ps c Hprems Hconc.
      induction dt as [|s r l IH].
      + apply deriv_prseq_P_prem. simpl. tauto. assumption.
      + pose proof (semiproperUp DC _ Hsp) as Hspup. apply Forall_ForallT in Hspup.
        apply (ForallT_mp Hspup) in IH. apply semiproper_root in Hsp.
        simpl in Hsp. destruct Hsp as [Hexr Hwfr].
        apply (deriv_prseq_P_ext _ _ _ _ _ _ Hexr Hwfr).
        apply allDT_root in HP. assumption.
        apply ForallT_deriv_prseqs_P. apply ForallT_map.
        rewrite ForallT_forall in IH. apply ForallT_forall.
        intros dt Hdt. specialize (IH dt Hdt).
        apply allDTUp in HP. rewrite Forall_forall in HP.
        specialize (HP dt Hdt). specialize (IH HP).
        eapply deriv_prseq_P_weak; try eassumption.
        apply (premsDTUp _ (premsDT (Der s r l)) (incl_refl _)).
        assumption.
    - revert c.
      apply (deriv_prseq_P_mut_rect _ _ _ (fun c => DerivRulePseq P (ps, c))
               (fun lc => ForallT (fun c => DerivRulePseq P (ps, c)) lc)).
      + intros c Hc HPc. unshelve eexists. exists (Unf c); simpl;
          [apply semiproper_Unf|auto_incl|reflexivity].
        simpl. assumption.
      + intros cs c r Hexr Hwfr HPc Hders HDers.
        apply ForallT_DerivRulePseq_sig in HDers.
        destruct HDers as [ldt Hldt].
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hspup Hldt].
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hprems Hldt].
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hconc HP].
        apply Forall2_Forall_r in Hspup, Hprems, HP. apply Forall2_flip in Hconc.
        rewrite Forall2_map_iff in Hconc. apply Forall2_eq_iff in Hconc.
        rewrite map_id in Hconc. rewrite <- Hconc in Hwfr.
        assert (semiproper DC (Der c r ldt)) as Hsp.
        { apply semiproper_Der; tauto. }
        unshelve eexists. exists (Der c r ldt); try apply Hsp; try reflexivity.
        rewrite premsDT_Der. apply Forall_incl_premsDTs. assumption.
        simpl. split; try assumption.
        apply Forall_fold_right. assumption.
      + apply ForallT_nil.
      + intros c cs Hder HDer Hders HDers.
        apply ForallT_cons; assumption.
  Defined.

  Lemma DerivRulePseq_iff_deriv_prseq_P (P : sequent -> Prop) :
    forall ps c, DerivRulePseq P (ps, c) <+> deriv_prseq_P DC P ps c.
  Proof. intros ps c. apply DerivRulePseq_iff_deriv_rule_P. Defined.

  Lemma DerivRuleSDR_iff_deriv_rule_sdr :
    forall r, DerivRuleSDR r <+> deriv_rule_sdr r.
  Proof.
    intro r. rewrite DerivRuleSDR_Pseq.
    apply DerivRulePseq_iff_deriv_rule_P.
  Defined.

  Lemma DerivRuleSR_iff_deriv_rule_sr :
    forall r, DerivRuleSR r <+> deriv_rule_sr r.
  Proof.
    intro r. rewrite DerivRuleSR_Pseq.
    apply DerivRulePseq_iff_deriv_rule_P.
  Defined.

  Lemma ForallT_DerivRulePseq_iff_deriv_rule_P (P : sequent -> Prop) (lr : list rule) :
    ForallT (DerivRulePseq P) lr <+> ForallT (deriv_rule_P DC P) lr.
  Proof.
    apply ForallT_act_iff. intro s. apply DerivRulePseq_iff_deriv_rule_P.
  Defined.

  Lemma ForallT_DerivRuleSDR_iff_deriv_rule_sdr (lr : list rule) :
    ForallT DerivRuleSDR lr <+> ForallT deriv_rule_sdr lr.
  Proof.
    apply ForallT_act_iff. intro s. apply DerivRuleSDR_iff_deriv_rule_sdr.
  Defined.

  Lemma DerivSDR_tran : forall ls s, ForallT DerivSDR ls -> DerivRuleSDR (ls, s) -> DerivSDR s.
  Proof.
    intros ls s Hder Hderr. apply DerivSDR_iff_deriv_seq_sdr.
    apply DerivRuleSDR_iff_deriv_rule_sdr in Hderr.
    apply ForallT_DerivSDR_iff_deriv_seq_sdr in Hder.
    apply ForallT_deriv_seqs_P_iff in Hder.
    eapply deriv_seq_P_tran; eassumption.
  Defined.

  Lemma DerivSR_tran : forall ls s, ForallT DerivSR ls -> DerivRuleSR (ls, s) -> DerivSR s.
  Proof.
    intros ls s Hder Hderr. apply DerivSR_iff_deriv_seq_sr.
    apply DerivRuleSR_iff_deriv_rule_sr in Hderr.
    apply ForallT_DerivSR_iff_deriv_seq_sr in Hder.
    apply ForallT_deriv_seqs_P_iff in Hder.
    eapply deriv_seq_P_tran; eassumption.
  Defined.

  Lemma DerivRulePseq_tran (P : sequent -> Prop) :
    forall prems ls conc, ForallT (fun s => DerivRulePseq P (prems, s)) ls ->
                     DerivRulePseq P (ls, conc) -> DerivRulePseq P (prems, conc).
  Proof.
    intros prems ls conc Hall H.
    apply DerivRulePseq_iff_deriv_rule_P in H.
    apply DerivRulePseq_iff_deriv_rule_P.
    apply ForallT_map, ForallT_DerivRulePseq_iff_deriv_rule_P in Hall.
    unfold deriv_rule_sdr, deriv_rule_P in Hall.
    apply ForallT_map in Hall. apply ForallT_deriv_prseqs_P_iff in Hall.
    eapply deriv_prseq_P_tran; eassumption.
  Defined.

  Lemma DerivRulePseq_imp (P Q : sequent -> Prop) :
    (forall s, P s -> Q s) -> forall r, DerivRulePseq P r -> DerivRulePseq Q r.
  Proof.
    intros HPQ r [Hderr HP].
    exists Hderr. eapply allDT_impl.
    intro dt. apply HPQ. assumption.
  Defined.

  Lemma DerivRulePseq_Proot {P prems conc} : DerivRulePseq P (prems, conc) -> P conc.
  Proof.
    intros [[dt H H0 Hconc] HP].
    apply allDT_root in HP. simpl in HP.
    rewrite Hconc in HP. assumption.
  Qed.
  
  Lemma DerivRuleSDR_tran :
    forall prems ls conc, ForallT (fun s => DerivRuleSDR (prems, s)) ls ->
            DerivRuleSDR (ls, conc) -> DerivRuleSDR (prems, conc).
  Proof.
    intros prems ls conc Hall H.
    apply DerivRuleSDR_iff_deriv_rule_sdr in H.
    apply DerivRuleSDR_iff_deriv_rule_sdr.
    apply ForallT_map, ForallT_DerivRuleSDR_iff_deriv_rule_sdr in Hall.
    unfold deriv_rule_sdr, deriv_rule_P in Hall.
    apply ForallT_map in Hall. apply ForallT_deriv_prseqs_P_iff in Hall.
    eapply deriv_prseq_P_tran; eassumption.
  Defined.

  Lemma DerivRuleSDR_incl : forall prems prems' conc, incl prems prems' ->
    DerivRuleSDR (prems, conc) -> DerivRuleSDR (prems', conc).
  Proof.
    intros prems prems' conc Hinc Hder.
    apply DerivRuleSDR_iff_deriv_rule_sdr in Hder.
    apply DerivRuleSDR_iff_deriv_rule_sdr.
    eapply deriv_prseq_P_weak; eassumption.
  Defined.


End Derivability.


Section Decidability.

  Context (DC : DISPCALC).
  Hypothesis C1_holds : C1 DC.
  Hypothesis set_eq_deriv : forall s t, PR s ≃ PR t -> DerivRule DC ([s], t).
  Hypothesis DC_ruleRed_sr : forall r, r ∈ DC -> DerivRuleReducSR DC r.

Theorem subfml_ppty :
    forall dt, proper DC dt ->
          allDT (fun d => dtFmls d ⊆ listsubexprs (dtFmls dt) /\ dtSVs d ⊆ dtSVs dt) dt.
  Proof.
    induction dt as [s|s r l IH]; intro Hpro.
    - unfold dtFmls, dtSVs. simpl. split; [apply listsubexprs_refl | apply incl_refl].
    - pose proof (properUp Hpro) as Hproup. simpl in Hproup.
      apply (Forall_mp Hproup) in IH. rewrite allDT_Der.
      repeat split; try ((apply listsubexprs_refl) || (apply incl_refl)).
      rewrite allDTs_Forall. rewrite Forall_forall in IH |- *.
      intros dt Hindt. specialize (IH dt Hindt).
      rewrite allDT_in_tree in IH. rewrite allDT_in_tree.
      intros d Hind. specialize (IH d Hind). destruct IH as [IHfmls IHSVs].
      destruct Hpro as [Hexr [Hwfr Hprems]].
      apply allDT_root in Hexr, Hwfr. simpl in Hexr, Hwfr.
      pose proof (C1_holds r Hexr) as HC1.
      apply (C1_ruleInst r (map conclDT l, s) Hwfr) in HC1.
      unfold C1_one in HC1. simpl in HC1. rewrite Forall_map in HC1.
      rewrite Forall_forall in HC1. specialize (HC1 dt Hindt). destruct HC1 as [Hfmls HSVs].
      split; eapply incl_tran; try eassumption.
      apply listsubexprs_subclosed. assumption.
  Qed.

  Definition subPRuns (s : sequent) : list structr :=
    I :: map FS (listsubexprs (seqFmls s)) ++ map SV (seqSVs s).

  Definition subPR (s : sequent) : list sstructr :=
    map (pair true) (subPRuns s) ++ map (pair false) (subPRuns s).

  Lemma fmls_in_PR : forall X A b sgn, In (sgn, £A) (strPR b X) -> In A (strFmls X).
  Proof.
    induction X; intros A0 b sgn H.
    - simpl. destruct H as [H|H]; try contradiction. discriminate.
    - simpl. destruct H as [H|H]; try contradiction. injection H.
      intros HeqA Heqb. now left.
    - simpl. destruct H as [H|H]; try contradiction. discriminate.
    - unfold strFmls. rewrite allVars_eq. rewrite Var_dec_not_Var;
        try (intros V HV; discriminate).
      simpl ipse. fold strFmls. simpl.
      rewrite app_nil_r. apply (IHX _ (negb b) sgn). assumption.
    - unfold strFmls. rewrite allVars_eq. rewrite Var_dec_not_Var;
        try (intros V HV; discriminate).
      simpl ipse. fold strFmls. simpl.
      rewrite app_nil_r. simpl in H.
      rewrite in_app_iff in H |- *. destruct H as [H|H].
      + left. apply (IHX1 _ b sgn). assumption.
      + right. apply (IHX2 _ b sgn). assumption.
  Qed.

  Lemma fmls_in_seqPR : forall s A sgn, In (sgn, £A) (PR s) -> In A (seqFmls s).
  Proof.
    intros s A sgn H. destruct s. simpl in H |- *.
    rewrite in_app_iff in H |- *. destruct H as [H|H].
    - left. apply (fmls_in_PR _ _ false sgn). assumption.
    - right. apply (fmls_in_PR _ _ true sgn). assumption.
  Qed.

  Lemma SVs_in_PR : forall X x b sgn, In (sgn, $x) (strPR b X) -> In x (strSVs X).
  Proof.
    induction X; intros A0 b sgn H.
    - destruct H as [H|H]; try contradiction. injection H.
      intros HeqA Heqb. now left.
    - destruct H as [H|H]; try contradiction. discriminate.
    - destruct H as [H|H]; try contradiction. discriminate.
    - unfold strSVs. rewrite allVars_eq. rewrite Var_dec_not_Var;
        try (intros V HV; discriminate).
      simpl ipse. fold strSVs. simpl.
      rewrite app_nil_r.
      apply (IHX _ (negb b) sgn). assumption.
    - unfold strSVs. rewrite allVars_eq. rewrite Var_dec_not_Var;
        try (intros V HV; discriminate).
      simpl ipse. fold strSVs. simpl.
      rewrite app_nil_r. simpl in H.
      rewrite in_app_iff in H |- *. destruct H as [H|H].
      + left. apply (IHX1 _ b sgn). assumption.
      + right. apply (IHX2 _ b sgn). assumption.
  Qed.

  Lemma SVs_in_seqPR : forall s x sgn, In (sgn, $x) (PR s) -> In x (seqSVs s).
  Proof.
    intros s x sgn H. destruct s. unfold seqSVs. simpl in H |- *.
    rewrite in_app_iff in H |- *. destruct H as [H|H].
    - left. apply (SVs_in_PR _ _ false sgn). assumption.
    - right. apply (SVs_in_PR _ _ true sgn). assumption.
  Qed.

  Lemma fmls_in_subPR : forall s A sgn, In A (listsubexprs (seqFmls s)) -> In (sgn, £A) (subPR s).
  Proof.
    intros s A sgn H. unfold subPR, subPRuns. rewrite in_app_iff.
    destruct sgn; [left | right]; apply in_map; right; rewrite in_app_iff;
    left; apply in_map; assumption.
  Qed.

  Lemma SVs_in_subPR : forall s v sgn, In v (seqSVs s) -> In (sgn, $v) (subPR s).
  Proof.
    intros s v sgn H. unfold subPR, subPRuns. rewrite in_app_iff.
    destruct sgn; [left | right]; apply in_map; right; rewrite in_app_iff;
    right; apply in_map; assumption.
  Qed.

  Lemma incl_fmls_SVs_PR : forall s t,
    incl (seqFmls s) (listsubexprs (seqFmls t)) -> incl (seqSVs s) (seqSVs t) ->
      incl (PR s) (subPR t).
  Proof.
    intros s t Hfmls HSVs sZ HsZ. destruct sZ as [b Z].
    pose proof (seqPR_isPrim _ HsZ) as Hpr. simpl in Hpr.
    destruct Z; try contradiction.
    - apply SVs_in_seqPR in HsZ. apply SVs_in_subPR.
      apply HSVs. assumption.
    - apply fmls_in_seqPR in HsZ. apply fmls_in_subPR.
      apply Hfmls. assumption.
    - unfold subPR, subPRuns. simpl. destruct b.
      + left. reflexivity.
      + rewrite in_app_iff. right. right. left. reflexivity.
  Qed.

  Lemma seqPR_subPR : forall s, PR s ⊆ subPR s.
  Proof.
    intro s. apply incl_fmls_SVs_PR; try apply incl_refl.
    apply listsubexprs_refl.
  Qed.

  Theorem subPR_ppty : forall dt, proper DC dt ->
    allDT (fun d => incl (PR (conclDT d)) (subPR (conclDT dt))) dt.
  Proof.
    intros dt Hpro. rewrite allDT_in_tree. intros d Hind.
    pose proof (subfml_ppty dt Hpro) as H. rewrite allDT_in_tree in H.
    specialize (H d Hind). apply incl_fmls_SVs_PR; tauto.
  Qed.

  Lemma reduc_DerivSR : forall s, Deriv DC s -> DerivSR DC (reduc s).
  Proof.  
    intros s Hders. destruct Hders as [dt Hpro Hconc]. rewrite <- Hconc.
    revert Hpro. clear s Hconc. induction dt as [|s r l IH];
      try (intro Hpro; contradict Hpro; apply not_proper_Unf).
    intros Hpro. simpl. pose proof (properUp Hpro) as Hproup. simpl in Hproup.
    apply Forall_ForallT in Hproup.
    apply (ForallT_mp Hproup) in IH. apply ForallT_map in IH.
    rewrite <- map_map in IH.
    assert (In r DC) as Hinr by apply Hpro.
    apply (DerivSR_tran DC _ _ IH).
    apply (DC_ruleRed_sr r Hinr (map conclDT l, s)).
    apply Hpro.
  Defined.

  Lemma push_irredundant :
    forall dt, proper DC dt -> dtSemireduced dt -> Forall irredundant (nextUp dt) ->
          {dt' | conclDT dt' = conclDT dt /\ proper DC dt' /\ dtSemireduced dt' /\ irredundant dt'}.
  Proof.
    intros dt Hpro Hsr Hirr. destruct (seqInDTs_dec (nextUp dt) (conclDT dt)) as [yes|no].
    - destruct yes as [d [dt' [Hind [Hindt' Hconcdt']]]].
      exists d. split; try assumption. split; [idtac | split].
      + apply properUp in Hpro. rewrite Forall_forall in Hpro.
        specialize (Hpro dt' Hindt'). apply proper_allDT in Hpro.
        rewrite allDT_in_tree in Hpro. apply Hpro. assumption.
      + unfold dtSemireduced in Hsr. apply allDTUp in Hsr.
        rewrite Forall_forall in Hsr. specialize (Hsr dt' Hindt').
        rewrite allDT_in_tree_allDT in Hsr. apply Hsr. assumption.
      + rewrite Forall_forall in Hirr. specialize (Hirr dt' Hindt').
        unfold irredundant in Hirr. rewrite allDT_in_tree_allDT in Hirr.
        apply Hirr. assumption.
    - exists dt. split; try reflexivity. repeat (split; try assumption).
      apply allDT_nextUp. rewrite allDTs_Forall. tauto.
  Defined.

  Lemma SR_to_ISR : forall s, DerivSR DC s -> DerivISR DC s.
  Proof.
    intros s [[dt Hpro Hconc] Hsr]. simpl in Hsr. rewrite <- Hconc.
    revert Hpro Hsr. clear s Hconc. induction dt as [|s r l IH];
      try (intro Hpro; contradict Hpro; apply not_proper_Unf).
    intros Hpro Hsr. simpl.
    pose proof (properUp Hpro) as Hproup. simpl in Hproup.
    pose proof (allDTUp Hsr) as Hsrup. simpl in Hsrup.
    apply (Forall_ForallT) in Hproup.
    apply (ForallT_mp Hproup) in IH.
    apply (Forall_ForallT) in Hsrup.
    apply (ForallT_mp Hsrup) in IH.
    apply ForallT_map in IH.
    destruct (ForallT_DerivISR_sig DC IH) as [li Hli].
    apply Forall2_and_inv in Hli. destruct Hli as [Hproli Hli].
    apply Forall2_Forall_r in Hproli.
    apply Forall2_and_inv in Hli. destruct Hli as [Hconcli Hli].
    apply Forall2_flip in Hconcli. rewrite Forall2_map_iff in Hconcli.
    rewrite Forall2_eq_iff, map_id in Hconcli.
    apply Forall2_Forall_r in Hli.
    apply Forall_and_inv in Hli. destruct Hli as [Hsrli Hirrli].
    destruct (push_irredundant (Der s r li)) as
      [dti [Hconcdti [Hprodti [Hsrdti Hsindti]]]]; try assumption.
    - apply proper_Der; try apply Hpro; try assumption.
      rewrite Hconcli. apply Hpro.
    - unfold dtSemireduced in Hsr |- *. rewrite allDT_Der in Hsr |- *.
      rewrite allDTs_Forall. tauto.
    - do 2 (try (unshelve eexists)). exists dti. all: simpl; assumption.
  Defined.


  Lemma reduc_DerivISR : forall s, Deriv DC s -> DerivISR DC (reduc s).
  Proof. intros s Hders. apply SR_to_ISR, reduc_DerivSR. assumption. Defined.

  Theorem red_DerivISR :
    forall s, seqReduced s -> Deriv DC s -> DerivISR DC s.
  Proof.
    intros s Hreds H. rewrite <- (seq_reduc_fixpoint _ Hreds).
    revert H. apply reduc_DerivISR.
  Defined.


  Lemma all_applications_of : forall (r : rule) (ls : list sequent) (s : sequent),
    {lap : list (list sequent) | forall ap, In ap lap <-> (incl ap ls /\ ruleInst r (ap, s))}.
  Proof.
    intros r ls s. destruct (all_msets_len ls (length (premsRule r))) as [lc Hlc].
    exists (filter (fun prems => bisruleInst r (prems, s)) lc).
    intro ap. rewrite filter_In, bisruleInst_true_iff, Hlc.
    split; try tauto. intros [Hinc Hrulefs]. repeat (split; try assumption).
    apply eq_sym. apply (ruleInst_length r (ap, s)). assumption.
  Defined.

  Lemma all_applications (lr : list rule) (ls : list sequent) (s : sequent) :
    {llap : list (list (list sequent)) |
      Forall2 (fun r lap => forall ap, In ap lap <-> (incl ap ls /\ ruleInst r (ap, s))) lr llap}.
  Proof.
    apply ForallT_sig_elim.
    induction lr as [|r lr]; try constructor;
      [apply all_applications_of | assumption].
  Defined.


  Lemma DerivCISR_dec : forall l s, (forall t, t ∈ l -> seqSemireduced t) -> s ∈ l ->
    DerivCISR DC l s + (DerivCISR DC l s -> False).
  Proof.
    intro ls. induction ls as [ls IH] using (wf_nat_ind (@length sequent)).
    intros s Hsrls Hins. set (ls' := remove_seq s ls).
    destruct (all_applications DC ls' s) as [llap Hllap].
    destruct (@ForallT_dec_EEF _
                  (fun t => DerivCISR DC ls' t)
                  (fun t => DerivCISR DC ls' t -> False) llap) as [yes|no].
    - rewrite ForallT_forall. intros lap Hinlap.
      rewrite ForallT_forall. intros ap Hinap.
      rewrite ForallT_forall. intros t Hint.
      destruct (Forall2_sig_l Hllap lap Hinlap) as [r [Hinr Hlap]].
      pose proof (proj1 (Hlap ap) Hinap) as Hap.
      apply IH.
      + apply remove_length_lt. assumption.
      + intros u Hinu. apply Hsrls. apply (in_remove _ _ _ _ Hinu).
      + apply Hap. assumption.
    - left.
      rewrite ExistsT_exists in yes.
      destruct yes as [lap Hinlap yes].
      rewrite ExistsT_exists in yes.
      destruct yes as [ap Hinap Hap].
      destruct (ForallT_DerivCISR_sig DC Hap) as [ldt Hldt].
      destruct (Forall2_sig_l Hllap lap Hinlap) as [r [Hinr Hlap]].
      clear Hap. specialize (Hlap ap). destruct Hlap as [Hap _]. specialize (Hap Hinap).
      apply Forall2_and_inv in Hldt. destruct Hldt as [Hproup Hldt].
      apply Forall2_Forall_r in Hproup.
      apply Forall2_and_inv in Hldt. destruct Hldt as [Hconc Hldt].
      apply Forall2_flip in Hconc. rewrite Forall2_map_iff in Hconc.
      apply Forall2_eq_iff in Hconc. rewrite map_id in Hconc.
      apply Forall2_Forall_r in Hldt.
      apply Forall_and_inv in Hldt. destruct Hldt as [Hsrldt Hldt].
      apply Forall_and_inv in Hldt. destruct Hldt as [Hirrldt Hcontldt].
      do 3 (try unshelve eexists).
      exists (Der s r ldt). all: simpl; try tauto.
      + apply proper_Der; try assumption. rewrite Hconc. tauto.
      + unfold dtSemireduced. rewrite allDT_Der. split.
        apply Hsrls. assumption. rewrite Forall_fold_right in Hsrldt. assumption.
      + unfold irredundant. rewrite allDT_Der. split.
        * simpl. intro Hsin. apply seqInDTs_exDTs in Hsin.
          rewrite <- allDTs_Forall in Hcontldt.
          pose proof (allDTs_exDTs_and Hcontldt Hsin) as Hctr.
          apply exDTs_Exists, Exists_exists in Hctr. destruct Hctr as [dt [Hindt Hdt]].
          apply exDT_in_tree in Hdt. destruct Hdt as [d [Hind [Hinconcd Heqconcd]]].
          rewrite Heqconcd in Hinconcd. apply in_remove in Hinconcd. tauto.
        * apply allDTs_Forall. assumption.
      + split; try assumption. rewrite <- Forall_fold_right.
        eapply Forall_impl; try apply Hcontldt.
        intros dt Hdt. rewrite allDT_in_tree in Hdt. rewrite allDT_in_tree.
        intros d Hd. specialize (Hdt d Hd). apply (in_remove _ _ _ _ Hdt).
    - right. intro Hder. remember (der_dt DC) as dt.
      pose proof (der_proper DC) as Hpro. pose proof (der_concl DC) as Hconc.
      destruct dt. apply (not_proper_Unf s0 (rls:=DC)).
      rewrite Heqdt. apply der_proper. rewrite <- Heqdt in Hconc.
      simpl in Hconc. rewrite Hconc in Heqdt. clear Hconc.
      destruct (Forall2_sig_r Hllap r) as [lap [Hinlap Hlap]].
      rewrite <- Heqdt in Hpro. unfold proper in Hpro. simpl in Hpro. tauto.
      rewrite ForallT_forall in no.
      specialize (no lap Hinlap).
      rewrite ForallT_forall in no.
      specialize (no (map conclDT l)). rewrite ExistsT_exists in no.
      destruct no as [t Hint Hdert]. apply Hlap. split.
      + intros t Ht.
        apply in_map_inv_sig in Ht. destruct Ht as [dt [Hconcdt Hindt]].
        apply in_in_remove. pose proof (derisr_irredun DC) as Hirr.
        rewrite <- Heqdt in Hirr. apply allDT_root in Hirr. simpl in Hirr.
        intro Heq. contradict Hirr. rewrite <- Heq.
        constructor 1 with dt; try assumption. constructor 1. assumption.
        pose proof (dercisr_cont DC) as Hcont. rewrite <- Heqdt in Hcont.
        apply allDTUp in Hcont. rewrite Forall_forall in Hcont.
        specialize (Hcont dt Hindt). apply allDT_root in Hcont.
        simpl in Hcont. rewrite Hconcdt in Hcont. assumption.
      + rewrite <- Heqdt in Hpro. unfold proper in Hpro. simpl in Hpro. tauto.
      + apply Hdert. apply (DerivCISR_Up DC ls s Hder).
        rewrite <- Heqdt. assumption.
  Defined.
        
      
     
  Lemma red_Deriv_dec' : forall s, seqReduced s -> Deriv DC s + (Deriv DC s -> False).
  Proof.
    intros s Hreds. destruct (finite_seqSemireduced (subPR s)) as [ls Hls].
    destruct (DerivCISR_dec ls s) as [yes|no].
    - intros t Ht. apply Hls. assumption.
    - apply Hls. split; try (apply seq_red_semireduced; assumption).
      apply seqPR_subPR.
    - left. apply yes.
    - right. intro Hctr. apply no. apply (red_DerivISR _ Hreds) in Hctr.
      exists Hctr. pose proof (subPR_ppty _ (der_proper DC)) as H.
      apply (allDT_and_acc _ (dersr_semireduced DC)) in H.
      eapply allDT_impl; try apply H.
      intros dt Hdt. rewrite der_concl in Hdt. apply Hls; assumption.
  Defined.

  Lemma red_Deriv_dec : forall s, Deriv DC (reduc s) + (Deriv DC (reduc s) -> False).
  Proof.
    intro s. apply (red_Deriv_dec' (reduc s)). apply seq_red_reduc.
  Defined.

  Lemma Deriv_reduc_iff : forall s, Deriv DC (reduc s) <+> Deriv DC s.
  Proof.
    intro s. split.
    - intro Hdr. apply (Deriv_tran DC [reduc s] s).
      + constructor; try constructor. assumption.
      + apply set_eq_deriv. apply reduc_PR_set_eq.
    - intro Hdr. apply (Deriv_tran DC [s] _).
      + constructor; try constructor. assumption.
      + apply set_eq_deriv. apply set_eq_sym. apply reduc_PR_set_eq.
  Defined.
  
  Theorem Deriv_dec : forall s, Deriv DC s + (Deriv DC s -> False).
  Proof.
    intro s. destruct (red_Deriv_dec s) as [Hder|Hnder].
    - left. apply Deriv_reduc_iff. assumption.  
    - right. intro H. apply Hnder. apply Deriv_reduc_iff. assumption.
  Defined.


End Decidability.
