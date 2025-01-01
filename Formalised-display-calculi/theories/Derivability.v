Require Import String.
Require Import Relations.
Require Import List ListDec SetoidList Decidable.
Import ListNotations.
Require Import ListSetNotations.
Require Import Datatypes.
Require Import Arith.
Require Import Bool.

Require Import EqDec.
Require Import Utils.
Require Import Tactics.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.

Open Scope list_scope.

Section Derivability.

  Context `{SL : STRLANG}.
  Context (DC : DISPCALC).

  (* Class versions of mutually inductive definitions
     deriv_seq, deriv_prseq, etc. *)

  Class Deriv (s : sequent) := {
    der_dt : dertree;
    der_proper : proper DC der_dt;
    der_concl : conclDT der_dt = s }.

  Class DerivRule (r : rule) := {
    derr_dt : dertree;
    derr_semiproper : semiproper DC derr_dt;
    derr_prems : premsDT derr_dt ⊆ premsRule r;
    derr_concl : conclDT derr_dt = conclRule r; }.

  Class DerivRuleNC (r : rule) := {
    derrnc_derr :: DerivRule r;
    derrnc_nocut : allDT nocut derr_dt; }.

  Definition DerivDC (DC' : DISPCALC) := forall r, r ∈ DC' -> DerivRule r.

  Lemma alr_DerivRule (r : rule) `{dr : DerivRule r} : DerivRule r.
  Proof. assumption. Defined.

  #[export] Instance derr_rules : forall r, r ∈ DC -> DerivRule r.
  Proof.
    intros r H.
    constructor 1 with (Der (conclRule r) r (map Unf (premsRule r))); [split| |].
    - split; try assumption.
      rewrite <- Forall_fold_right. apply Forall_forall.
      intros dt Hdt. destruct (in_map_inv_sig Hdt) as [s [Heq Hin] ].
      rewrite <- Heq. simpl. tauto.
    - simpl. split. exists I_afs. now rewrite map_map, map_id, I_afs_id_rule, surjective_pairing.
      rewrite <- Forall_fold_right. apply Forall_forall.
      intros dt Hdt. destruct (in_map_inv_sig Hdt) as [s [Heq Hin] ].
      rewrite <- Heq. simpl. tauto.
    - simpl. rewrite fold_right_map, map_map. simpl. rewrite <- fold_right_map.
      simpl. rewrite fold_right_cons. apply incl_refl.
    - reflexivity.
  Defined.

  #[export] Instance derrnc_rules : forall r, r ∈ remove_rule CUT DC -> DerivRuleNC r.
  Proof.
    intros r H. apply in_remove in H. destruct H as [H0 H1].
    constructor 1 with (derr_rules r H0).
    simpl. split; try assumption. rewrite <- Forall_fold_right. apply Forall_forall.
    intros dt Hdt. destruct (in_map_inv_sig Hdt) as [s [Heq Hin] ].
    rewrite <- Heq. simpl. tauto.
  Defined.

  Lemma ForallT_Deriv_sig :
    forall ls, ForallT Deriv ls ->
      ForallT (fun s => {dt | proper DC dt /\ conclDT dt = s}) ls.
  Proof.
    induction ls as [|s ls].
    - intros _. constructor.
    - intro H. inversion H. constructor.
      + destruct X as [dt]. exists dt. tauto.
      + apply IHls. assumption.
  Defined.

  Lemma ForallT_DerivRule_sig_gen :
    forall {l : list dertree} {f g}, ForallT (fun d => DerivRule (f d, g d)) l ->
    {ldt | Forall (semiproper DC) ldt /\
           Forall2 (fun d1 d2 => incl (premsDT d2) (f d1) /\ conclDT d2 = g d1) l ldt}.
  Proof.
    intros l f g Hder. induction l as [|dt l]; try (exists []; split; constructor).
    pose proof (ForallT_inv Hder) as Hderdt.
    pose proof (ForallT_inv_tail Hder) as Hderl.
    specialize (IHl Hderl). destruct IHl as [ldt Hldt].
    destruct Hderdt as [dt' Hsp Hconc Hprems].
    exists (dt' :: ldt). split; constructor; tauto.
  Defined.

  Lemma ForallT_DerivRule_sig :
    forall {prems ls}, ForallT (fun s => DerivRule (prems, s)) ls ->
    {ldt | Forall2 (fun s dt => semiproper DC dt /\ incl (premsDT dt) prems /\ conclDT dt = s) ls ldt}.
  Proof.
    intros prems ls Hder. induction ls as [|s ls]; try (exists []; constructor).
    pose proof (ForallT_inv Hder) as Hders.
    pose proof (ForallT_inv_tail Hder) as Hderls.
    specialize (IHls Hderls). destruct IHls as [ldt Hldt].
    destruct Hders as [dt Hsp Hprems Hconc].
    exists (dt :: ldt). constructor; try assumption. tauto.
  Defined.

  Lemma ForallT_DerivRuleNC_sig :
    forall {prems ls}, ForallT (fun s => DerivRuleNC (prems, s)) ls ->
    {ldt | Forall2 (fun s dt => semiproper DC dt /\ incl (premsDT dt) prems /\
                             conclDT dt = s /\ allDT nocut dt) ls ldt}.
  Proof.
    intros prems ls Hder. induction ls as [|s ls]; try (exists []; constructor).
    pose proof (ForallT_inv Hder) as Hders.
    pose proof (ForallT_inv_tail Hder) as Hderls.
    specialize (IHls Hderls). destruct IHls as [ldt Hldt].
    destruct Hders as [[dt Hsp Hprems Hconc] Hnc].
    exists (dt :: ldt). constructor; try assumption. tauto.
  Defined.

  Lemma Deriv_iff_deriv_seq (s : sequent) :
    Deriv s <+> deriv_seq DC s.
  Proof.
    split.
    - intros [dt Hprop Hconc]. rewrite <- Hconc. clear s Hconc.
      induction dt as [|s r l IH]; try (contradict Hprop; apply not_proper_Unf).
      pose proof (proper_up_Forall DC Hprop) as Hpropup. apply Forall_ForallT in Hpropup.
      apply (ForallT_mp Hpropup) in IH. apply proper_root in Hprop.
      simpl in Hprop. destruct Hprop as [Hexr Hwfr].
      apply (deriv_seq_ext _ _ _ _ Hexr Hwfr).
      apply ForallT_deriv_seqs. apply ForallT_map. assumption.
    - revert s. apply (deriv_seq_mut_rect _ (fun s => Deriv s) (fun ls => ForallT Deriv ls)).
      + intros ps c r Hexr Hwfr Hders HDers.
        apply ForallT_Deriv_sig, ForallT_sig_elim in HDers.
        destruct HDers as [ldt Hldt].
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hpro Hconc].
        apply Forall2_Forall_r in Hpro. apply Forall2_flip in Hconc.
        rewrite Forall2_map_iff in Hconc. apply Forall2_eq_iff in Hconc.
        rewrite map_id in Hconc. rewrite <- Hconc in Hwfr.
        exists (Der c r ldt). apply proper_Der; try assumption. reflexivity.
      + apply ForallT_nil.
      + intros c cs Hder HDer Hders HDers.
        apply ForallT_cons; assumption.
  Defined.

  Lemma Deriv_iff_deriv_prseq_nil (s : sequent) :
    Deriv s <+> deriv_prseq DC [] s.
  Proof.
    rewrite Deriv_iff_deriv_seq. apply deriv_seq_prseq_nil.
  Defined.


  Lemma ForallT_Deriv_iff_deriv_seq (ls : list sequent) :
    ForallT Deriv ls <+> ForallT (deriv_seq DC) ls.
  Proof.
    apply ForallT_act_iff. intro s. apply Deriv_iff_deriv_seq.
  Defined.

  Lemma ForallT_Deriv_iff_deriv_prseq_nil (ls : list sequent) :
    ForallT Deriv ls <+> ForallT (deriv_prseq DC []) ls.
  Proof.
    apply ForallT_act_iff. intro s. apply Deriv_iff_deriv_prseq_nil.
  Defined.

  Lemma ForallT_Deriv_iff_deriv_prseqs_nil (ls : list sequent) :
    ForallT Deriv ls <+> deriv_prseqs DC [] ls.
  Proof.
    rewrite ForallT_Deriv_iff_deriv_prseq_nil.
    apply ForallT_deriv_prseqs_iff.
  Defined.

  Lemma DerivRule_iff_deriv_rule (r : rule) :
    DerivRule r <+> deriv_rule DC r.
  Proof.
    destruct r as [ps c]. split.
    - intros [dt Hsp Hprems Hconc]. simpl in Hprems, Hconc.
      apply (deriv_prseq_weak _ (premsDT dt));
      try assumption. rewrite <- Hconc.
      clear ps c Hprems Hconc.
      induction dt as [|s r l IH].
      + apply deriv_prseq_prem. simpl. tauto.
      + pose proof (semiproperUp DC _ Hsp) as Hspup. apply Forall_ForallT in Hspup.
        apply (ForallT_mp Hspup) in IH. apply semiproper_root in Hsp.
        simpl in Hsp. destruct Hsp as [Hexr Hwfr].
        apply (deriv_prseq_ext _ _ _ _ _ Hexr Hwfr).
        apply ForallT_deriv_prseqs. apply ForallT_map.
        rewrite ForallT_forall in IH. apply ForallT_forall.
        intros dt Hdt. specialize (IH dt Hdt).
        eapply deriv_prseq_weak; try eassumption.
        apply (premsDTUp _ (premsDT (Der s r l)) (incl_refl _)).
        assumption.
    - revert c.
      apply (deriv_prseq_mut_rect _ _ (fun c => DerivRule (ps, c))
               (fun lc => ForallT (fun c => DerivRule (ps, c)) lc)).
      + intros c Hc. exists (Unf c); simpl;
          [apply semiproper_Unf|auto_incl|reflexivity].
      + intros cs c r Hexr Hwfr Hders HDers.
        apply ForallT_DerivRule_sig in HDers.
        destruct HDers as [ldt Hldt].
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hspup Hldt].
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hprems Hconc].
        apply Forall2_Forall_r in Hspup, Hprems. apply Forall2_flip in Hconc.
        rewrite Forall2_map_iff in Hconc. apply Forall2_eq_iff in Hconc.
        rewrite map_id in Hconc. rewrite <- Hconc in Hwfr.
        assert (semiproper DC (Der c r ldt)) as Hsp.
        { apply semiproper_Der; tauto. }
        exists (Der c r ldt); try apply Hsp; try reflexivity.
        rewrite premsDT_Der. apply Forall_incl_premsDTs. assumption.
      + apply ForallT_nil.
      + intros c cs Hder HDer Hders HDers.
        apply ForallT_cons; assumption.
  Defined.

  Lemma ForallT_DerivRule_iff_deriv_rule (lr : list rule) :
    ForallT DerivRule lr <+> ForallT (deriv_rule DC) lr.
  Proof.
    apply ForallT_act_iff. intro s. apply DerivRule_iff_deriv_rule.
  Defined.

  Lemma DerivRule_iff_deriv_prseq (ps : list sequent) (c : sequent) :
    DerivRule (ps, c) <+> deriv_prseq DC ps c.
  Proof. apply DerivRule_iff_deriv_rule. Defined.

  Lemma ForallT_DerivRule_iff_deriv_prseq (ps ls : list sequent) :
    ForallT (fun s => DerivRule (ps, s)) ls <+> ForallT (deriv_prseq DC ps) ls.
  Proof.
    apply ForallT_act_iff. intro s. apply DerivRule_iff_deriv_prseq.
  Defined.

  Lemma ForallT_DerivRule_iff_deriv_prseqs (ps ls : list sequent) :
    ForallT (fun s => DerivRule (ps, s)) ls <+> deriv_prseqs DC ps ls.
  Proof.
    rewrite ForallT_DerivRule_iff_deriv_prseq.
    apply ForallT_deriv_prseqs_iff.
  Defined.

  Lemma DerivDC_iff_ForallT_DerivRule (DC' : DISPCALC) :
    DerivDC DC' <+> ForallT DerivRule DC'.
  Proof.
    split. apply ForallT_forall. unfold DerivDC. apply ForallT_forall.
  Defined.

  Lemma DerivDC_iff_ForallT_deriv_rule (DC' : DISPCALC) :
    DerivDC DC' <+> ForallT (deriv_rule DC) DC'.
  Proof.
    rewrite DerivDC_iff_ForallT_DerivRule.
    apply ForallT_DerivRule_iff_deriv_rule.
  Defined.

  Lemma DerivRuleNC_iff_deriv_ncprseq (ps : list sequent) (c : sequent) :
    DerivRuleNC (ps, c) <+> deriv_ncprseq DC ps c.
  Proof.
    split.
    - intros [[dt Hsp Hprems Hconc] Hnc]. simpl in Hprems, Hconc, Hnc.
      apply (deriv_cofprseq_weak _ _ (premsDT dt));
      try assumption. rewrite <- Hconc.
      clear ps c Hprems Hconc.
      induction dt as [|s r l IH].
      + apply deriv_cofprseq_prem. simpl. tauto.
      + pose proof (semiproperUp DC _ Hsp) as Hspup. apply Forall_ForallT in Hspup.
        pose proof (allDTUp Hnc) as Hncup. apply Forall_ForallT in Hncup.
        apply (ForallT_mp Hspup) in IH.
        apply (ForallT_mp Hncup) in IH. apply semiproper_root in Hsp.
        simpl in Hsp. destruct Hsp as [Hexr Hwfr].
        apply (deriv_cofprseq_ext _ _ _ _ _ _ Hexr Hwfr); try (simpl in Hnc; tauto).
        apply ForallT_deriv_cofprseqs. apply ForallT_map.
        rewrite ForallT_forall in IH. apply ForallT_forall.
        intros dt Hdt. specialize (IH dt Hdt).
        eapply deriv_cofprseq_weak; try eassumption.
        apply (premsDTUp _ (premsDT (Der s r l)) (incl_refl _)).
        assumption.
    - revert c.
      apply (deriv_cofprseq_mut_rect _ _ _ (fun c => DerivRuleNC (ps, c))
               (fun lc => ForallT (fun c => DerivRuleNC (ps, c)) lc)).
      + intros c Hc. unshelve econstructor.
        exists (Unf c); simpl; [apply semiproper_Unf|auto_incl|reflexivity].
        simpl. exact Logic.I.
      + intros cs c r Hexr Hwfr Hcof Hders HDers.
        apply ForallT_DerivRuleNC_sig in HDers.
        destruct HDers as [ldt Hldt].
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hspup Hldt].
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hprems Hldt].
        apply Forall2_and_inv in Hldt. destruct Hldt as [Hconc Hnc].
        apply Forall2_Forall_r in Hspup, Hprems, Hnc. apply Forall2_flip in Hconc.
        rewrite Forall2_map_iff in Hconc. apply Forall2_eq_iff in Hconc.
        rewrite map_id in Hconc. rewrite <- Hconc in Hwfr.
        assert (semiproper DC (Der c r ldt)) as Hsp.
        { apply semiproper_Der; tauto. }
        unshelve econstructor.
        exists (Der c r ldt); try apply Hsp; try reflexivity.
        rewrite premsDT_Der. apply Forall_incl_premsDTs. assumption.
        simpl derr_dt. rewrite allDT_Der. rewrite allDTs_Forall.
        split; try assumption.
        destruct (eqdec r CUT) as [Heq|Hneq]; try assumption.
        destruct Hcof; try assumption.
        destruct H as (sl & sr & Y & A & H). tauto.
      + apply ForallT_nil.
      + intros c cs Hder HDer Hders HDers.
        apply ForallT_cons; assumption.
  Defined.

  Lemma Deriv_tran : forall ls s, ForallT Deriv ls -> DerivRule (ls, s) -> Deriv s.
  Proof.
    intros ls s HDers HDer.
    apply ForallT_Deriv_iff_deriv_prseqs_nil in HDers.
    apply DerivRule_iff_deriv_prseq in HDer.
    apply Deriv_iff_deriv_prseq_nil.
    eapply deriv_prseq_tran; eassumption.
  Defined.

  Corollary DerivRule_tran :
    forall ps ls c, ForallT (fun s => DerivRule (ps, s)) ls ->
            DerivRule (ls, c) -> DerivRule (ps, c).
  Proof.
    intros ps ls c HDers HDer.
    apply ForallT_DerivRule_iff_deriv_prseqs in HDers.
    apply DerivRule_iff_deriv_prseq in HDer.
    apply DerivRule_iff_deriv_prseq.
    eapply deriv_prseq_tran; eassumption.
  Defined.

  Lemma DerivRule_refl : forall c, DerivRule ([c], c).
  Proof.
    intro c. exists (Unf c); repeat split. apply incl_refl.
  Defined.
  
  Lemma DerivRuleNC_refl : forall c, DerivRuleNC ([c], c).
  Proof.
    intro c. unshelve econstructor.
    exists (Unf c); repeat split. apply incl_refl. apply Logic.I.
  Defined.

  Lemma DerivRule_Subst : forall r r', ruleInst r r' -> DerivRule r -> DerivRule r'.
  Proof.
    intros r r' Hinst Hder.
    apply DerivRule_iff_deriv_rule in Hder.
    apply DerivRule_iff_deriv_rule.
    revert Hinst Hder. apply deriv_rule_Inst.
  Defined.


End Derivability.


Section DerivRule.

  Context `{SL : STRLANG}.
  Context (DC : DISPCALC).

  #[export] Instance dernc_derremcut (r : rule) :
    DerivRuleNC DC r -> DerivRule (remove_rule CUT DC) r.
  Proof.
    intro H. constructor 1 with (derr_dt DC); try apply derrnc_derr.
    split. apply (allDT_impl (fun dt => exr DC dt /\ nocut dt)).
    intros dt [Hfrb Hnocut]. destruct dt; try tauto. apply in_in_remove; assumption.
    apply allDT_and. split. apply derrnc_derr. apply derrnc_nocut. apply derrnc_derr.
  Defined.

  Lemma derremcut_dernc (r : rule) :
    DerivRule (remove_rule CUT DC) r -> DerivRuleNC DC r.
    intro H. unshelve econstructor. constructor 1 with (derr_dt _);
      try split; try apply H.
    eapply allDT_impl. intro dt. eapply exr_subset. 2:{ apply H. }
    intros x Hx. apply in_remove in Hx. tauto.
    pose proof (proj1 (derr_semiproper _)) as Hexr.
    rewrite allDT_in_tree in Hexr. rewrite allDT_in_tree.
    intros d Hd. specialize (Hexr d Hd). destruct d; try tauto.
    apply in_remove in Hexr. tauto.
  Defined.

  Lemma dernc_derremcut_iff (r : rule) :
    DerivRuleNC DC r <+> DerivRule (remove_rule CUT DC) r.
  Proof.
    split; [apply dernc_derremcut|apply derremcut_dernc].
  Defined.

  Lemma DerivRule_rule_bw_Inst_expl (ps ss : list sequent) (c : sequent) (afs : afsSubst)
    (HDer : DerivRule DC (ss, c)) :
    ForallT (fun s => DerivRule DC (ps, seqSubst afs s)) ss -> DerivRule DC (ps, seqSubst afs c).
  Proof.
    intros HDers. apply DerivRule_iff_deriv_prseq in HDer.
    apply DerivRule_iff_deriv_prseq.
    unshelve eapply (deriv_prseq_tran_afs _ _ _ _ _ _ HDer).
    simpl. apply ForallT_deriv_prseqs_iff. apply ForallT_map.
    apply ForallT_forall. intros s Hs.
    rewrite ForallT_forall in HDers.
    rewrite <- DerivRule_iff_deriv_prseq. apply HDers. assumption.
  Defined.

  Lemma DerivRule_rule_bw_Inst (ps ss : list sequent) (c : sequent) (afs : afsSubst)
    {HDer : DerivRule DC (ss, c)} :
    ForallT (fun s => DerivRule DC (ps, seqSubst afs s)) ss -> DerivRule DC (ps, seqSubst afs c).
  Proof.
    apply DerivRule_rule_bw_Inst_expl. assumption.
  Defined.

  Lemma DerivRule_rule_bw_inDC (ps ss : list sequent) (c : sequent) (afs : afsSubst) :
    (ss, c) ∈ DC ->
    ForallT (fun s => DerivRule DC (ps, seqSubst afs s)) ss -> DerivRule DC (ps, seqSubst afs c).
  Proof.
    intro H. apply DerivRule_rule_bw_Inst_expl. apply derr_rules. assumption.
  Defined.

  Lemma deriv_cofseq_rule_bw_inDC (P : formula -> Prop) (ss : list sequent) (c : sequent) (afs : afsSubst) :
    (ss, c) ∈ DC ->
    (ss, c) <> CUT \/ (exists sl sr Y A, P A /\ map (seqSubst afs) ss = [sl; sr] /\ sr = FS A ⊢ Y) ->
    deriv_cofseqs DC P (map (seqSubst afs) ss) -> deriv_cofseq DC P (seqSubst afs c).
  Proof.
    intros Hexr Hcof Hders.
    apply (deriv_cofseq_ext _ _ (map (seqSubst afs) ss) (seqSubst afs c) (ss, c));
    try assumption. exists afs. reflexivity.
  Defined.

  Lemma deriv_cofseq_rule_bw_InstNC (P : formula -> Prop) (ss : list sequent) (c : sequent) (afs : afsSubst) {HDer : DerivRuleNC DC (ss, c)} :
    ForallT (deriv_cofseq DC P) (map (seqSubst afs) ss) -> deriv_cofseq DC P (seqSubst afs c).
  Proof.
    intro Hders. apply ForallT_deriv_cofseqs in Hders.
    eapply deriv_cofseq_tran_afs; try eassumption.
    apply DerivRuleNC_iff_deriv_ncprseq. assumption.
  Defined.

End DerivRule.

Section DerivRuleNC.

  Context `{SL : STRLANG}.
  Context (DC : DISPCALC).

  Lemma DerivRuleNC_rule_bw_Inst (ps ss : list sequent) (c : sequent) (afs : afsSubst)
    {HDer : DerivRuleNC DC (ss, c)} :
    ForallT (fun s => DerivRuleNC DC (ps, seqSubst afs s)) ss -> DerivRuleNC DC (ps, seqSubst afs c).
  Proof.
    intro HDers. apply dernc_derremcut_iff.
    eapply ForallT_act_iff in HDers.
    2:{ intro s. split. apply derremcut_dernc. apply dernc_derremcut. }
    rewrite dernc_derremcut_iff in HDer.
    revert HDer HDers. apply DerivRule_rule_bw_Inst_expl.
  Defined.

  Lemma DerivRuleNC_rule_bw_inDC (ps ss : list sequent) (c : sequent) (afs : afsSubst) :
    (ss,c) <> CUT -> (ss, c) ∈ DC ->
    ForallT (fun s => DerivRuleNC DC (ps, seqSubst afs s)) ss -> DerivRuleNC DC (ps, seqSubst afs c).
  Proof.
    intros Hnc Hin HDers. apply dernc_derremcut_iff.
    eapply ForallT_act_iff in HDers.
    2:{ intro s. split. apply derremcut_dernc. apply dernc_derremcut. }
    revert HDers. apply DerivRule_rule_bw_inDC.
    apply in_in_remove; assumption.
  Defined.

  Lemma DerivRuleNC_tran :
    forall prems ls conc, ForallT (fun s => DerivRuleNC DC (prems, s)) ls ->
            DerivRuleNC DC (ls, conc) -> DerivRuleNC DC (prems, conc).
  Proof.
    intros prems ls conc HDers HDer.
    eapply ForallT_act_iff in HDers.
    2:{ intro s. split. apply derremcut_dernc. apply dernc_derremcut. }
    apply dernc_derremcut in HDer. apply derremcut_dernc.
    revert HDers HDer. apply DerivRule_tran.
  Defined.

 
End DerivRuleNC.

Section SubDisp.
  
  Context `{SL : STRLANG}.
  Variables DC1 DC2 DC3 : DISPCALC.

  Definition SubDer := forall r, DerivRule DC1 r -> DerivRule DC2 r.

  Definition EqDer := forall r, DerivRule DC1 r <+> DerivRule DC2 r.

  Definition SubDerDC := forall DC, DerivDC DC1 DC -> DerivDC DC2 DC.

  Definition SubDerNC := forall r, DerivRuleNC DC1 r -> DerivRuleNC DC2 r.

  Lemma SubDer_SubDerDC : SubDer -> SubDerDC.
  Proof.
    intros H DC HDC r Hr. apply H, HDC. assumption.
  Defined.

  Lemma DerivDC_refl : DerivDC DC1 DC1.
  Proof.
    intros r Hr. apply derr_rules. assumption.
  Defined.

  Lemma DerivDC_app : DerivDC DC3 DC1 -> DerivDC DC3 DC2 -> DerivDC DC3 (DC1 ++ DC2).
  Proof.
    intros H1 H2 r Hr. apply in_app_iff in Hr.
    destruct (in_dec rule_eq_dec r DC1); try (apply H1; assumption).
    destruct (in_dec rule_eq_dec r DC2); try (apply H2; assumption).
    exfalso. destruct Hr; contradiction.
  Defined.

  Lemma SubDC_DerivDC : incl DC1 DC2 -> DerivDC DC2 DC1.
  Proof.
    intros H r Hr. apply H in Hr. apply derr_rules. assumption.
  Defined.

  Lemma SubDC_SubDer : DC1 ⊆ DC2 -> SubDer.
  Proof.
    intros Hsub r Hderncr. constructor 1 with (derr_dt DC1); try split;
      try apply Hderncr.
    eapply allDT_impl; try apply derr_exr.
    intro dt. apply exr_subset. eassumption. apply Hderncr.
  Defined.

  Lemma SubDC_SubDerDC : DC1 ⊆ DC2 -> SubDerDC.
  Proof.
    intro H. apply SubDer_SubDerDC, SubDC_SubDer. assumption.
  Defined.

  Lemma SubDC_DerivRule (r : rule) {dr : DerivRule DC1 r} :
    incl DC1 DC2 -> DerivRule DC2 r.
  Proof.
    intro H. apply SubDC_SubDer; assumption.
  Defined.

  Lemma SubDC_dernc : incl DC1 DC2 -> SubDerNC.
  Proof.
    intros Hsub r Hderncr. constructor 1 with (SubDC_SubDer Hsub r (derrnc_derr DC1)).
    apply Hderncr.
  Defined.


End SubDisp.

Section MoreSubDisp.

  Context `{SL : STRLANG}.

  Lemma DerivDC_SubDer (DC1 DC2 : DISPCALC) : DerivDC DC2 DC1 -> SubDer DC1 DC2.
  Proof.
    intros HdDC r Hr.
    apply DerivDC_iff_ForallT_deriv_rule in HdDC.
    apply DerivRule_iff_deriv_rule in Hr.
    apply DerivRule_iff_deriv_rule.
    revert HdDC Hr. apply deriv_rule_replace.
  Defined.

  Lemma DerivDC_SubDer_iff (DC1 DC2 : DISPCALC) : DerivDC DC2 DC1 <+> SubDer DC1 DC2.
  Proof.
    split. apply DerivDC_SubDer.
    intros Hder r Hr. apply Hder. apply derr_rules. assumption.
  Defined.

  Lemma double_SubDer_EqDer (DC1 DC2 : DISPCALC) :
    SubDer DC1 DC2 -> SubDer DC2 DC1 -> EqDer DC1 DC2.
  Proof.
    intros H1 H2 r. split. apply H1. apply H2.
  Defined.
  
  Lemma DerivDC_EqDer (DC1 DC2 : DISPCALC) :
    DerivDC DC1 DC2 -> DerivDC DC2 DC1 -> EqDer DC1 DC2.
  Proof.
    intros H1 H2. apply double_SubDer_EqDer; apply DerivDC_SubDer; assumption.
  Defined.

  Lemma Deriv_DerivRule_iff (DC : DISPCALC) :
    forall s, Deriv DC s <+> DerivRule DC ([], s).
  Proof.
    intro s. split.
    - intros [dt Hpro Hconc]. exists dt; try split; try apply Hpro; try assumption.
      simpl. destruct Hpro as [_ [_ H]].
      rewrite H. apply incl_refl.
    - intros [d Hspd Hpremsd Hconcd].
      simpl in Hconcd, Hpremsd. apply incl_l_nil in Hpremsd.
      exists d. unfold proper. unfold semiproper in Hspd. tauto. assumption.
  Defined.

  Corollary Extend_DerivDC (DC1 DC2 : DISPCALC) :
    DerivDC DC1 DC2 -> SubDer (DC1 ++ DC2) DC1.
  Proof.
    intro H. apply DerivDC_SubDer. apply DerivDC_app; [apply DerivDC_refl | assumption].
  Defined.

  Lemma DerivDC_one (DC : DISPCALC) (r : rule) :
    DerivRule DC r -> DerivDC DC [r].
  Proof.
    intros H x Hx. dec_destruct_List_In rule_eq_dec x. rewrite Heq. assumption.
  Defined.

  Theorem Extend_DerivRule (DC : DISPCALC) (r : rule)
    {dr : DerivRule DC r} : SubDer (DC ++ [r]) DC.
  Proof.
    apply Extend_DerivDC, DerivDC_one. assumption.
  Defined.

  Theorem Extend_DerivRule_expl (DC : DISPCALC) (r : rule) :
    DerivRule DC r -> SubDer (DC ++ [r]) DC.
  Proof.
    intro dr. apply Extend_DerivDC, DerivDC_one. assumption.
  Defined.

  Theorem Extend_DerivRuleNC (DC : DISPCALC) (r : rule)
    {dr : DerivRuleNC DC r} : SubDerNC (DC ++ [r]) DC.
  Proof.
    intros rho Hder.
    apply dernc_derremcut_iff in dr.
    apply dernc_derremcut_iff in Hder.
    apply dernc_derremcut_iff.
    unfold remove_rule in Hder. rewrite remove_app in Hder.
    unfold remove in Hder at 2.
    destruct (rule_eq_dec CUT r) as [Heq|Hneq].
    - rewrite app_nil_r in Hder. assumption.
    - revert Hder. apply Extend_DerivRule. assumption.
  Defined.

  Theorem Extend_DerivRuleNC_expl (DC : DISPCALC) (r : rule) :
    DerivRuleNC DC r -> SubDerNC (DC ++ [r]) DC.
  Proof.
    intro dr. apply Extend_DerivRuleNC. assumption.
  Defined.

End MoreSubDisp.  


(* Tactics to simplify proofs within the object logic *)

Ltac auto_wfr :=
  match goal with |- wfr (Der ?s ?r ?l) => now exists (rule_matchsub r (map conclDT l, s)) end.


Ltac auto_ruleInst :=
  match goal with
    |- ruleInst ?r ?r' => exists (rule_matchsub r r'); simpl; reflexivity
  end.


Ltac rewrite_all_conclDT ldt :=
  match ldt with
  | ?d :: ?l =>
      try (match goal with Heq : conclDT d = _ |- _ => rewrite Heq in * end);
      rewrite_all_conclDT l
  | [] => idtac
  end.

(* Automatically checks that a given dertree is a correct
   witness of a DerivRule r *)
Ltac confirm_derr dt :=
  try constructor 1 with dt; repeat split; try tauto;
    try (auto_in; fail); try (auto_wfr; fail);
    try reflexivity; try auto_incl.

(* Automatically checks that a given dertree is a correct
   witness of a DerivRuleNC r *)
Ltac confirm_derrnc dt :=
    unshelve econstructor;
    try constructor 1 with dt; repeat split; try tauto;
    try (auto_in; fail); try (auto_wfr; fail);
    try reflexivity; try auto_incl; try discriminate.


(* This makes sure eq_rect_r is always unfolded by the simpl tactic.
   Without it, the tactics below end up reducing terms to something huge. *)
Arguments eq_rect_r /.


(* Backward reasoning by applying display rules.
   inst = rule is not in the calculus but was proved derivable before
          (with an Instance of the relevant Class)
   inDC = the rule is already part of the calculus *)

Ltac apply_DR_inst r :=
  match goal with
    | |- DerivRule _ (?ps, ?c) =>
        change c with (seqSubst (seq_matchsub (conclRule r) c) (conclRule r));
        apply (DerivRule_rule_bw_Inst _ _ (premsRule r) (conclRule r)
                 (seq_matchsub (conclRule r) c));
        repeat (apply ForallT_cons); try (apply ForallT_nil);
        simpl
    end.

Ltac apply_DR_inDC r :=
  match goal with
    | |- DerivRule ?DC (?ps, ?c) =>
        change c with (seqSubst (seq_matchsub (conclRule r) c) (conclRule r));
        apply (DerivRule_rule_bw_inDC _ _ (premsRule r) (conclRule r)
                 (seq_matchsub (conclRule r) c)); [auto_in|];
        repeat (apply ForallT_cons); try (apply ForallT_nil);
        simpl
    end.

Ltac apply_DRNC_inst r :=
  match goal with
    | |- DerivRuleNC ?DC (?ps, ?c) =>
        change c with (seqSubst (seq_matchsub (conclRule r) c) (conclRule r));
        apply (DerivRuleNC_rule_bw_Inst _ _ (premsRule r) (conclRule r)
                 (seq_matchsub (conclRule r) c));
        repeat (apply ForallT_cons); try (apply ForallT_nil);
        simpl
    end.

Ltac apply_DRNC_inDC r :=
  match goal with
    | |- DerivRuleNC ?DC (?ps, ?c) =>
        change c with (seqSubst (seq_matchsub (conclRule r) c) (conclRule r));
        apply (DerivRuleNC_rule_bw_inDC _ _ (premsRule r) (conclRule r)
                 (seq_matchsub (conclRule r) c)); [discriminate|auto_in|];
        repeat (apply ForallT_cons); try (apply ForallT_nil);
        simpl
    end.


Ltac apply_cof_inDC r :=
  match goal with
    | |- deriv_cofseq ?DC ?P ?c =>
        change c with (seqSubst (seq_matchsub (conclRule r) c) (conclRule r));
        apply (deriv_cofseq_rule_bw_inDC _ _ (premsRule r) (conclRule r)
                 (seq_matchsub (conclRule r) c));
        [auto_in|left; discriminate|apply ForallT_deriv_cofseqs;
        repeat (apply ForallT_cons); try (apply ForallT_nil);
        simpl]
    end.


Ltac apply_cof_inst r :=
  match goal with
    | |- deriv_cofseq ?DC ?P ?c =>
        change c with (seqSubst (seq_matchsub (conclRule r) c) (conclRule r));
        apply (deriv_cofseq_rule_bw_InstNC _ _ (premsRule r) (conclRule r)
                 (seq_matchsub (conclRule r) c));
        repeat (apply ForallT_cons); try (apply ForallT_nil);
        simpl
    end.


(* Apply the cut rule when trying to prove derivability of a sequent
   satisfying a cutOnFmls. Parameter is the cut formula *)

Ltac apply_cof_CUT A :=
  match goal with
    | |- deriv_cofseq ?DC ?P (?X ⊢ ?Y) =>
        change (X ⊢ Y) with (seqSubst (CUT_spec A X Y) (conclRule CUT));
        apply (deriv_cofseq_rule_bw_inDC _ _ (premsRule CUT) (conclRule CUT) (CUT_spec A X Y));
        [auto_in|right;
        exists (seqSubst (CUT_spec A X Y) (SV "X" ⊢ FS (FV "A"))),
          (seqSubst (CUT_spec A X Y) (FS (FV "A") ⊢ SV "Y")), Y, A;
          repeat split; try (compute; tauto; fail)|simpl];
        apply ForallT_deriv_cofseqs;
        repeat (apply ForallT_cons); try (apply ForallT_nil)
    end.

