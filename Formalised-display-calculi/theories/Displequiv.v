Require Import String.
Open Scope string_scope.
Require Import List SetoidList.
Import ListNotations.
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
Require Import Deletion.
Require Import Reduction.

Require Import Rules.
Require Import PL.
Require Import CPLRules.
Import CPLRules.
Import CPLNotations.

Open Scope list_scope.

Import ListSetNotations.

Section Displequiv.

  Definition DE : DISPCALC :=
    [Mlrn; Mrrslln; Mrls; Snn; Sns; DSEr; Mrrn; Mlrsrln; Mlls; Comml; Assol].

  Definition MDE : DISPCALC :=
    [Mlln; Mlls; Mlrn; Mlrs; Mrln; Mrls; Mrrn; Mrrs; Snn; Sns; Ssn; Sss; DSEl; DSEr;
     DSIl; DSIr; Comml; Commr; Assol; Assolinv].

  Definition ICW : DISPCALC :=
    [Iaddl; Idell; Iaddr; Idelr; Wkl; Wkr; Contl; ContWkls; ContWkln].

  Definition MDEICW : DISPCALC := MDE ++ ICW.

  Ltac set_XYZW :=    
    set (X := $"X" : structr);
    set (Y := $"Y" : structr);
    set (Z := $"Z" : structr);
    set (W := $"W" : structr).

  #[export] Instance DE_Commr : DerivRule DE Commr.
  Proof.
    set_XYZW.
    set (d := Der (X ⊢ Z,, Y) Mlls
             [Der (∗Z,, X ⊢ Y) Comml
             [Der (X,, ∗Z ⊢ Y) Mrrn
             [Unf (X ⊢ Y,, Z)] ] ]).
    confirm_derr d.
  Defined.

  #[export] Instance DE_Mlln : DerivRule DE Mlln.
  Proof.
    apply (Extend_DerivRule _ Commr). set_XYZW.
    set (d := Der (Y ⊢ ∗X,, Z) Commr
             [Der (Y ⊢ Z,, ∗X) Mlrn [Der (Y,, X ⊢ Z) Comml [Unf (X,, Y ⊢ Z)]]]).
    confirm_derr d.
  Defined.

  #[export] Instance DE_Mlrs : DerivRule DE Mlrs.
  Proof.
    apply (Extend_DerivRule _ Commr). set_XYZW.
    set (d := Der (X ⊢ Z,, Y) Commr
             [Der (X ⊢ Y,, Z) Mlls
             [Der (∗Y,, X ⊢ Z) Comml
             [Unf (X,, ∗Y ⊢ Z)]]]).
    confirm_derr d.
  Defined.

  #[export] Instance DE_Mrln : DerivRule DE Mrln.
  Proof.
    apply (Extend_DerivRule _ Commr). set_XYZW.
    set (d := Der (∗Y,, X ⊢ Z) Comml
             [Der (X,, ∗Y ⊢ Z) Mrrn
             [Der (X ⊢ Z,, Y) Commr
             [Unf (X ⊢ Y,, Z)]]]).
    confirm_derr d.
  Defined.

  #[export] Instance DE_Mrrs : DerivRule DE Mrrs.
  Proof.
    apply (Extend_DerivRule _ Commr). set_XYZW.
    set (d := Der (X,, Z ⊢ Y) Comml
             [Der (Z,, X ⊢ Y) Mrls
             [Der (X ⊢ ∗Z,, Y) Commr
             [Unf (X ⊢ Y,, ∗Z)]]]).
    confirm_derr d.
  Defined.

  #[export] Instance DE_Ssn : DerivRule DE Ssn.
  Proof.
    set_XYZW.
    set (d := Der (∗Y ⊢ X) DSEr [Der (∗Y ⊢ (∗∗X)) Snn [Unf (∗X ⊢ Y)]]).
    confirm_derr d.
  Defined.

  #[export] Instance DE_Sss : DerivRule DE Sss.
  Proof.
    set_XYZW.
    set (d := Der (Y ⊢ X) DSEr [Der (Y ⊢ (∗∗X)) Sns [Unf (∗X ⊢ ∗Y)]]).
    confirm_derr d.
  Defined.

  #[export] Instance DE_DSEl : DerivRule DE DSEl.
  Proof.
    apply (Extend_DerivRule _ Sss). set_XYZW.
    set (d := Der (X ⊢ Y) Sss [Der (∗Y ⊢ ∗X) DSEr [Der (∗Y ⊢ ∗∗∗X) Snn [Unf ((∗∗X) ⊢ Y)]]]).
    confirm_derr d.
  Defined.

  #[export] Instance DE_DSIl : DerivRule DE DSIl.
  Proof.
    apply (Extend_DerivRule _ Ssn). set_XYZW.
    set (d := Der ((∗∗X) ⊢ Y) Ssn [Der (∗Y ⊢ ∗X) Snn [Unf (X ⊢ Y)]]).
    confirm_derr d.
  Defined.

  #[export] Instance DE_DSIr : DerivRule DE DSIr.
  Proof.
    set_XYZW.
    set (d := Der (X ⊢ ∗∗Y) Sns [Der (∗Y ⊢ ∗X) Snn [Unf (X ⊢ Y)]]).
    confirm_derr d.
  Defined.
  

  #[export] Instance DE_Assolinv : DerivRule DE Assolinv.
  Proof.
    apply (Extend_DerivRule _ Mrrs). set_XYZW.
    set (d := Der (X,, (Y,, Z) ⊢ W) Comml
             [Der ((Y,, Z),, X ⊢ W) Mrrs
             [Der (Y,, Z ⊢ W,, ∗X) Comml
             [Der (Z,, Y ⊢ W,, ∗X) Mlrn
             [Der ((Z,, Y),, X ⊢ W) Assol
             [Der (Z,, (Y,, X) ⊢ W) Comml
             [Der ((Y,, X),, Z ⊢ W) Mrrs
             [Der (Y,, X ⊢ W,, ∗Z) Comml
             [Der (X,, Y ⊢ W,, ∗Z) Mlrn
             [Unf ((X,, Y),, Z ⊢ W)]]]]]]]]]).
    confirm_derr d.
  Defined.

  #[export] Instance MDE_Mrrslln : DerivRule MDE Mrrslln.
  Proof.
    set_XYZW.
    set (d := Der (Z ⊢ ∗X,, Y) Mlln [Der (X,, Z ⊢ Y) Mrrs [Unf (X ⊢ Y,, ∗Z)]]).
    confirm_derr d.
  Defined.

  #[export] Instance MDE_Mlrsrln : DerivRule MDE Mlrsrln.
  Proof.
    set_XYZW.
    set (d := Der (∗Z,, X ⊢ Y) Mrln [Der (X ⊢ Z,, Y) Mlrs [Unf (X,, ∗Y ⊢ Z)]]).
    confirm_derr d.
  Defined.
    
  Lemma DE_eq_MDE : EqDer DE MDE.
  Proof.
    apply DerivDC_EqDer;
    intros r Hr; dec_destruct_List_In rule_eq_dec r; rewrite Heq;
      try (apply derr_rules; simpl; tauto);
      try apply (alr_DerivRule _ _).
  Defined.

  Definition displequiv (s t : sequent) := DerivRule MDE ([s], t).

  Lemma displequiv_refl (s : sequent) : displequiv s s.
  Proof. confirm_derr (Unf s). Defined.

  Lemma displequiv_tran (s t u : sequent) : displequiv s t -> displequiv t u -> displequiv s u.
  Proof.
    intros Hst Htu. eapply DerivRule_tran.
    constructor 2; try constructor 1.
    eassumption. assumption.
  Defined.

  Ltac confirm_derr_onerule r :=
    match goal with
      |- DerivRule _ ([?s], ?t) => confirm_derr (Der t r [Unf s])
    end.

  Ltac confirm_derr_displequiv_onerule r :=
    match goal with
      |- displequiv ?s ?t =>
        unfold displequiv; confirm_derr (Der t r [Unf s])
    end.

  Ltac confirm_derr_DE d :=
    match goal with
      |- displequiv ?s ?t =>
        unfold displequiv; apply DE_eq_MDE; confirm_derr d
    end.

  Ltac confirm_derr_DE_onerule r :=
    match goal with
      |- displequiv ?s ?t =>
        unfold displequiv; apply DE_eq_MDE; confirm_derr (Der t r [Unf s])
    end.

  Lemma ForallT_displequiv_deriv_prseqs :
    forall s ps, ForallT (displequiv s) ps <+> deriv_prseqs MDE [s] ps.
  Proof.
    intros s ps. split.
    - intro H. apply ForallT_deriv_prseqs.
      apply ForallT_forall.
      rewrite ForallT_forall in H.
      intros c Hc. apply DerivRule_iff_deriv_prseq.
      apply H. assumption.
    - intro H. apply ForallT_forall.
      intros c Hc. apply DerivRule_iff_deriv_prseq.
      apply ForallT_deriv_prseqs_iff in H.
      rewrite ForallT_forall in H. apply H. assumption.
  Defined.

  Lemma DE_rule_inversion :
    forall r r', r ∈ DE -> ruleInst r r' -> ForallT (displequiv (conclRule r')) (premsRule r').
  Proof.
    intros r r' Hr Hsub.
    dec_destruct_List_In rule_eq_dec r; rewrite Heq in Hsub;
      apply ruleInst_ruleSubst in Hsub; destruct Hsub as [pfs Hpfs]; rewrite Hpfs; simpl;
      set (X := snd pfs "X"); set (Y := snd pfs "Y");
      set (Z := snd pfs "Z"); set (W := snd pfs "W");
      constructor 2; try constructor 1; unfold displequiv.
    - confirm_derr_onerule Mrrs.
    - confirm_derr (Der (X ⊢ Y,, ∗ Z) Mlrn [Der (X,, Z ⊢ Y) Mrls [Unf (Z ⊢ ∗X,, Y)]]).
    - confirm_derr_onerule Mlln.
    - confirm_derr_onerule Sss.
    - confirm_derr_onerule Sns.
    - confirm_derr_onerule DSIr.
    - confirm_derr_onerule Mlrs.
    - confirm_derr (Der (X,, ∗ Y ⊢ Z) Mrrn [Der (X ⊢ Z,, Y) Mlls [Unf (∗Z,, X ⊢ Y)]]).
    - confirm_derr_onerule Mrln.
    - confirm_derr_onerule Comml.
    - confirm_derr_onerule Assolinv.
  Defined.

  Lemma DE_length_prems_one : forall r, r ∈ DE -> length (premsRule r) = 1.
  Proof.
    intros r Hr. destruct_List_In_name Hr; rewrite <- Hr0; reflexivity.
  Qed.

  Lemma DE_ruleInst_prems_sig :
    forall r ps c, r ∈ DE -> ruleInst r (ps, c) -> {s | ps = [s]}.
  Proof.
    intros r ps c Hexr Hwfr.
    pose proof (DE_length_prems_one _ Hexr) as Hlen.
    rewrite (ruleInst_length r _ Hwfr) in Hlen.
    simpl in Hlen. destruct_list_easy ps s.
    exists s. reflexivity.
  Defined.

  Lemma MDE_length_prems_one : forall r, r ∈ MDE -> length (premsRule r) = 1.
  Proof.
    intros r Hr. destruct_List_In_name Hr; rewrite <- Hr0; reflexivity.
  Qed.

  Lemma MDE_ruleInst_prems_sig :
    forall r ps c, r ∈ MDE -> ruleInst r (ps, c) -> {s | ps = [s]}.
  Proof.
    intros r ps c Hexr Hwfr.
    pose proof (MDE_length_prems_one _ Hexr) as Hlen.
    rewrite (ruleInst_length r _ Hwfr) in Hlen.
    simpl in Hlen. destruct_list_easy ps s.
    exists s. reflexivity.
  Defined.

  Lemma displequiv_sym (s t : sequent) : displequiv s t -> displequiv t s.
  Proof.
    intro de. apply DE_eq_MDE in de.
    apply DerivRule_iff_deriv_rule in de.
    apply DerivRule_iff_deriv_rule.
    revert t de.
    apply (deriv_prseq_mut_rect _ _ (fun t => deriv_prseq MDE [t] s)
             (fun lt => forall t, t ∈ lt -> deriv_prseq MDE [t] s)).
    - intros c Hc. apply in_singleton_eq in Hc. rewrite Hc.
      apply deriv_prseq_refl.
    - intros ps c r Hexr Hwfr Hderps Hders.
      destruct (DE_ruleInst_prems_sig _ _ _ Hexr Hwfr) as [t Heqps].
      rewrite Heqps in *.
      pose proof (DE_rule_inversion  _ _ Hexr Hwfr) as Hinv.
      simpl in Hinv. apply ForallT_displequiv_deriv_prseqs in Hinv.
      specialize (Hders t (or_introl eq_refl)).
      eapply deriv_prseq_tran; try eassumption.
    - contradiction.
    - intros c cs Hdersc Hdercs Hderscs Hdercss.
      intros t Ht. destruct (eqdec c t) as [Heq|Hneq];
      [|destruct (in_dec eqdec t cs) as [Hin|Hnin]].
      + rewrite <- Heq. assumption.
      + apply Hdercss. assumption.
      + exfalso. destruct Ht; contradiction.
  Defined.

  #[export] Instance MDE_Distl : DerivRule MDE Distl.
  Proof.
    set_XYZW.
    confirm_derr (Der (∗X,, ∗Y ⊢ Z) Mrrn
                 [Der (∗X ⊢ Z,, Y) Commr
                 [Der (∗X ⊢ Y,, Z) Mlrs
                 [Der (∗X,, ∗Z ⊢ Y) Mrln
                 [Der (∗Z ⊢ X,, Y) Ssn
                 [Unf (∗(X,, Y) ⊢ Z)]]]]]).
  Defined.

  #[export] Instance MDE_Factl : DerivRule MDE Factl.
  Proof.
    apply displequiv_sym. apply (alr_DerivRule _ _).
  Defined.

  #[export] Instance MDE_Distr : DerivRule MDE Distr.
  Proof.
    set_XYZW.
    confirm_derr (Der (X ⊢ ∗Y,, ∗Z) Mlrn
                 [Der (X,, Z ⊢ ∗Y) Comml
                 [Der (Z,, X ⊢ ∗Y) Mrrs
                 [Der (Z ⊢ ∗Y,, ∗X) Mlln
                 [Der (Y,, Z ⊢ ∗X) Sns
                 [Unf (X ⊢ ∗(Y,, Z))]]]]]).
  Defined.

  #[export] Instance MDE_Factr : DerivRule MDE Factr.
  Proof.
    apply displequiv_sym. apply (alr_DerivRule _ _).
  Defined.

  Lemma MDE_Dist_Fact : DerivDC MDE [Distl; Factl; Distr; Factr].
  Proof.
    intros r Hr. dec_destruct_List_In rule_eq_dec r;
      rewrite Heq; apply (alr_DerivRule _ _).
  Defined.         

  Lemma DE_rule_Comma_lant :
    forall r ps c V, r ∈ DE -> ruleInst r (ps, c) ->
        ForallT (fun s => displequiv (V,, antec s ⊢ succ s) (V,, antec c ⊢ succ c)) ps.
  Proof.
    intros r prems conc V Hr Hsub.
    dec_destruct_List_In rule_eq_dec r; rewrite Heq in Hsub;
      apply ruleInst_ruleSubst in Hsub; destruct Hsub as [pfs Hpfs];
      injection Hpfs; intros Hconc Hprems; rewrite Hconc, Hprems; simpl;
      set (X := snd pfs "X"); set (Y := snd pfs "Y");
      set (Z := snd pfs "Z"); set (W := snd pfs "W");
      constructor 2; try constructor 1; simpl.
    - confirm_derr (Der (V,, X ⊢ Z,, ∗ Y) Mlrn
                   [Der ((V,, X),, Y ⊢ Z) Assol
                   [Unf (V,, (X,, Y) ⊢ Z)]]).
    - confirm_derr (Der (V,, Z ⊢ ∗ X,, Y) Mlln
                   [Der (X,, (V,, Z) ⊢ Y) Assolinv
                   [Der ((X,, V),, Z ⊢ Y) Mrrs
                   [Der (X,, V ⊢ Y,, ∗Z) Comml
                   [Unf (V,, X ⊢ Y,, ∗ Z)]]]]).
    - confirm_derr (Der (V,, (Y,, X) ⊢ Z) Comml
                   [Der ((Y,, X),, V ⊢ Z) Assol
                   [Der (Y,, (X,, V) ⊢ Z) Mrls
                   [Der (X,, V ⊢ ∗ Y,, Z) Comml
                   [Unf (V,, X ⊢ ∗ Y,, Z)]]]]).
    - confirm_derr (Der (V,, ∗ Y ⊢ ∗ X) Comml
                   [Der (∗Y,, V ⊢ ∗ X) Mrln
                   [Der (V ⊢ Y,, ∗ X) Mlrn
                   [Unf (V,, X ⊢ Y)]]]).
    - confirm_derr (Der (V,, Y ⊢ ∗ X) Comml
                   [Der (Y,, V ⊢ ∗ X) Mrls
                   [Der (V ⊢ ∗ Y,, ∗ X) Mlrn
                   [Unf (V,, X ⊢ ∗ Y)]]]).
    - confirm_derr_displequiv_onerule DSEr.
    - confirm_derr (Der (V,, (X,, ∗ Z) ⊢ Y) Assolinv
                   [Der ((V,, X),, ∗ Z ⊢ Y) Mrrn
                   [Unf (V,, X ⊢ Y,, Z)]]).
    - confirm_derr (Der (V,, (∗ Z,, X) ⊢ Y) Mrls
                   [Der (∗ Z,, X ⊢ ∗ V,, Y) Comml
                   [Der (X,, ∗ Z ⊢ ∗ V,, Y) Mlln
                   [Der (V,, (X,, ∗ Z) ⊢ Y) Assolinv
                   [Der ((V,, X),, ∗ Z ⊢ Y) Comml
                   [Der (∗Z,, (V,, X) ⊢ Y) Mrln
                   [Der (V,, X ⊢ Z,, Y) Mlrs
                   [Der ((V,, X),, ∗ Y ⊢ Z) Assol
                   [Unf (V,, (X,, ∗ Y) ⊢ Z)]]]]]]]]).
    - confirm_derr (Der (V,, Y ⊢ X,, Z) Mlls
                   [Der (∗ X,, (V,, Y) ⊢ Z) Assolinv
                   [Der ((∗ X,, V),, Y ⊢ Z) Mrrs
                   [Der (∗ X,, V ⊢ Z,, ∗ Y) Comml
                   [Der (V,, ∗ X ⊢ Z,, ∗ Y) Mlrn
                   [Der ((V,, ∗ X),, Y ⊢ Z) Assol
                   [Unf (V,, (∗ X,, Y) ⊢ Z)]]]]]]).
    - confirm_derr (Der (V,, (Y,, X) ⊢ Z) Mrls
                   [Der (Y,, X ⊢ ∗ V,, Z) Comml
                   [Der (X,, Y ⊢ ∗ V,, Z) Mlln
                   [Unf (V,, (X,, Y) ⊢ Z)]]]).
    - confirm_derr (Der (V,, ((X,, Y),, Z) ⊢ W) Mrls
                   [Der ((X,, Y),, Z ⊢ ∗ V,, W) Assol
                   [Der (X,, (Y,, Z) ⊢ ∗ V,, W) Mlln
                   [Unf (V,, (X,, (Y,, Z)) ⊢ W)]]]).
  Defined.

  Theorem displequiv_Comma_lant : forall {X Y X' Y'} Z,
    displequiv (X ⊢ Y) (X' ⊢ Y') -> displequiv (Z,, X ⊢ Y) (Z,, X' ⊢ Y').
  Proof.
    intros X Y X' Y' Z de. apply DE_eq_MDE in de.
    destruct de as [dt Hsp Hprems Hconc].
    simpl in Hconc, Hprems. revert X Y X' Y' Hsp Hprems Hconc.
    induction dt as [s|s r l IH]; intros X Y X' Y' Hsp Hprems Hconc.
    - simpl in Hconc, Hprems. specialize (Hprems s (or_introl eq_refl)).
      dec_destruct_List_In sequent_eq_dec s.
      rewrite Heq in Hconc. injection Hconc.
      intros HeqY HeqX. rewrite HeqY, HeqX.
      apply displequiv_refl.
    - pose proof (semiproperUp _ _ Hsp) as Hspup.
      apply semiproper_root in Hsp. destruct Hsp as [Hexr Hwfr].
      destruct l. exfalso. simpl in Hexr, Hwfr. destruct_or_name Hexr;
        rewrite <- Hexr0 in Hwfr; destruct Hwfr; discriminate.
      apply ForallT_inv in IH.
      specialize (IH X Y (antec (conclDT d)) (succ (conclDT d))).
      eapply displequiv_tran; try apply IH.
      apply (Forall_inv Hspup).
      eapply premsDTUp; try eassumption. now left.
      destruct (conclDT d). reflexivity.
      simpl in Hconc. pose proof (f_equal antec Hconc) as Hants.
      pose proof (f_equal succ Hconc) as Hsucs.
      simpl in Hants, Hsucs. rewrite <- Hants, <- Hsucs.
      apply (ForallT_inv (DE_rule_Comma_lant r (conclDT d :: map conclDT l) s Z Hexr Hwfr)).
  Defined.

  Lemma displequiv_outstreduc_ant : forall X Y, displequiv (X ⊢ Y) (outstreduc X ⊢ Y).
  Proof.
    induction X as [X IH] using (wf_nat_ind strSize).
    destruct X; intro Y;
      try (simpl; apply displequiv_refl).
    destruct X; try (simpl; apply displequiv_refl).
    simpl. eapply displequiv_tran; [idtac | apply IH].
    confirm_derr_displequiv_onerule DSEl.
    simpl. lia.
  Defined.

  Lemma displequiv_star_similar_ant :
    forall X X' Y, outstreduc X = outstreduc X' -> displequiv (X ⊢ Y) (X' ⊢ Y).
  Proof.
    intros X X' Y Hstreq.
    eapply displequiv_tran; try apply displequiv_outstreduc_ant.
    rewrite Hstreq. apply displequiv_sym, displequiv_outstreduc_ant.
  Defined.

  Lemma displequiv_PR_sing_tostar_ant :
    forall {X Y sZ}, strPR true X = [sZ] -> displequiv (X ⊢ Y) (tostar sZ ⊢ Y).
  Proof.
    intros X Y sZ HPRX. apply displequiv_star_similar_ant.
    induction X as [X IH] using (wf_nat_ind strSize).
    destruct X; simpl in HPRX;
      try (injection HPRX; intro Heq; rewrite <- Heq; reflexivity).
    - destruct X; simpl in HPRX;
        try (injection HPRX; intro Heq; rewrite <- Heq; reflexivity).
      + simpl. apply IH; try (simpl; lia). assumption.
      + pose proof (nb_PR_ge1 X1 false). pose proof (nb_PR_ge1 X2 false).
        apply (f_equal (@length sstructr)) in HPRX.
        rewrite app_length in HPRX. simpl in HPRX. lia.
    - pose proof (nb_PR_ge1 X1 true). pose proof (nb_PR_ge1 X2 true).
      apply (f_equal (@length sstructr)) in HPRX.
      rewrite app_length in HPRX. simpl in HPRX. lia.
  Defined.

  Lemma displequiv_PR_sing_eq_ant :
    forall {X X' Y} sZ, strPR true X = [sZ] -> strPR true X' = [sZ] -> displequiv (X ⊢ Y) (X' ⊢ Y).
  Proof.
    intros X X' Y sZ HPRX HPRX'.
    eapply displequiv_tran; [apply (displequiv_PR_sing_tostar_ant HPRX) | idtac].
    apply displequiv_sym. apply displequiv_PR_sing_tostar_ant. assumption.
  Defined.

  Lemma displequiv_star_tog_ant : forall {X Y}, displequiv (∗X ⊢ Y) (tog X ⊢ Y).
  Proof.
    intros X Y. apply displequiv_star_similar_ant.
    destruct X; reflexivity.
  Defined.

  Lemma displequiv_outstreduc_suc : forall X Y, displequiv (X ⊢ Y) (X ⊢ outstreduc Y).
  Proof.
    induction Y as [Y IH] using (wf_nat_ind strSize).
    destruct Y;
      try (simpl; apply displequiv_refl).
    destruct Y; try (simpl; apply displequiv_refl).
    simpl. eapply displequiv_tran; [idtac | apply IH].
    confirm_derr_DE_onerule DSEr.
    simpl. lia.
  Defined.

  Lemma displequiv_star_similar_suc :
    forall X Y Y', outstreduc Y = outstreduc Y' -> displequiv (X ⊢ Y) (X ⊢ Y').
  Proof.
    intros X Y Y' Hstreq.
    eapply displequiv_tran; try apply displequiv_outstreduc_suc.
    rewrite Hstreq. apply displequiv_sym, displequiv_outstreduc_suc.
  Defined.

  Lemma displequiv_PR_sing_tostar_suc :
    forall {X Y sZ}, strPR true Y = [sZ] -> displequiv (X ⊢ Y) (X ⊢ tostar sZ).
  Proof.
    intros X Y sZ HPRY. apply displequiv_star_similar_suc.
    induction Y as [Y IH] using (wf_nat_ind strSize).
    destruct Y; simpl in HPRY;
      try (injection HPRY; intro Heq; rewrite <- Heq; reflexivity).
    - destruct Y; simpl in HPRY;
        try (injection HPRY; intro Heq; rewrite <- Heq; reflexivity).
      + simpl. apply IH; try (simpl; lia). assumption.
      + pose proof (nb_PR_ge1 Y1 false). pose proof (nb_PR_ge1 Y2 false).
        apply (f_equal (@length sstructr)) in HPRY.
        rewrite app_length in HPRY. simpl in HPRY. lia.
    - pose proof (nb_PR_ge1 Y1 true). pose proof (nb_PR_ge1 Y2 true).
      apply (f_equal (@length sstructr)) in HPRY.
      rewrite app_length in HPRY. simpl in HPRY. lia.
  Defined.

  Lemma displequiv_PR_sing_eq_suc :
    forall {X Y Y' sZ}, strPR true Y = [sZ] -> strPR true Y' = [sZ] -> displequiv (X ⊢ Y) (X ⊢ Y').
  Proof.
    intros X Y Y' sZ HPRY HPRY'.
    eapply displequiv_tran; [apply (displequiv_PR_sing_tostar_suc HPRY) | idtac].
    apply displequiv_sym. apply displequiv_PR_sing_tostar_suc. assumption.
  Defined.

  Lemma displequiv_tostar_sws_star_ant :
    forall {sX Y}, displequiv (tostar (sws sX) ⊢ Y) (∗ tostar sX ⊢ Y).
  Proof.
    intros [b X] Y. apply displequiv_star_similar_ant.
    destruct b; destruct X; reflexivity.
  Defined.

  Lemma displequiv_tostar_star_sws_ant :
    forall {sX Y}, displequiv (∗ tostar sX ⊢ Y) (tostar (sws sX) ⊢ Y).
  Proof.
    intros. apply displequiv_sym, displequiv_tostar_sws_star_ant.
  Defined.
  
  Lemma displequiv_tog_star_ant :
    forall {X Y}, displequiv (tog X ⊢ Y) (∗X ⊢ Y).
  Proof.
    intros X Y. apply displequiv_star_similar_ant.
    destruct X; reflexivity.
  Defined.

  Theorem DE_rule_Starred :
    forall r prems conc, r ∈ DE -> ruleInst r (prems, conc) ->
        ForallT (fun s => displequiv (∗ antec s ⊢ ∗ succ s) (∗ antec conc ⊢ ∗ succ conc)) prems.
  Proof.
    intros r prems conc Hr Hsub.
    dec_destruct_List_In rule_eq_dec r; rewrite Heq in Hsub;
      apply ruleInst_ruleSubst in Hsub; destruct Hsub as [pfs Hpfs];
      injection Hpfs; intros Hconc Hprems; rewrite Hconc, Hprems; simpl;
      set (X := snd pfs "X"); set (Y := snd pfs "Y");
      set (Z := snd pfs "Z"); set (W := snd pfs "W");
      constructor 2; try constructor 1; simpl;
      apply (Extend_DerivDC _ _ MDE_Dist_Fact).
    - confirm_derr (Der (∗X ⊢ ∗(Z,, ∗Y)) Factr
                   [Der (∗X ⊢ ∗Z,, ∗∗Y) Mlrn
                   [Der (∗X,, ∗Y ⊢ ∗Z) Distl
                   [Unf (∗(X,, Y) ⊢ ∗Z)]]]).
    - confirm_derr (Der (∗Z ⊢ ∗(∗X,, Y)) Factr
                   [Der (∗Z ⊢ (∗∗X),, ∗Y) Mlln
                   [Der (∗X,, ∗Z ⊢ ∗Y) Mrrs
                   [Der (∗X ⊢ ∗Y,, ∗∗Z) Distr
                   [Unf (∗X ⊢ ∗(Y,, ∗Z))]]]]).
    - confirm_derr (Der (∗(Y,, X) ⊢ ∗Z) Factl
                   [Der (∗Y,, ∗X ⊢ ∗Z) Mrls
                   [Der (∗X ⊢ (∗∗Y),, ∗Z) Distr
                   [Unf (∗X ⊢ ∗(∗Y,, Z))]]]).
    - confirm_derr_onerule Snn.
    - confirm_derr_onerule Sns.
    - confirm_derr_onerule DSEr.
    - confirm_derr (Der (∗(X,, ∗Z) ⊢ ∗Y) Factl
                   [Der (∗X,, (∗∗Z) ⊢ ∗Y) Mrrn
                   [Der (∗X ⊢ ∗Y,, ∗Z) Distr
                   [Unf (∗X ⊢ ∗(Y,, Z))]]]).
    - confirm_derr (Der (∗(∗Z,, X) ⊢ ∗Y) Factl
                   [Der ((∗∗Z),, ∗X ⊢ ∗Y) Mrln
                   [Der (∗X ⊢ ∗Z,, ∗Y) Mlrs
                   [Der (∗X,, (∗∗Y) ⊢ ∗Z) Distl
                   [Unf (∗(X,, ∗Y) ⊢ ∗Z)]]]]).
    - confirm_derr (Der (∗Y ⊢ ∗(X,, Z)) Factr
                   [Der (∗Y ⊢ ∗X,, ∗Z) Mlls
                   [Der ((∗∗X),, ∗Y ⊢ ∗Z) Distl
                   [Unf (∗(∗X,, Y) ⊢ ∗Z)]]]).
    - confirm_derr (Der (∗(Y,, X) ⊢ ∗Z) Factl
                   [Der (∗Y,, ∗X ⊢ ∗Z) Comml
                   [Der (∗X,, ∗Y ⊢ ∗Z) Distl
                   [Unf (∗(X,, Y) ⊢ ∗Z)]]]).
    - confirm_derr (Der (∗((X,, Y),, Z) ⊢ ∗W) Factl
                   [Der (∗(X,, Y),, ∗Z ⊢ ∗W) Mrrn
                   [Der (∗(X,, Y) ⊢ ∗W,, Z) Factl
                   [Der (∗X,, ∗Y ⊢ ∗W,, Z) Mlrs
                   [Der ((∗X,, ∗Y),, ∗Z ⊢ ∗W) Assol
                   [Der (∗X,, (∗Y,, ∗Z) ⊢ ∗W) Mrln
                   [Der (∗Y,, ∗Z ⊢ X,, ∗W) Distl
                   [Der (∗(Y,, Z) ⊢ X,, ∗W) Mlls
                   [Der (∗X,, ∗(Y,, Z) ⊢ ∗W) Distl
                   [Unf (∗(X,, (Y,, Z)) ⊢ ∗W)]]]]]]]]]).
  Defined.

  Theorem displequiv_Star :
    forall X Y X' Y', displequiv (X ⊢ Y) (X' ⊢ Y') -> displequiv (∗X ⊢ ∗Y) (∗X' ⊢ ∗Y').
  Proof.
    intros X Y X' Y' de. apply DE_eq_MDE in de.
    destruct de as [dt Hsp Hprems Hconc].
    simpl in Hconc, Hprems. revert X Y X' Y' Hsp Hprems Hconc.
    induction dt as [s|s r l IH]; intros X Y X' Y' Hsp Hprems Hconc.
    - simpl in Hconc, Hprems. specialize (Hprems s (or_introl eq_refl)).
      dec_destruct_List_In sequent_eq_dec s.
      rewrite Heq in Hconc. injection Hconc.
      intros HeqY HeqX. rewrite HeqY, HeqX.
      apply displequiv_refl.
    - pose proof (semiproperUp _ _ Hsp) as Hspup.
      apply semiproper_root in Hsp. destruct Hsp as [Hexr Hwfr].
      destruct l. exfalso. simpl in Hexr, Hwfr. destruct_or_name Hexr;
        rewrite <- Hexr0 in Hwfr; destruct Hwfr; discriminate.
      apply ForallT_inv in IH.
      specialize (IH X Y (antec (conclDT d)) (succ (conclDT d))).
      eapply displequiv_tran; try apply IH.
      apply (Forall_inv Hspup).
      eapply premsDTUp; try eassumption. now left.
      destruct (conclDT d). reflexivity.
      simpl in Hconc. pose proof (f_equal antec Hconc) as Hants.
      pose proof (f_equal succ Hconc) as Hsucs.
      simpl in Hants, Hsucs. rewrite <- Hants, <- Hsucs.
      apply (ForallT_inv (DE_rule_Starred r (conclDT d :: map conclDT l) s Hexr Hwfr)).
  Defined.


  Lemma detach_prim_ant : forall X Y sZ, isPrim (snd sZ) ->
      bstrNiso X sZ = true -> displequiv (X ⊢ Y) (tostar sZ,, strDel X sZ ⊢ Y).
  Proof.
    induction X; intros Y sZ HprsZ Hniso; try discriminate.
    - simpl. simpl in Hniso. specialize (IHX (∗Y) (sws sZ) (isPrim_sws _ HprsZ) Hniso).
      apply displequiv_Star in IHX.
      apply (displequiv_tran _ (∗X ⊢ (∗∗Y))). confirm_derr_displequiv_onerule DSIr.
      eapply displequiv_tran; try apply IHX.
      apply (displequiv_tran _ (∗ tostar (sws sZ) ⊢ Y,, strDel X (sws sZ))).
      apply (Extend_DerivRule _ Distl).
      confirm_derr (Der (∗ tostar (sws sZ) ⊢ Y,, strDel X (sws sZ)) Mlrs
                      [Der (∗ tostar (sws sZ),, ∗ strDel X (sws sZ) ⊢ Y) DSEr
                         [Der (∗ tostar (sws sZ),, ∗ strDel X (sws sZ) ⊢ ∗ (∗ Y)) Distl
                            [Unf (∗ (tostar (sws sZ),, strDel X (sws sZ)) ⊢ ∗ (∗ Y))]]]).
      apply (displequiv_tran _ (tostar sZ ⊢ Y,, strDel X (sws sZ))).
      apply (displequiv_PR_sing_eq_ant sZ);
        simpl; rewrite PR_tostar_eq; simpl; try (rewrite sws_invol);
        try reflexivity; try (apply isPrim_sws); assumption.
      apply (displequiv_tran _ (∗ strDel X (sws sZ) ⊢ ∗ tostar sZ,, Y)).
      confirm_derr (Der (∗ strDel X (sws sZ) ⊢ ∗ tostar sZ,, Y) Mlln
                         [Der (tostar sZ,, ∗ strDel X (sws sZ) ⊢ Y) Mrrn
                            [Unf (tostar sZ ⊢ Y,, strDel X (sws sZ))]]).
      eapply displequiv_tran. apply displequiv_star_tog_ant.
      confirm_derr_DE_onerule Mrls.
    - simpl in Hniso |- *.
      destruct (bstrSub X1 sZ) eqn:HsubX1;
        [destruct (bstrNiso X1 sZ) eqn:HnisoX1 |
         destruct (bstrSub X2 sZ) eqn:HsubX2; [destruct (bstrNiso X2 sZ) eqn:HnisoX2 | idtac]].
      + apply (displequiv_tran _ (X1 ⊢ Y,, ∗ X2));
          [idtac | apply (displequiv_tran _ (tostar sZ,, strDel X1 sZ ⊢ Y,, ∗ X2))].
        * confirm_derr_displequiv_onerule Mlrn.
            (*confirm_derr (Der (X1 ⊢ Y,, ∗ X2) Mlrn [Unf (X1,, X2 ⊢ Y)]).*)
        * apply IHX1; assumption.
        * confirm_derr (Der (tostar sZ,, (strDel X1 sZ,, X2) ⊢ Y) Assolinv
                             [Der ((tostar sZ,, strDel X1 sZ),, X2 ⊢ Y) Mrrs
                                [Unf (tostar sZ,, strDel X1 sZ ⊢ Y,, ∗ X2)]]).
      + pose proof (isoprim_unique_t _ _ HprsZ HsubX1 HnisoX1) as HPRX1.
        apply (displequiv_tran _ (X1 ⊢ Y,, ∗ X2));
          [idtac | apply (displequiv_tran _ (tostar sZ ⊢ Y,, ∗ X2))].
        * confirm_derr_DE_onerule Mlrn.
        * apply displequiv_PR_sing_tostar_ant. assumption.
        * confirm_derr_displequiv_onerule Mrrs.
      + eapply displequiv_tran; try eapply displequiv_Comma_lant.
        apply IHX2. eassumption. assumption.
        confirm_derr (Der (tostar sZ,, (X1,, strDel X2 sZ) ⊢ Y) Assolinv
                           [Der ((tostar sZ,, X1),, strDel X2 sZ ⊢ Y) Mrrs
                              [Der (tostar sZ,, X1 ⊢ Y,, ∗ strDel X2 sZ) Comml
                                 [Der (X1,, tostar sZ ⊢ Y,, ∗ strDel X2 sZ) Mlrn
                                    [Der ((X1,, tostar sZ),, strDel X2 sZ ⊢ Y) Assol
                                       [Unf (X1,, (tostar sZ,, strDel X2 sZ) ⊢ Y)]]]]]).
      + pose proof (isoprim_unique_t _ _ HprsZ HsubX2 HnisoX2) as HPRX2.
        apply (displequiv_tran _ (X2 ⊢ Y,, ∗X1)).
        confirm_derr_DE (Der (X2 ⊢ Y,, ∗X1) Mlrn
                           [Der (X2,, X1 ⊢ Y) Comml
                              [Unf (X1,, X2 ⊢ Y)]]).
        eapply displequiv_tran; [apply (displequiv_PR_sing_tostar_ant HPRX2) | idtac].
        confirm_derr_displequiv_onerule Mrrs.        
      + discriminate.
  Defined.

  Lemma detach_prim_suc : forall X Y sZ, isPrim (snd sZ) ->
      bstrNiso Y sZ = true -> displequiv (X ⊢ Y) (X ⊢ tostar sZ,, strDel Y sZ).
  Proof.
    intros X Y sZ HprsZ Hniso.
    apply (displequiv_tran _ (∗ Y ⊢ ∗ X) _).
    confirm_derr_DE_onerule Snn.
    eapply (displequiv_tran).
    apply (detach_prim_ant _ _ _ (isPrim_sws _ HprsZ)). simpl.
    rewrite sws_invol. assumption.
    simpl. rewrite sws_invol.
    apply (displequiv_tran _ (tostar (sws sZ) ⊢ ∗ X,, ∗ tog (strDel Y sZ))).
    confirm_derr_DE_onerule Mlrn.
    eapply displequiv_tran; try apply displequiv_tostar_sws_star_ant.
    apply (displequiv_tran _ (tog (strDel Y sZ) ⊢ tostar sZ,, ∗X)).
    confirm_derr (Der (tog (strDel Y sZ) ⊢ tostar sZ,, ∗ X) Mlls
                       [Der (∗ tostar sZ,, tog (strDel Y sZ) ⊢ ∗X) Mrrs
                          [Unf (∗ tostar sZ ⊢ ∗ X,, ∗ tog (strDel Y sZ))]]).
    eapply displequiv_tran; try apply displequiv_tog_star_ant.
    confirm_derr (Der (X ⊢ tostar sZ,, strDel Y sZ) Commr
                       [Der (X ⊢ strDel Y sZ,, tostar sZ) Mlls
                          [Der (∗ strDel Y sZ,, X ⊢ tostar sZ) Mrrs
                             [Unf (∗ strDel Y sZ ⊢ tostar sZ,, ∗ X)]]]).
  Defined.

  Lemma detach_prim :
    forall s sZ, sZ ∈ PR s -> bseqComma s = true ->
              {X' & {Y' & displequiv s (tostar (sws sZ),, X' ⊢ Y')}}.
  Proof.
    intros [X Y] sZ HinsZ HC. pose proof (seqPR_isPrim _ HinsZ) as HprsZ.
    destruct (in_dec sstructr_eq_dec sZ (strPR false X)) as [HinsZX|HninsZX];
      [destruct (bstrComma X) eqn:HCX |
       destruct (in_dec sstructr_eq_dec sZ (strPR true Y)) as [HinsZY|HninsZY];
        try (simpl in HinsZ; rewrite in_app_iff in HinsZ;
             exfalso; destruct HinsZ; contradiction); destruct (bstrComma Y) eqn:HCY].
    - exists (strDel X (sws sZ)), Y.
      rewrite <- (sws_invol sZ) in HinsZX.
      pose proof (strPR_niso _ HinsZX HCX) as HnisoX.
      apply detach_prim_ant; try assumption.
      apply isPrim_sws. assumption.
    - exists (∗ strDel Y (hdPR true Y)), (tostar (hdPR true Y)).
      apply in_PR_sw_iff in HinsZX. simpl in HinsZX.
      apply isPrim_sws in HprsZ.
      pose proof (in_strPR_sub_t _ _ HinsZX) as HsubX.
      pose proof (primComma_iso _ _ HprsZ HsubX HCX) as HnisoX.
      apply (displequiv_tran _ (tostar (sws sZ) ⊢ Y));
      [apply displequiv_PR_sing_tostar_ant | idtac].
      fold (id (sws sZ)). fold (swsc true (sws sZ)).
      apply (isoprim_unique); assumption.
      eapply displequiv_tran;
        [apply (detach_prim_suc _ Y (hdPR true Y)) |
         confirm_derr_DE_onerule Mrrn].
      apply hdPR_isPrim.
      eapply strPR_niso_t. apply hdPR_in_PR.
      destruct (bstrComma Y) eqn:HCY; try reflexivity.
      simpl in HC. rewrite HCX, HCY in HC. discriminate.
    - exists X, (strDel Y sZ).
      pose proof (strPR_niso_t HinsZY HCY) as HnisoY.
      eapply displequiv_tran; [apply detach_prim_suc | idtac]; try eassumption.
      apply (displequiv_tran _ (∗ tostar sZ ⊢ strDel Y sZ,, ∗X)).
      confirm_derr (Der (∗ tostar sZ ⊢ strDel Y sZ,, ∗ X) Mlrn
                         [Der (∗ tostar sZ,, X ⊢ strDel Y sZ) Mrln
                            [Unf (X ⊢ tostar sZ,, strDel Y sZ)]]).
      eapply displequiv_tran; try apply displequiv_tostar_star_sws_ant.
      confirm_derr_displequiv_onerule Mrrs.
    - exists (∗ tostar (hdPR true (∗X))), (strDel (∗X) (hdPR true (∗X))).
      apply (displequiv_tran _ (∗Y ⊢ ∗X)).
      confirm_derr_DE_onerule Snn.
      apply isPrim_sws in HprsZ.
      apply in_PR_sw in HinsZY. simpl in HinsZY.
      change (strPR false Y) with (strPR true (∗Y)) in HinsZY.
      pose proof (in_strPR_sub_t _ _ HinsZY) as HsubY.
      pose proof (primComma_iso _ _ HprsZ HsubY HCY) as HnisoY.
      pose proof (isoprim_unique_t _ _ HprsZ HsubY HnisoY) as HPRY.
      eapply displequiv_tran.
      apply (displequiv_PR_sing_tostar_ant HPRY).
      eapply displequiv_tran.
      apply (detach_prim_suc _ (∗X) (hdPR true (∗X))).
      apply hdPR_isPrim.
      apply orb_prop in HC. destruct HC as [HCX|HCY'];
        [idtac | rewrite HCY in HCY'; discriminate].
      apply strPR_niso_t. apply hdPR_in_PR. assumption.
      confirm_derr (Der (tostar (sws sZ),, ∗ tostar (hdPR true (∗ X))
                              ⊢ strDel (∗ X) (hdPR true (∗ X))) Comml
                         [Der (∗ tostar (hdPR true (∗ X)),, tostar (sws sZ)
                                 ⊢ strDel (∗ X) (hdPR true (∗ X))) Mrln
                            [Unf (tostar (sws sZ)
                                    ⊢ tostar (hdPR true (∗ X)),,
                                    strDel (∗ X) (hdPR true (∗ X)))]]).
  Defined.

  Theorem induction_from_rank (s:nat) : forall P : nat -> Type, P s ->
    (forall n, n >= s -> P n -> P (S n)) -> forall n, n >= s -> P n.
  Proof.
    intros P base IS. induction n.
    - intro H. apply Arith_prebase.le_n_0_eq_stt in H.
      rewrite H. assumption.
    - intro H. destruct (le_lt_eq_dec _ _ H) as [sltSn|seqSn].
      + apply IS; try lia. apply IHn. lia.
      + rewrite <- seqSn. assumption.
  Defined.

  Lemma MDE_mset_eq :
    forall r r', r ∈ MDE -> ruleInst r r' ->
        Forall (fun s => PR s ≡ PR (conclRule r')) (premsRule r').
  Proof.
    intros r r' Hr Hsub.
    dec_destruct_List_In rule_eq_dec r; rewrite Heq in Hsub;
      apply ruleInst_ruleSubst in Hsub; destruct Hsub as [pfs Hpfs];
      rewrite Hpfs; simpl;
      set (X := snd pfs "X"); set (Y := snd pfs "Y");
      set (Z := snd pfs "Z"); set (W := snd pfs "W");
      constructor 2; try constructor 1; simpl; try aac_reflexivity.
  Qed.


  Theorem displequiv_mset_eq : forall s t, displequiv s t -> PR s ≡ PR t.
  Proof.
    intros s t [dt Hsp Hprems Hconc].
    simpl in Hconc, Hprems. rewrite <- Hconc. clear Hconc t.
    revert Hsp Hprems.
    induction dt as [s0|s0 r l IH]; intros Hsp Hprems.
    - simpl in Hprems |- *. specialize (Hprems s0 (or_introl eq_refl)).
      destruct Hprems as [Heq|]; try contradiction.
      rewrite Heq. apply mset_eq_refl.
    - pose proof (semiproperUp _ _ Hsp) as Hspup.
      apply semiproper_root in Hsp.
      destruct Hsp as [Hexr Hwfr].
      apply (Forall_mp Hspup) in IH.
      apply (Forall_mp (premsDTUp_Forall _ _ Hprems)) in IH.
      simpl in IH.
      destruct l. exfalso. simpl in Hexr, Hwfr. destruct_or_name Hexr;
        rewrite <- Hexr0 in Hwfr; destruct Hwfr; discriminate.
      simpl. eapply mset_eq_tran; try apply (Forall_inv IH).
      apply (Forall_inv (MDE_mset_eq r _ Hexr Hwfr)).
  Qed.

  Lemma displequiv_all_mset_eq :
    forall s t, displequiv s t -> deriv_rule_P MDE (fun u => PR u ≡ PR s) ([s], t).
  Proof.
    intros s t Hder. apply DerivRule_iff_deriv_rule in Hder.
    revert t Hder. apply (deriv_prseq_mut_rect _ _ _
                           (fun lt => deriv_prseqs_P MDE (fun u => PR u ≡ PR s) [s] lt)).
    - intros c Hc. apply in_singleton_eq in Hc. rewrite Hc.
      constructor; [now left|apply mset_eq_refl].
    - intros ps c r Hexr Hwfr Hderps HderPps.
      apply (deriv_prseq_P_ext _ _ _ ps c r); try assumption.
      destruct (MDE_ruleInst_prems_sig _ _ _ Hexr Hwfr) as [t Heqps].
      rewrite Heqps in *. apply (mset_eq_tran _ (PR t)).
      + pose proof (MDE_mset_eq _ _ Hexr Hwfr) as Hmeq.
        simpl in Hmeq. rewrite Forall_forall in Hmeq.
        specialize (Hmeq t (or_introl eq_refl)).
        apply mset_eq_sym. assumption.
      + pose proof (deriv_prseqs_P_concl_P _ _ _ _ HderPps) as HP.
        specialize (HP t (or_introl eq_refl)). assumption.
    - apply deriv_prseqs_P_nil.
    - intros. apply deriv_prseqs_P_cons; assumption.
  Defined.     


  Lemma eq_seqPR_length_2_displequiv :
    forall s t, length (PR s) = 2 -> PR s = PR t -> displequiv s t.
  Proof.
    intros s t Hlen HeqPRt.
    destruct (PR s) as [|sX l] eqn:HeqPRs; try discriminate.
    destruct l as [|sY l]; try discriminate.
    destruct l; try discriminate.
    destruct s as [X1 Y1] eqn:Heqs. destruct t as [X2 Y2] eqn:Heqt.
    simpl in HeqPRs, HeqPRt.
    pose proof (nb_PR_ge1 X1 false) as HlenX1.
    pose proof (nb_PR_ge1 X2 false) as HlenX2.
    pose proof (nb_PR_ge1 Y1 true) as HlenY1.
    pose proof (nb_PR_ge1 Y2 true) as HlenY2.
    destruct (strPR false X1) as [|sX1 lX1] eqn:HeqPRX1; try (simpl in HlenX1; lia).
    destruct (strPR true Y1) as [|sY1 lY1] eqn:HeqPRY1; try (simpl in HlenY1; lia).
    destruct (strPR false X2) as [|sX2 lX2] eqn:HeqPRX2; try (simpl in HlenX2; lia).
    destruct (strPR true Y2) as [|sY2 lY2] eqn:HeqPRY2; try (simpl in HlenY2; lia).
    destruct lX1; destruct lY1;
      try (apply (f_equal (@length sstructr)) in HeqPRs; simpl in HeqPRs; try lia;
           rewrite ! app_length in HeqPRs; simpl in HeqPRs; lia).
    injection HeqPRs. intros HeqY1sY HeqX1sX.
    destruct lX2; destruct lY2;
      try (apply (f_equal (@length sstructr)) in HeqPRt; simpl in HeqPRt; try lia;
           rewrite ! app_length in HeqPRt; simpl in HeqPRt; lia).
    injection HeqPRt. intros HeqY2sY HeqX2sX.
    rewrite HeqY1sY, HeqX1sX, HeqY2sY, HeqX2sX in *.
    apply PR_PR_negb_eq_imp in HeqPRX1, HeqPRX2. simpl in HeqPRX1, HeqPRX2.
    eapply displequiv_tran. apply (displequiv_PR_sing_eq_ant _ HeqPRX1 HeqPRX2).
    apply (displequiv_PR_sing_eq_suc HeqPRY1 HeqPRY2).
  Defined.
  

  Lemma seqPR_eq_len_2 :
    forall (X Y : structr) sX sY,
      PR (X ⊢ Y) = [sX; sY] -> strPR false X = [sX] /\ strPR true Y = [sY].
  Proof.
    intros X Y sX sY HeqPR. simpl in HeqPR.
    pose proof (nb_PR_ge1 X false) as HlenX.
    pose proof (nb_PR_ge1 Y true) as HlenY.
    destruct (strPR false X) as [|sX' lX] eqn:HeqPRX; try (simpl in HlenX; lia).
    destruct (strPR true Y) as [|sY' lY] eqn:HeqPRY; try (simpl in HlenY; lia).
    destruct lX; destruct lY;
      try (apply (f_equal (@length sstructr)) in HeqPR; simpl in HeqPR; try lia;
           rewrite ! app_length in HeqPR; simpl in HeqPR; lia).
    injection HeqPR. intros HeqsY HeqsX.
    rewrite HeqsX, HeqsY. tauto.
  Qed.
    
    
   
  Theorem mset_eq_PR_displequiv :
    forall s t, PR s ≡ PR t -> displequiv s t.
  Proof.
    intros s t. pose proof (nb_seqPR_ge2 s) as Hn.
    remember (length (PR s)) as n.
    revert s t Heqn. pattern n. revert n Hn.
    apply (induction_from_rank 2); try assumption.
    - intros s t Hlen Heqst.
      destruct (PR s) as [|sX l] eqn:HeqPRs; try discriminate.
      destruct l as [|sY l]; try discriminate.
      destruct l; try discriminate.
      destruct s as [X1 Y1] eqn:Heqs. destruct t as [X2 Y2] eqn:Heqt.
      pose proof HeqPRs as HeqPRs'. simpl in HeqPRs'.
      pose proof (nb_PR_ge1 X1 false) as HlenX1.
      pose proof (nb_PR_ge1 X2 false) as HlenX2.
      pose proof (nb_PR_ge1 Y1 true) as HlenY1.
      pose proof (nb_PR_ge1 Y2 true) as HlenY2.
      destruct (strPR false X1) as [|sX1 lX1] eqn:HeqPRX1; try (simpl in HlenX1; lia).
      destruct (strPR true Y1) as [|sY1 lY1] eqn:HeqPRY1; try (simpl in HlenY1; lia).
      destruct lX1; destruct lY1;
        try (apply (f_equal (@length sstructr)) in HeqPRs'; simpl in HeqPRs'; try lia;
             rewrite ! app_length in HeqPRs'; simpl in HeqPRs'; lia).
      injection HeqPRs'. intros HeqY1sY HeqX1sX.      
      destruct (list_eq_dec sstructr_eq_dec (PR t) [sX; sY]) as [HeqPRt|HneqPRt];
        [idtac | destruct (list_eq_dec sstructr_eq_dec (PR t) [sY; sX]) as [HeqPRt'|HneqPRt']].
      + apply eq_seqPR_length_2_displequiv.
        rewrite HeqPRs. reflexivity.
        rewrite Heqt in HeqPRt. rewrite HeqPRs, HeqPRt. reflexivity.
      + apply (displequiv_tran _ (∗Y1 ⊢ ∗X1)).
        confirm_derr_DE_onerule Snn.
        apply eq_seqPR_length_2_displequiv.
        simpl. rewrite HeqPRY1, HeqPRX1. reflexivity.
        simpl. rewrite Heqt in HeqPRt'.
        apply seqPR_eq_len_2 in HeqPRt'.
        destruct HeqPRt' as [HeqPRX2 HeqPRY2].
        rewrite HeqPRX1, HeqPRY1, HeqPRX2, HeqPRY2, HeqY1sY, HeqX1sX.
        reflexivity.
      + exfalso. apply mset_eq_length_2_inv in Heqst.
        rewrite Heqt in HneqPRt, HneqPRt'.
        destruct Heqst; contradiction.
    - intros n Hn IH s t Hlen Heqst.
      destruct (detach_prim s (hdseqPR s)) as [X1 [Y1 Hdes]].
      apply hdseqPR_in_seqPR.
      apply seqgt2_Comma. lia.
      destruct (detach_prim t (hdseqPR s)) as [X2 [Y2 Hdet]].
      apply (mset_eq_set_eq Heqst), hdseqPR_in_seqPR.
      apply seqgt2_Comma. rewrite <- (mset_eq_length _ _ Heqst). lia.
      eapply displequiv_tran; try apply Hdes.
      eapply displequiv_tran;
        [eapply displequiv_Comma_lant | apply displequiv_sym, Hdet].
      apply IH.
      + apply displequiv_mset_eq, mset_eq_length in Hdes.
        simpl in Hdes |- *. rewrite <- app_assoc, app_length in Hdes.
        rewrite PR_tostar_eq in Hdes. simpl in Hdes. lia.
        apply isPrim_sws, hdseqPR_isPrim.
      + apply displequiv_mset_eq in Hdes, Hdet.
        apply mset_eq_sym in Hdes.
        apply (mset_eq_tran _ _ _ Hdes) in Heqst.
        apply (mset_eq_tran _ _ _ Heqst) in Hdet.
        simpl in Hdet |- *. rewrite <- ! app_assoc in Hdet.
        apply mset_eq_app_inv_l in Hdet. assumption.
  Defined.

  Theorem mset_eq_PR_Deriv_MDE_mset_eq :
    forall s t, PR s ≡ PR t -> deriv_rule_P MDE (fun u => PR u ≡ PR s) ([s], t).
  Proof.
    intros s t H. apply displequiv_all_mset_eq.
    apply mset_eq_PR_displequiv. assumption.
  Defined.

End Displequiv.
