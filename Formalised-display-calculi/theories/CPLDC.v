Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Require Import ListSetNotations.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Llang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.
Require Import CutElim.
Require Import Derivability.
Require Import BelnapAid.
Require Import PL.
Import PLNotations.
Require Import Rules.
Require Import CPLRules.

Import CPLRules.

Definition cpldc : DISPCALC :=
  [atrefl; Iwr; Iaddl; Idell; Iwl; Comml; Contl; Assol; CUT;
   Topl; Topr; Botl; Botr; Negl; Negr; Conl; Conr; Disl; Disr; Impl; Impr;
   Mlrn; Mrrslln; Mrls; Snn; Sns; DSEr; Mrrn; Mlrsrln; Mlls].


Lemma MinDC_cpldc : incl MinDC cpldc.
Proof. forall_list_tauto. Qed.

Module CPLDeriv.

  Definition PLfml := PL.formula.
  Definition derPL := @dertree PLfml.
  Definition strPL := @structr PLfml.

  #[export] Instance dernc_Ssn : DerivRuleNC cpldc Ssn.
  Proof. apply (SubDC_dernc MinDC _ MinDC_cpldc _ dernc_Ssn). Defined.

  #[export] Instance dernc_Mrrs : DerivRuleNC cpldc Mrrs.
  Proof. apply (SubDC_dernc MinDC _ MinDC_cpldc _ dernc_Mrrs). Defined.

  #[export] Instance dernc_Sss : DerivRuleNC cpldc Sss.
  Proof. apply (SubDC_dernc MinDC _ MinDC_cpldc _ dernc_Sss). Defined.

  #[export] Instance dernc_DSEl : DerivRuleNC cpldc DSEl.
  Proof. apply (SubDC_dernc MinDC _ MinDC_cpldc _ dernc_DSEl). Defined.

  #[export] Instance dernc_Sns : DerivRuleNC cpldc Sns.
  Proof. apply (SubDC_dernc MinDC _ MinDC_cpldc _ dernc_Sns). Defined.

  #[export] Instance dernc_Commr : DerivRuleNC cpldc Commr.
  Proof. apply (SubDC_dernc MinDC _ MinDC_cpldc _ dernc_Commr). Defined.

  #[export] Instance dernc_Mlln : DerivRuleNC cpldc Mlln.
  Proof. apply (SubDC_dernc MinDC _ MinDC_cpldc _ dernc_Mlln). Defined.


  #[export] Instance dernc_frefl : forall A : PL.formula, fmlNoFV A -> DerivRuleNC cpldc (frefl A).
  Proof.
    intros A H. induction A; try contradiction.
    all: try (apply fmlNoFV_ipsubfmls in H; try (intros; discriminate)).
    all: try (specialize (IHA (Forall_inv H))).
    all: try (specialize (IHA1 (Forall_inv H));
              specialize (IHA2 (Forall_inv (Forall_inv_tail H)))).
    all: unfold frefl.
    - set (d := Der (£p p ⊢ £p p) atrefl []). confirm_derrnc d.
    - set (d := Der (£ PL.Top ⊢ £ PL.Top) Topl
               [Der (I ⊢ £ PL.Top) Topr []]).
      confirm_derrnc d.
    - set (d := Der (£ PL.Bot ⊢ £ PL.Bot) Botr
               [Der (£ PL.Bot ⊢ I) Botl []]).
      confirm_derrnc d.
    - apply_DRNC_inDC Negr.
      apply_DRNC_inDC Negl.
      apply_DRNC_inDC (@Snn PLfml).
      assumption.
    - apply_DRNC_inDC Impr.
      apply_DRNC_inDC (@Comml PLfml).
      apply_DRNC_inDC (@Mrls PLfml).
      apply_DRNC_inDC Impl; assumption.
    - apply_DRNC_inDC Disr.
      apply_DRNC_inDC Disl; assumption.
    - apply_DRNC_inDC Conl.
      apply_DRNC_inDC Conr; assumption.
  Defined.

  Import PL.
  #[export] Instance cpldc_derr_frefl : forall A : formula, fmlNoFV A -> DerivRule cpldc (frefl A).
  Proof. apply dernc_frefl. Defined.

End CPLDeriv.

Module CPLBelnap.

  Import CPLDeriv.

  Theorem has_CUT : In CUT cpldc.
  Proof. simpl. tauto. Qed.

  Theorem C3_holds : C3 cpldc.
  Proof. auto_C3. Qed.

  Theorem C4_holds : C4 cpldc.
  Proof. auto_C4. Qed.

  Theorem C5_holds : C5 cpldc.
  Proof. auto_C5. Qed.


  Theorem C8_Neg {X Y A} : C8_case cpldc X Y [X ⊢ ∗ £A; ∗ £A ⊢ Y] (isipsubfml (¬ A)).
  Proof.
    prep_C8_case.
    apply_cof_inst (@Sss PLfml).
    apply_cof_CUT A.
    - apply_cof_inst (@Ssn PLfml). assumption.
    - apply_cof_inst (@Sns PLfml). assumption.
  Defined.


  Theorem C8_Con {X Y Z A B} : C8_case cpldc (X,, Y) Z
                                 [X ⊢ £A; Y ⊢ £B; £A,, £B ⊢ Z]
                                 (isipsubfml (A ∧ B)).
  Proof.
    prep_C8_case.
    apply_cof_inst (@Mrrs PLfml).
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC (@Mlrn PLfml).
    apply_cof_inDC (@Mrls PLfml).
    apply_cof_CUT B; [assumption|].
    apply_cof_inst (@Mlln PLfml).
    assumption.
  Defined.

  Theorem C8_Dis {X Y Z A B} : C8_case cpldc X (Y,, Z)
                                       [X ⊢ £A,, £B; £A ⊢ Y; £B ⊢ Z]
                                       (isipsubfml (A ∨ B)).
  Proof.
    prep_C8_case.
    apply_cof_inDC (@Mlls PLfml).
    apply_cof_CUT B; [|assumption].
    apply_cof_inDC (@Mlrsrln PLfml).
    apply_cof_CUT A; [|assumption].
    apply_cof_inDC (@Mrrn PLfml).
    assumption.
  Defined.

  Theorem C8_Imp {X Y Z A B} :
    C8_case cpldc X (∗Y,, Z) [Y ⊢ £A; X,, £A ⊢ £B; £B ⊢ Z] (isipsubfml (A → B)).
  Proof.
    prep_C8_case.
    apply_cof_inst (@Mlln PLfml).
    apply_cof_CUT B; [|assumption].
    apply_cof_inst (@Mrrs PLfml).
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC (@Mlrn PLfml).
    apply_cof_inDC (@Comml PLfml).
    assumption.
  Defined.
  
  Theorem C8_holds : C8 cpldc.
  Proof.
    auto_C8 PL.formula.
    - remember (fst (fst afsR) "p") as p. rewrite HeqipsA in *.
      exists (Der (£ PL.Atf p ⊢ £ PL.Atf p) atrefl []). split.
      try (repeat (split; try auto_in; try auto_wfr)).
      rewrite HeqX, HeqY. split; try reflexivity.
      simpl. split; [left; discriminate|constructor].
    - exists dR. rewrite HeqX, HeqY. split; [|split]; try assumption.
      apply (allDT_impl (@nocut_impl_cut _ _ pl _ (@isipsubfml _ _ pl A))).
      assumption.
    - exists dL. rewrite HeqX, HeqY. split; [|split]; try assumption.
      apply (allDT_impl (@nocut_impl_cut _ _ pl _ (@isipsubfml _ _ pl A))).
      assumption.
    - rewrite HeqX, HeqY, HeqAR. rewrite H1 in *.
      apply (C8_Neg [dL; dR]); try auto_Forall.
      simpl. rewrite H, H0. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Con [dL; dL0; dR]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Dis [dL; dR; dR0]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
    - rewrite HeqX, HeqY, HeqAR. rewrite H2, H3 in *.
      apply (C8_Imp [dR; dL; dR0]); try auto_Forall.
      simpl. rewrite H, H0, H1. reflexivity.
  Defined.

End CPLBelnap.

#[export] Instance cpldcBel : BELNAP cpldc := {|
  has_CUT := CPLBelnap.has_CUT;
  C3_holds := CPLBelnap.C3_holds;
  C4_holds := CPLBelnap.C4_holds;
  C5_holds := CPLBelnap.C5_holds;
  C8_holds := CPLBelnap.C8_holds; |}.
