Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Require Import ListSetNotations.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.
Require Import CutElim.
Require Import Derivability.
Require Import BelnapAid.
Require Import PL.
Import CPLNotations.
Require Import Rules.
Require Import CPLRules.

Import CPLRules.

Definition cpldc : DISPCALC :=
  [atrefl; Iwr; Iaddl; Idell; Iwl; Comml; Contl; Assol; CUT;
   Topl; Topr; Botl; Botr; Negl; Negr; Conl; Conr; Disl; Disr; Impl; Impr;
   Mlrn; Mrrslln; Mrls; Snn; Sns; DSEr; Mrrn; Mlrsrln; Mlls].


Module CPLDeriv.

  Ltac set_XYZW :=
    set (X := $"X" : structr); set (Y := $"Y" : structr);
    set (Z := $"Z" : structr); set (W := $"W" : structr).

  #[export] Instance dernc_Sss : DerivRuleNC cpldc Sss.
  Proof.
    unfold Sss.
    apply_DRNC_inDC DSEr.
    apply_DRNC_inDC Sns.
    apply DerivRuleNC_refl.
  Defined.

  #[export] Instance dernc_DSEl : DerivRuleNC cpldc DSEl.
  Proof.
    set_XYZW.
    apply (Extend_DerivRuleNC _ Sss).
    set (d := Der (X ⊢ Y) Sss
             [Der (∗Y ⊢ ∗X) DSEr
             [Der (∗Y ⊢ ∗∗∗X) Snn
             [Unf ((∗∗X) ⊢ Y)]]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Ssn : DerivRuleNC cpldc Ssn.
  Proof.
    set (d := Der (∗ $"Y" ⊢ $"X") DSEr
             [Der (∗ $"Y" ⊢ ∗ ∗ $"X") Snn
             [Unf (∗ $"X" ⊢ $"Y")]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Sns : DerivRuleNC cpldc Sns.
  Proof.
    set_XYZW.
    apply (Extend_DerivRuleNC _ DSEl).
    set (d := Der (Y ⊢ ∗ X) DSEl
             [Der ((∗∗Y) ⊢ ∗X) Snn
             [Unf (X ⊢ ∗Y)]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Mrrs : DerivRuleNC cpldc Mrrs.
  Proof.
    set_XYZW.
    set (d := Der (X,, Z ⊢ Y) Mrls [Der (Z ⊢ ∗X,, Y) Mrrslln [Unf (X ⊢ Y,, ∗Z)] ]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Commr : DerivRuleNC cpldc Commr.
  Proof.
    set_XYZW.
    set (d := Der (X ⊢ Z,, Y) Mlls
             [Der (∗Z,, X ⊢ Y) Comml
             [Der (X,, ∗Z ⊢ Y) Mrrn
             [Unf (X ⊢ Y,, Z)]]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Mlln : DerivRuleNC cpldc Mlln.
  Proof.
    set_XYZW.
    apply (Extend_DerivRuleNC _ Commr).
    set (d := Der (Y ⊢ ∗X,, Z) Commr
             [Der (Y ⊢ Z,, ∗X) Mlrn
             [Der (Y,, X ⊢ Z) Comml
             [Unf (X,, Y ⊢ Z)]]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Assolinv : DerivRuleNC cpldc Assolinv.
  Proof.
    unfold Assolinv. set_XYZW.
    apply_DRNC_inDC Comml.
    apply_DRNC_inst Mrrs.
    apply_DRNC_inDC Comml.
    apply_DRNC_inDC Mlrn.
    apply_DRNC_inDC Assol.
    apply_DRNC_inDC Comml.
    apply_DRNC_inst Mrrs.
    apply_DRNC_inDC Comml.
    apply_DRNC_inDC Mlrn.
    apply DerivRuleNC_refl.
  Defined.

  #[export] Instance derr_Wkl : DerivRule cpldc Wkl.
  Proof.
    set_XYZW.
    apply (Extend_DerivRule _ Mrrs).
    confirm_derr (Der (Z,, X ⊢ Y) Mrrs
                 [Der (Z ⊢ Y,, ∗X) Iwl
                 [Der (I ⊢ Y,, ∗X) Mlrn
                 [Der (I,, X ⊢ Y) Iaddl
                 [Unf (X ⊢ Y)]]]]).
  Defined.

  #[export] Instance dernc_frefl : forall A : PL.formula, fmlNoFV A -> DerivRuleNC cpldc (frefl A).
  Proof.
    intros A H. induction A; try (contradict H; apply isVar_not_noVar; constructor).
    all: try (apply fmlNoFV_ipse in H; try (intros; discriminate)).
    all: try (specialize (IHA (Forall_inv H))).
    all: try (specialize (IHA1 (Forall_inv H));
              specialize (IHA2 (Forall_inv (Forall_inv_tail H)))).
    all: unfold frefl.
    - set (d := Der (£% p ⊢ £% p) atrefl []). confirm_derrnc d.
    - set (d := Der (£ PL.Top ⊢ £ PL.Top) Topl
               [Der (I ⊢ £ PL.Top) Topr []]).
      confirm_derrnc d.
    - set (d := Der (£ PL.Bot ⊢ £ PL.Bot) Botr
               [Der (£ PL.Bot ⊢ I) Botl []]).
      confirm_derrnc d.
    - apply_DRNC_inDC Negr.
      apply_DRNC_inDC Negl.
      apply_DRNC_inDC Snn.
      assumption.
    - apply_DRNC_inDC Impr.
      apply_DRNC_inDC Comml.
      apply_DRNC_inDC Mrls.
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
    apply_cof_inst Sss.
    apply_cof_CUT A.
    - apply_cof_inst Ssn. assumption.
    - apply_cof_inst Sns. assumption.
  Defined.


  Theorem C8_Con {X Y Z A B} : C8_case cpldc (X,, Y) Z
                                 [X ⊢ £A; Y ⊢ £B; £A,, £B ⊢ Z]
                                 (isipsubfml (A ∧ B)).
  Proof.
    prep_C8_case.
    apply_cof_inst Mrrs.
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC Mlrn.
    apply_cof_inDC Mrls.
    apply_cof_CUT B; [assumption|].
    apply_cof_inst Mlln.
    assumption.
  Defined.

  Theorem C8_Dis {X Y Z A B} : C8_case cpldc X (Y,, Z)
                                       [X ⊢ £A,, £B; £A ⊢ Y; £B ⊢ Z]
                                       (isipsubfml (A ∨ B)).
  Proof.
    prep_C8_case.
    apply_cof_inDC Mlls.
    apply_cof_CUT B; [|assumption].
    apply_cof_inDC Mlrsrln.
    apply_cof_CUT A; [|assumption].
    apply_cof_inDC Mrrn.
    assumption.
  Defined.

  Theorem C8_Imp {X Y Z A B} :
    C8_case cpldc X (∗Y,, Z) [Y ⊢ £A; X,, £A ⊢ £B; £B ⊢ Z] (isipsubfml (A → B)).
  Proof.
    prep_C8_case.
    apply_cof_inst Mlln.
    apply_cof_CUT B; [|assumption].
    apply_cof_inst Mrrs.
    apply_cof_CUT A; [assumption|].
    apply_cof_inDC Mlrn.
    apply_cof_inDC Comml.
    assumption.
  Defined.

  
  Theorem C8_holds : C8 cpldc.
  Proof.
    auto_C8.
    - remember (fst (fst afsR) "p") as p. rewrite HeqipsA in *.
      exists (Der (£ PL.Atf p ⊢ £ PL.Atf p) atrefl []). split.
      try (repeat (split; try auto_in; try auto_wfr)).
      rewrite HeqX, HeqY. split; try reflexivity.
      simpl. split; [left; discriminate|constructor].
    - exists dR. rewrite HeqX, HeqY. split; [|split]; try assumption.
      apply (allDT_impl _ _ (nocut_impl_cut (@isipsubfml _ _ f_pl A))).
      assumption.
    - exists dL. rewrite HeqX, HeqY. split; [|split]; try assumption.
      apply (allDT_impl _ _ (nocut_impl_cut (@isipsubfml _ _ f_pl A))).
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
