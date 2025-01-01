Require Import String.
Require Import Ensembles.
Require Import List.
Import ListNotations.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.
Require Import Derivability.
Require Import Rules.
Require Import PL.
Require Import CPLDC.
Require Import CPLRules.
Import CPLRules.

Open Scope string_scope.
Open Scope list_scope.
Close Scope nat_scope.



(* Proof that our display calculus for CPL is Hilbert-complete *)


Section BasicCalc.

  Context `{LL : LOGLANG}.

  Definition HCrule := list formula * formula.
  Definition HCpremsRule (r : HCrule) : list formula := fst r.
  Definition HCconclRule (r : HCrule) : formula := snd r.

End BasicCalc.


Definition HILBCALC `{LL : LOGLANG} := list (@HCrule formula).

Import CPLNotations.

Definition MP : HCrule := ([?"A"; ?"A" → ?"B"],
                            ?"B").

Definition CPLHC1 : HCrule := ([], ?"A" → (?"B" → ?"A")).
Definition CPLHC2 : HCrule := ([], (¬ ?"A" → ¬ ?"B") → (?"B" → ?"A")).
Definition CPLHC3 : HCrule := ([], (?"A" → (?"B" → ?"C")) →
                                     ((?"A" → ?"B") → (?"A" → ?"C"))).

Definition CPL_HC : @HILBCALC _ _ _ PL := [MP; CPLHC1; CPLHC2; CPLHC3].


Section HC_TO_DC.

  Definition fmltoseq (A : PL.formula) : sequent := I ⊢ FS A.

  Definition HCtoDC_rule (r : HCrule) : rule := 
    (map fmltoseq (HCpremsRule r), fmltoseq (HCconclRule r)).

  Definition HCtoDC (HC : HILBCALC) : DISPCALC := map HCtoDC_rule HC.

End HC_TO_DC.

Definition cplHilbComp (DC : DISPCALC) := SubDer (HCtoDC CPL_HC) DC.

Definition cplLr : DISPCALC := (CPL_DC ++ [refl]).

Definition ExtraDC : DISPCALC := [Ssn; Sns; Sss; DSEl; Commr; Mlln; Mrrs; Assolinv; Wkl].

#[export] Instance cplLr_MP : DerivRule cplLr (HCtoDC_rule MP).
Proof.
  unfold MP. set (A := ?"A"). set (B := ?"B").
  simpl. unfold fmltoseq.
  set (d := Der (I ⊢ £B) CUT
           [Unf (I ⊢ £(A → B));
            Der (£(A → B) ⊢ £B) Idell
              [Der (£(A → B),, I ⊢ £B) Comml
              [Der (I,, £(A → B) ⊢ £B) Mrls
              [Der (£(A → B) ⊢ ∗I,, £B) Impl
              [Unf (I ⊢ £A);
               Der (£B ⊢ £B) refl []]]]]]).
  confirm_derr d.
Defined.

Theorem cplLr_ExtraDC : DerivDC cplLr ExtraDC.
Proof.
  Import CPLDeriv.
  intros r Hr; dec_destruct_List_In (@eqdec rule _) r;
  rewrite Heq;
  apply (SubDC_DerivRule CPL_DC cplLr);
  try (unfold cplLr; apply incl_appl, incl_refl);
  apply (alr_DerivRule _ _).
Defined.

#[export] Instance cplLr_CPLHC1 : DerivRule cplLr (HCtoDC_rule CPLHC1).
Proof.
  unfold CPLHC1. set (A := ?"A"). set (B := ?"B").
  apply (Extend_DerivDC _ _ cplLr_ExtraDC).
  confirm_derr (Der (I ⊢ £(A → (B → A))) Impr
               [Der (I,, £A ⊢ £(B → A)) Comml
               [Der (£A,, I ⊢ £(B → A)) Iaddl                    
               [Der (£A ⊢ £(B → A)) Impr
               [Der (£A,, £B ⊢ £A) Comml
               [Der (£B,, £A ⊢ £A) Wkl
               [Der (£A ⊢ £A) refl []]]]]]]).
Defined.

#[export] Instance cplLr_CPLHC2 : DerivRule cplLr (HCtoDC_rule CPLHC2).
Proof.
  unfold CPLHC2. set (A := ?"A"). set (B := ?"B").
  apply (Extend_DerivDC _ _ cplLr_ExtraDC).
  set (d := Der (I ⊢ £((¬ A → ¬ B) → (B → A))) Impr
            [Der (I,, £(¬ A → ¬ B) ⊢ £(B → A)) Comml
            [Der (£(¬ A → ¬ B),, I ⊢ £(B → A)) Iaddl
            [Der (£(¬ A → ¬ B) ⊢ £(B → A)) Impr
            [Der (£(¬ A → ¬ B),, £B ⊢ £A) DSEr
            [Der (£(¬ A → ¬ B),, £B ⊢ ∗∗£A) Mrrs
            [Der (£(¬ A → ¬ B) ⊢ (∗∗£A),, ∗£B) Impl
            [Der (∗£A ⊢ £(¬ A)) Negr
            [Der (∗£A ⊢ ∗£A) Snn
            [Der (£A ⊢ £A) refl []]];
             Der (£(¬ B) ⊢ ∗£B) Negl
               [Der (∗£B ⊢ ∗£B) Snn
               [Der (£B ⊢ £B) refl []]]]]]]]]]).
  confirm_derr d.
Defined.

#[export] Instance cplLr_CPLHC3 : DerivRule cplLr (HCtoDC_rule CPLHC3).
Proof.
  unfold CPLHC3. set (A := ?"A"). set (B := ?"B"). set (C := ?"C").
  apply (Extend_DerivDC _ _ cplLr_ExtraDC).
  set (d :=  Der (I ⊢ £((A → (B → C)) → ((A → B) → (A → C)))) Impr
            [Der (I,, £(A → (B → C)) ⊢ £((A → B) → (A → C))) Comml
            [Der (£(A → (B → C)),, I ⊢ £((A → B) → (A → C))) Iaddl
            [Der (£(A → (B → C)) ⊢ £((A → B) → (A → C))) Impr
            [Der (£(A → (B → C)),, £(A → B) ⊢ £(A → C)) Impr
            [Der ((£(A → (B → C)),, £(A → B)),, £A ⊢ £C) Comml
            [Der (£A,, (£(A → (B → C)),, £(A → B)) ⊢ £C) Assolinv
            [Der ((£A,, £(A → (B → C))),, £(A → B) ⊢ £C) Comml
            [Der (£(A → B),, (£A,, £(A → (B → C))) ⊢ £C) Mrls
            [Der ((£A,, £(A → (B → C))) ⊢ ∗£(A → B),, £C) Mrrs
            [Der (£A ⊢ (∗£(A → B),, £C),, ∗£(A → (B → C))) Contl
            [Der (£A,, £A ⊢ (∗£(A → B),, £C),, ∗£(A → (B → C))) Mlrn
            [Der ((£A,, £A),, £(A → (B → C)) ⊢ ∗£(A → B),, £C) Assol
            [Der (£A,, (£A,, £(A → (B → C))) ⊢ ∗£(A → B),, £C) Mrls
            [Der (£A,, £(A → (B → C)) ⊢ ∗£A,, (∗£(A → B),, £C)) Mrls
            [Der (£(A → (B → C)) ⊢ ∗£A,, (∗£A,, (∗£(A → B),, £C))) Impl
            [Der (£A ⊢ £A) refl [];
             Der (£(B → C) ⊢ ∗£A,, (∗£(A → B),, £C)) Mlln
               [Der (£A,, £(B → C) ⊢ ∗£(A → B),, £C) Mlln
               [Der (£(A → B),, (£A,, £(B → C)) ⊢ £C) Assolinv
               [Der ((£(A → B),, £A),, £(B → C) ⊢ £C) Mrrs
               [Der (£(A → B),, £A ⊢ £C,, ∗£(B → C)) Comml
               [Der (£A,, £(A → B) ⊢ £C,, ∗£(B → C)) Mrls
               [Der (£(A → B) ⊢ ∗£A,, (£C,, ∗£(B → C))) Impl
               [Der (£A ⊢ £A) refl [];
                Der (£B ⊢ £C,, ∗£(B → C)) Mlrn
                  [Der (£B,, £(B → C) ⊢ £C) Mrls
                  [Der (£(B → C) ⊢ ∗£B,, £C) Impl
                  [Der (£B ⊢ £B) refl [];
                   Der (£C ⊢ £C) refl []]]]]]]]]]]]]]]]]]]]]]]]]]]).
  confirm_derr d.
  Defined.

Theorem CPL_DCHilbComp : SubDer (HCtoDC CPL_HC) (CPL_DC ++ [refl]).
Proof.
  apply DerivDC_SubDer. intros r Hr.
  unfold HCtoDC, CPL_HC, map in Hr.
  dec_destruct_List_In rule_eq_dec r; rewrite Heq; try apply (alr_DerivRule _ _).
Defined.
