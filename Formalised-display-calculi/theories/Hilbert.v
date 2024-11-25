Require Import String.
Require Import Ensembles.
Require Import List.
Import ListNotations.

Require Import Tactics.
Require Import Utils.
Require Import Llang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.
Require Import Derivability.
Require Import Rules.
Require Import PL.
Import PLNotations.
Require Import CPLDC.
Require Import CPLRules.
Import CPLRules.

Open Scope string_scope.
Open Scope list_scope.
Close Scope nat_scope.



(* Proof that our display calculus for CPL is Hilbert-complete *)


Section BasicCalc.

  Context `{SL : SUBSTLLANG}.

  Definition HCrule := list formula * formula.
  Definition HCpremsRule (r : HCrule) : list formula := fst r.
  Definition HCconclRule (r : HCrule) : formula := snd r.

End BasicCalc.


Definition HILBCALC `{SL : SUBSTLLANG} := list (@HCrule formula).

Definition MP : HCrule := ([?"A"; ?"A" → ?"B"],
                            ?"B").

Definition CPLHC1 : HCrule := ([], ?"A" → (?"B" → ?"A")).
Definition CPLHC2 : HCrule := ([], (¬ ?"A" → ¬ ?"B") → (?"B" → ?"A")).
Definition CPLHC3 : HCrule := ([], (?"A" → (?"B" → ?"C")) →
                                     ((?"A" → ?"B") → (?"A" → ?"C"))).

Definition cplHC : @HILBCALC _ _ _ substpl := [MP; CPLHC1; CPLHC2; CPLHC3].


Section HC_TO_DC.

  Context `{SL : SUBSTLLANG}.

  Definition fmltoseq (A : formula) : @sequent formula := I ⊢ £A.

  Definition HCtoDC_rule (r : @HCrule formula) : @rule formula := 
    (map fmltoseq (HCpremsRule r), fmltoseq (HCconclRule r)).

  Definition HCtoDC (HC : HILBCALC) : DISPCALC := map HCtoDC_rule HC.

End HC_TO_DC.

Definition cplHilbComp (DC : DISPCALC) := SubDer (HCtoDC cplHC) DC.

Definition cplLr : DISPCALC := (cpldc ++ [refl]).


#[export] Instance cplLr_MP : DerivRule cplLr (HCtoDC_rule MP).
Proof.
  unfold MP. set (A := ?"A"). set (B := ?"B").
  simpl. unfold fmltoseq.
  set (d := Der (I ⊢ £B) CUT
           [Unf (I ⊢ £(A → B));
            Der (£(A → B) ⊢ £B) Idell
              [Der (I,, £(A → B) ⊢ £B) Mrls
              [Der (£(A → B) ⊢ ∗I,, £B) Impl
              [Unf (I ⊢ £A); Der (£B ⊢ £B) refl []]]]]).
  confirm_derr d.
Defined.

Theorem cplLr_ExtraDC : DerivDC cplLr ExtraDC.
Proof.
  apply (SubDC_SubDerDC MinDC). forall_list_tauto. apply MinDC_ExtraDC.
Defined.

#[export] Instance cplLr_CPLHC1 : DerivRule cplLr (HCtoDC_rule CPLHC1).
Proof.
  unfold CPLHC1. set (A := ?"A"). set (B := ?"B").
  apply (Extend_DerivDC _ _ cplLr_ExtraDC).
  confirm_derr (Der (I ⊢ £(A → (B → A))) Impr
               [Der (I,, £A ⊢ £(B → A)) Iaddl
               [Der (£A ⊢ £(B → A)) Impr
               [Der (£A,, £B ⊢ £A) Comml
               [Der (£B,, £A ⊢ £A) Wkl
               [Der (£A ⊢ £A) refl []]]]]]).
Defined.

#[export] Instance cplLr_CPLHC2 : DerivRule cplLr (HCtoDC_rule CPLHC2).
Proof.
  unfold CPLHC2. set (A := ?"A"). set (B := ?"B").
  apply (Extend_DerivDC _ _ cplLr_ExtraDC).
  set (d := Der (I ⊢ £((¬ A → ¬ B) → (B → A))) Impr
            [Der (I,, £(¬ A → ¬ B) ⊢ £(B → A)) Iaddl
            [Der (£(¬ A → ¬ B) ⊢ £(B → A)) Impr
            [Der (£(¬ A → ¬ B),, £B ⊢ £A) DSEr
            [Der (£(¬ A → ¬ B),, £B ⊢ ∗∗£A) Mrrs
            [Der (£(¬ A → ¬ B) ⊢ (∗∗£A),, ∗£B) Impl
            [Der (∗£A ⊢ £(¬ A)) Negr
            [Der (∗£A ⊢ ∗£A) Snn
            [Der (£A ⊢ £A) refl []]];
             Der (£(¬ B) ⊢ ∗£B) Negl
               [Der (∗£B ⊢ ∗£B) Snn
               [Der (£B ⊢ £B) refl []]]]]]]]]).
  confirm_derr d.
Defined.

#[export] Instance cplLr_CPLHC3 : DerivRule cplLr (HCtoDC_rule CPLHC3).
Proof.
  unfold CPLHC3. set (A := ?"A"). set (B := ?"B"). set (C := ?"C").
  apply (Extend_DerivDC _ _ cplLr_ExtraDC).
  set (d :=  Der (I ⊢ £((A → (B → C)) → ((A → B) → (A → C)))) Impr
            [Der (I,, £(A → (B → C)) ⊢ £((A → B) → (A → C))) Iaddl
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
                   Der (£C ⊢ £C) refl []]]]]]]]]]]]]]]]]]]]]]]]]]).
  confirm_derr d.
  Defined.

Theorem cpldcHilbComp : SubDer (HCtoDC cplHC) (cpldc ++ [refl]).
Proof.
  apply DerivDC_SubDer. intros r Hr.
  unfold HCtoDC, cplHC, map in Hr.
  dec_destruct_List_In rule_eq_dec r; rewrite Heq; try apply (alr_DerivRule _ _).
Defined.
