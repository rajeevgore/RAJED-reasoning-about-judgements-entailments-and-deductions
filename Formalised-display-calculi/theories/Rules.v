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
Require Import Derivability.


Section CommonRules.

  Context `{SL : SUBSTLLANG}.

  (* Reflexivity axioms *)
  Definition atrefl : rule := ([],
                              £p"p" ⊢ £p"p").

  Definition frefl (A : formula) : rule := ([],
                                            £A ⊢ £A).

  Definition refl  : @rule formula := ([],
                                        £?"A" ⊢ £?"A").

  (* Structural Rules *)
  Definition Isl   : @rule formula := ([I ⊢ $"Y"],       (* special case of Iwl *)
                                        ∗ I ⊢ $"Y").

  Definition Iul   : @rule formula := ([∗ I ⊢ $"Y"],
                                        I ⊢ $"Y").

  Definition Iaddl  : @rule formula := ([$"X" ⊢ $"Y"],
                                         I,, $"X" ⊢ $"Y").

  Definition Idell  : @rule formula := ([I,, $"X" ⊢ $"Y"],
                                         $"X" ⊢ $"Y").

  Definition Iwl   : @rule formula := ([I ⊢ $"Y"],
                                        $"X" ⊢ $"Y").

  Definition Iwr   : @rule formula := ([$"X" ⊢ I],         (* derivable as X ⊢ I / ∗I ⊢ ∗X / I ⊢ ∗X / ∗Y ⊢ ∗X / X ⊢ Y *)
                                        $"X" ⊢ $"Y").      (*                   Snn       Iul      Iwl        Sss      *)

  Definition Comml : @rule formula := ([$"X",, $"Y" ⊢ $"Z"],
                                        $"Y",, $"X" ⊢ $"Z").

  Definition Contl : @rule formula := ([$"X",, $"X" ⊢ $"Y"],
                                         $"X" ⊢ $"Y").

  Definition Assol : @rule formula := ([$"X",, ($"Y",, $"Z") ⊢ $"W"],
                                         ($"X",, $"Y"),, $"Z" ⊢ $"W").


  (* Display Equivalence Rules (DE) *)
  Definition Mlrn : @rule formula := ([$"X",, $"Y" ⊢ $"Z"],
                                       $"X" ⊢ $"Z",, ∗ $"Y").

  Definition Mrrslln : @rule formula := ([$"X" ⊢ $"Y",, ∗ $"Z"],
                                          $"Z" ⊢ ∗ $"X",, $"Y").

  Definition Mrls : @rule formula := ([$"X" ⊢ ∗ $"Y",, $"Z"],
                                      $"Y",, $"X" ⊢ $"Z").


  Definition Snn : @rule formula := ([$"X" ⊢ $"Y"],
                                      ∗ $"Y" ⊢ ∗ $"X").

  Definition Sks : @rule formula := ([∗ $"X" ⊢ ∗ $"Y"],
                                      $"Y" ⊢ ∗ ∗ $"X").

  Definition DSEr : @rule formula := ([$"X" ⊢ ∗ ∗ $"Y"],
                                       $"X" ⊢ $"Y").

  
  Definition Mrrn : @rule formula := ([$"X" ⊢ $"Y",, $"Z"],
                                       $"X",, ∗ $"Z" ⊢ $"Y").

  Definition Mlrsrln : @rule formula := ([$"X",, ∗ $"Y" ⊢ $"Z"],
                                          ∗ $"Z",, $"X" ⊢ $"Y").

  Definition Mlls : @rule formula := ([∗ $"X",, $"Y" ⊢ $"Z"],
                                      $"Y" ⊢ $"X",, $"Z").


  (* Some rules that can be derived from above rules *)
  Definition Ssn : @rule formula := ([∗ $"X" ⊢ $"Y"],
                                      ∗ $"Y" ⊢ $"X").

  Definition Sns : @rule formula := ([$"X" ⊢ ∗ $"Y"],
                                      $"Y" ⊢ ∗ $"X").

  Definition Sss : @rule formula := ([∗ $"X" ⊢ ∗ $"Y"],
                                      $"Y" ⊢ $"X").

  Definition DSEl : @rule formula := ([(∗ ∗ $"X") ⊢ $"Y"],
                                       $"X" ⊢ $"Y").

  Definition Commr : @rule formula := ([$"X" ⊢ $"Y",, $"Z"],
                                        $"X" ⊢ $"Z",, $"Y").

  Definition Mlln : @rule formula := ([$"X",, $"Y" ⊢ $"Z"],
                                       $"Y" ⊢ ∗ $"X",, $"Z").

  Definition Mrrs : @rule formula := ([$"X" ⊢ $"Y",, ∗$"Z"],
                                       $"X",, $"Z" ⊢ $"Y").

  Definition Assolinv : @rule formula := ([($"X",, $"Y"),, $"Z" ⊢ $"W"],
                                            $"X",, ($"Y",, $"Z") ⊢ $"W").




  Definition Mlrs : @rule formula := ([$"X",, ∗ $"Y" ⊢ $"Z"],
                                       $"X" ⊢ $"Z",, $"Y").

  Definition Mrln : @rule formula := ([$"X" ⊢ $"Y",, $"Z"],
                                      ∗ $"Y",, $"X" ⊢ $"Z").

  Definition Assor : @rule formula := ([$"X" ⊢ $"Y",, ($"Z",, $"W")],
                                        $"X" ⊢ ($"Y",, $"Z"),, $"W").

  Definition Assorinv : @rule formula := ([$"X" ⊢ ($"Y",, $"Z"),, $"W"],
                                           $"X" ⊢ $"Y",, ($"Z",, $"W")).

  Definition Iur : @rule formula := ([$"X" ⊢ ∗ I],
                                      $"X" ⊢ I).

  Definition Contr : @rule formula := ([$"X" ⊢ $"Y",, $"Y"],
                                        $"X" ⊢ $"Y").

  Definition Wkl : @rule formula := ([$"X" ⊢ $"Y"],
                                      $"Z",, $"X" ⊢ $"Y").
  Definition Wkr : @rule formula := ([$"X" ⊢ $"Y"],
                                      $"X" ⊢ $"Y",, $"Z").

  Definition ContIl : @rule formula := ([$"X",, $"X" ⊢ $"Y"],
                                         I,, $"X" ⊢ $"Y").

  Definition Iaddr : @rule formula := ([$"X" ⊢ $"Y"],
                                        $"X" ⊢ I,, $"Y").

  Definition Idelr : @rule formula := ([$"X" ⊢ I,, $"Y"],
                                        $"X" ⊢ $"Y").
  
  Definition ContWkls : @rule formula := ([∗ $"X" ⊢ $"X"],
                                           $"Y" ⊢ $"X").
  
  Definition ContWkln : @rule formula := ([$"X" ⊢ ∗ $"X"],
                                           $"Y" ⊢ ∗ $"X").

  Definition DSIl : @rule formula := ([$"X" ⊢ $"Y"],
                                       (∗ ∗ $"X") ⊢ $"Y").

  Definition DSIr : @rule formula := ([$"X" ⊢ $"Y"],
                                       $"X" ⊢ (∗ ∗ $"Y")).

  Definition Distl : @rule formula := ([∗ ($"X",, $"Y") ⊢ $"Z"],
                                        ∗ $"X",, ∗ $"Y" ⊢ $"Z").

  Definition Factl : @rule formula := ([∗ $"X",, ∗ $"Y" ⊢ $"Z"],
                                        ∗ ($"X",, $"Y") ⊢ $"Z").

  Definition Distr : @rule formula := ([$"X" ⊢ ∗ ($"Y",, $"Z")],
                                        $"X" ⊢ ∗ $"Y",, ∗ $"Z").

  Definition Factr : @rule formula := ([$"X" ⊢ ∗ $"Y",, ∗ $"Z"],
                                        $"X" ⊢ ∗ ($"Y",, $"Z")).


  (* BELNAP's DISPLAY RULES *)

  Definition MClrn : @rule formula := ([$"X",, $"Y" ⊢ $"Z"],
                                        $"X" ⊢ ∗ $"Y",, $"Z").

  Definition MCrls : @rule formula := ([$"X" ⊢ ∗ $"Y",, $"Z"],
                                        $"X",, $"Y" ⊢ $"Z").


  Definition MCrln : @rule formula := ([$"X" ⊢ $"Y",, $"Z"],
                                        $"X",, ∗ $"Y" ⊢ $"Z").
  (* Mlrs *)
  (* Commr *)


  (* Snn *)
  Definition Ssk: @rule formula := ([∗ $"X" ⊢ ∗ $"Y"],
                                     (∗ ∗ $"Y") ⊢ $"X").
  (* DSEl *)
  
                                        


End CommonRules.

Section CommonRulesDC.

  Context `{SL : SUBSTLLANG}.

  Definition MinDC : DISPCALC :=
    [atrefl; Iwr; Iaddl; Idell; Iwl; Comml; Contl; Assol; CUT;
     Mlrn; Mrrslln; Mrls; Snn; Sns; DSEr; Mrrn; Mlrsrln; Mlls].

  Definition ExtraDC : DISPCALC := [Ssn; Sns; Sss; DSEl; Commr; Mlln; Mrrs; Assolinv; Wkl].

  Ltac set_XYZW :=
    set (X := $"X" : @structr formula); set (Y := $"Y" : @structr formula);
    set (Z := $"Z" : @structr formula); set (W := $"W" : @structr formula).
  
  #[export] Instance dernc_Ssn : DerivRuleNC MinDC Ssn.
  Proof.
    set (d := Der (∗ $"Y" ⊢ $"X") DSEr
             [Der (∗ $"Y" ⊢ ∗ ∗ $"X") Snn
             [Unf (∗ $"X" ⊢ $"Y")]]
           : @dertree formula).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Mrrs : DerivRuleNC MinDC Mrrs.
  Proof.
    set_XYZW.
    set (d := Der (X,, Z ⊢ Y) Mrls [Der (Z ⊢ ∗X,, Y) Mrrslln [Unf (X ⊢ Y,, ∗Z)] ]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Sss : DerivRuleNC MinDC Sss.
  Proof.
    set_XYZW.
    set (d := Der (Y ⊢ X) DSEr [Der (Y ⊢ ∗∗X) Sns [Unf (∗X ⊢ ∗Y)] ]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_DSEl : DerivRuleNC MinDC DSEl.
  Proof.
    set_XYZW.
    apply (Extend_DerivRuleNC _ (@Sss formula)).
    set (d := Der (X ⊢ Y) Sss
             [Der (∗Y ⊢ ∗X) DSEr
             [Der (∗Y ⊢ ∗∗∗X) Snn
             [Unf ((∗∗X) ⊢ Y)]]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Sns : DerivRuleNC MinDC Sns.
  Proof.
    set_XYZW.
    apply (Extend_DerivRuleNC _ (@DSEl formula)).
    set (d := Der (Y ⊢ ∗ X) DSEl
             [Der ((∗∗Y) ⊢ ∗X) Snn
             [Unf (X ⊢ ∗Y)]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Commr : DerivRuleNC MinDC Commr.
  Proof.
    set_XYZW.
    set (d := Der (X ⊢ Z,, Y) Mlls [Der (∗Z,, X ⊢ Y) Comml
                                      [Der (X,, ∗Z ⊢ Y) Mrrn [Unf (X ⊢ Y,, Z)] ] ]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Mlln : DerivRuleNC MinDC Mlln.
  Proof.
    set_XYZW.
    apply (Extend_DerivRuleNC _ (@Commr formula)).
    set (d := Der (Y ⊢ ∗X,, Z) Commr
             [Der (Y ⊢ Z,, ∗X) Mlrn
             [Der (Y,, X ⊢ Z) Comml
             [Unf (X,, Y ⊢ Z)]]]).
    confirm_derrnc d.
  Defined.

  #[export] Instance dernc_Assolinv : DerivRuleNC MinDC Assolinv.
  Proof.
    unfold Assolinv. set_XYZW.
    apply_DRNC_inDC (@Comml formula).
    apply_DRNC_inst (@Mrrs formula).
    apply_DRNC_inDC (@Comml formula).
    apply_DRNC_inDC (@Mlrn formula).
    apply_DRNC_inDC (@Assol formula).
    apply_DRNC_inDC (@Comml formula).
    apply_DRNC_inst (@Mrrs formula).
    apply_DRNC_inDC (@Comml formula).
    apply_DRNC_inDC (@Mlrn formula).
    apply DerivRuleNC_refl.
  Defined.

  #[export] Instance derr_Wkl : DerivRule MinDC Wkl.
  Proof.
    set_XYZW.
    apply (Extend_DerivRule _ Mrrs).
    confirm_derr (Der (Z,, X ⊢ Y) Mrrs
                 [Der (Z ⊢ Y,, ∗X) Iwl
                 [Der (I ⊢ Y,, ∗X) Mlrn
                 [Der (I,, X ⊢ Y) Iaddl
                 [Unf (X ⊢ Y)]]]]).
  Defined.

  Theorem MinDC_ExtraDC : DerivDC MinDC ExtraDC.
  Proof.
    forall_list_tauto. dec_destruct_List_In rule_eq_dec x;
      rewrite Heq; apply (alr_DerivRule _ _).
  Defined.

End CommonRulesDC.
