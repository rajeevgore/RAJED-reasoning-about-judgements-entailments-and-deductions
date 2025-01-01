Require Import String.
Open Scope string_scope.
Require Import Ensembles.
Require Import List.
Import ListNotations.

Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Kt.
Import KtNotations.

Module KtRules.

  (* Logical rules *)

  Definition Topl  : rule := ([I ⊢ $"X"],
                               £⊤ ⊢ $"X").

  Definition Topr  : rule := ([],
                               I ⊢ £⊤).

  Definition Botl  : rule := ([],
                               £⊥ ⊢ I). 
  
  Definition Botr  : rule := ([$"X" ⊢ I],
                               $"X" ⊢ £⊥).

  Definition Negl  : rule := ([∗ £?"A" ⊢ $"X"],
                               £(¬ ?"A") ⊢ $"X").

  Definition Negr  : rule := ([$"X" ⊢ ∗ £?"A"],
                               $"X" ⊢ £(¬ ?"A")).

  Definition Conl  : rule := ([£?"A",, £?"B" ⊢ $"X"],
                               £(?"A" ∧ ?"B") ⊢ $"X").

  Definition Conr  : rule := ([$"X" ⊢ £?"A"   ;   $"Y" ⊢ £?"B"],
                               $"X",, $"Y" ⊢ £(?"A" ∧ ?"B")).

  Definition Disl  : rule := ([£?"A" ⊢ $"X"   ;   £?"B" ⊢ $"Y"],
                               £(?"A" ∨ ?"B") ⊢ $"X",, $"Y").

  Definition Disr  : rule := ([$"X" ⊢ £?"A",, £?"B"],
                               $"X" ⊢ £(?"A" ∨ ?"B")).

  Definition Impl  : rule := ([$"X" ⊢ £?"A"   ;   £?"B" ⊢ $"Y"],
                               £(?"A" → ?"B") ⊢ ∗ $"X",, $"Y").

  Definition Impr  : rule := ([$"X",, £?"A" ⊢ £?"B"],
                               $"X" ⊢ £(?"A" → ?"B")).

  Definition Boxnl : rule := ([£?"A" ⊢ $"X"],
                               £(◻ ?"A") ⊢ ● $"X").

  Definition Boxnr : rule := ([● $"X" ⊢ £?"A"],
                               $"X" ⊢ £(◻ ?"A")).

  Definition Dianl : rule := ([(∗●∗ £?"A") ⊢ $"X"],
                               £(◊ ?"A") ⊢ $"X").

  Definition Dianr : rule := ([$"X" ⊢ £?"A"],
                               (∗●∗ $"X") ⊢ £(◊ ?"A")).

  Definition Boxpl : rule := ([£?"A" ⊢ $"X"],
                               £(◼ ?"A") ⊢ ∗●∗ $"X").

  Definition Boxpr : rule := ([$"X" ⊢ ∗●∗ £?"A"],
                               $"X" ⊢ £(◼ ?"A")).

  Definition Diapl : rule := ([£?"A" ⊢ ● $"X"],
                               £(⧫ ?"A") ⊢ $"X").
  
  Definition Diapr : rule := ([$"X" ⊢ £?"A"],
                               ● $"X" ⊢ £(⧫ ?"A")).


  (* Structural rules *)
  Definition Iaddl  : rule := ([$"X" ⊢ $"Y"],
                                I,, $"X" ⊢ $"Y").

  Definition Idell  : rule := ([I,, $"X" ⊢ $"Y"],
                                $"X" ⊢ $"Y").

  Definition Iaddr : rule := ([$"X" ⊢ $"Y"],
                               $"X" ⊢ I,, $"Y").

  Definition Idelr : rule := ([$"X" ⊢ I,, $"Y"],
                               $"X" ⊢ $"Y").

  Definition Isl   : rule := ([I ⊢ $"Y"],
                               ∗ I ⊢ $"Y").

  Definition Iul   : rule := ([∗ I ⊢ $"Y"],
                               I ⊢ $"Y").

  Definition Isr   : rule := ([$"Y" ⊢ I],
                               $"Y" ⊢ ∗ I).

  Definition Iur   : rule := ([$"Y" ⊢ ∗ I],
                               $"Y" ⊢ I).

  Definition Wkl : rule := ([$"X" ⊢ $"Y"],
                             $"Z",, $"X" ⊢ $"Y").

  Definition Wkr : rule := ([$"X" ⊢ $"Y"],
                             $"X" ⊢ $"Y",, $"Z").

  Definition Assol : rule := ([$"X",, ($"Y",, $"Z") ⊢ $"W"],
                               ($"X",, $"Y"),, $"Z" ⊢ $"W").
  
  Definition Assoinvl : rule := ([($"X",, $"Y"),, $"Z" ⊢ $"W"],
                                  $"X",, ($"Y",, $"Z") ⊢ $"W").

  Definition Assor : rule := ([$"X" ⊢ $"Y",, ($"Z",, $"W")],
                               $"X" ⊢ ($"Y",, $"Z"),, $"W").
  
  Definition Assoinvr : rule := ([$"X" ⊢ ($"Y",, $"Z"),, $"W"],
                                  $"X" ⊢ $"Y",, ($"Z",, $"W")).

  Definition Comml : rule := ([$"X",, $"Y" ⊢ $"Z"],
                               $"Y",, $"X" ⊢ $"Z").

  Definition Commr : rule := ([$"X" ⊢ $"Y",, $"Z"],
                               $"X" ⊢ $"Z",, $"Y").

  Definition Contl : rule := ([$"X",, $"X" ⊢ $"Y"],
                               $"X" ⊢ $"Y").

  Definition Contr : rule := ([$"X" ⊢ $"Y",, $"Y"],
                               $"X" ⊢ $"Y").

  Definition Icl   : rule := ([I ⊢ $"Y"],
                               ● I ⊢ $"Y").

  Definition Icr   : rule := ([$"X" ⊢ I],
                               $"X" ⊢ ● I).



  (* Display rules *)

  Definition Mlrn : rule := ([$"X",, $"Y" ⊢ $"Z"],
                              $"X" ⊢ $"Z",, ∗ $"Y").

  Definition Mrrs : rule := ([$"X" ⊢ $"Y",, ∗$"Z"],
                              $"X",, $"Z" ⊢ $"Y").

  Definition Mlln : rule := ([$"X",, $"Y" ⊢ $"Z"],
                              $"Y" ⊢ ∗ $"X",, $"Z").

  Definition Mrls : rule := ([$"X" ⊢ ∗ $"Y",, $"Z"],
                              $"Y",, $"X" ⊢ $"Z").

  Definition Mrrn : rule := ([$"X" ⊢ $"Y",, $"Z"],
                              $"X",, ∗ $"Z" ⊢ $"Y").

  Definition Mlrs : rule := ([$"X",, ∗ $"Y" ⊢ $"Z"],
                              $"X" ⊢ $"Z",, $"Y").

  Definition Mrln : rule := ([$"X" ⊢ $"Y",, $"Z"],
                              ∗ $"Y",, $"X" ⊢ $"Z").

  Definition Mlls : rule := ([∗ $"X",, $"Y" ⊢ $"Z"],
                              $"Y" ⊢ $"X",, $"Z").

  Definition Ssn : rule := ([∗ $"X" ⊢ $"Y"],
                             ∗ $"Y" ⊢ $"X").

  Definition Sns : rule := ([$"X" ⊢ ∗ $"Y"],
                             $"Y" ⊢ ∗ $"X").

  Definition DSEl : rule := ([(∗ ∗ $"X") ⊢ $"Y"],
                              $"X" ⊢ $"Y").

  Definition DSIl : rule := ([$"X" ⊢ $"Y"],
                              (∗ ∗ $"X") ⊢ $"Y").

  Definition DSEr : rule := ([$"X" ⊢ ∗ ∗ $"Y"],
                              $"X" ⊢ $"Y").

  Definition DSIr : rule := ([$"X" ⊢ $"Y"],
                              $"X" ⊢ ∗ ∗ $"Y").

  Definition Scl : rule := ([● $"X" ⊢ $"Y"],
                             $"X" ⊢ ● $"Y").

  Definition Scr : rule := ([$"X" ⊢ ● $"Y"],
                             ● $"X" ⊢ $"Y").

  Definition Sss : rule := ([∗ $"X" ⊢ ∗ $"Y"],
                             $"Y" ⊢ $"X").


End KtRules.
