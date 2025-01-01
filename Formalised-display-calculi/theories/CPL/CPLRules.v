Require Import String.
Open Scope string_scope.
Require Import Ensembles.
Require Import List.
Import ListNotations.

Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import PL.
Import CPLNotations.

Module CPLRules.

  (* Logical rules *)

  Definition Topl  : rule := ([I ⊢ $"X"],   (* special case of Iwl *)
                               £⊤ ⊢ $"X").

  Definition Topr  : rule := ([],
                               I ⊢ £⊤).

  Definition Botl  : rule := ([],
                               £⊥ ⊢ I). 
  
  Definition Botr  : rule := ([$"X" ⊢ I],    (* X ⊢ I / ∗I ⊢ ∗X / I ⊢ ∗X / ∗⊥ ⊢ ∗X / X ⊢ ⊥ *)
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

  (* Structure-free / Context-sharing variants *)
  
  Definition Consll : rule := ([£?"A" ⊢ $"X"],
                              £(?"A" ∧ ?"B") ⊢ $"X").

  Definition Conslr : rule := ([£?"B" ⊢ $"X"],
                              £(?"A" ∧ ?"B") ⊢ $"X").

  Definition Consr : rule := ([$"X" ⊢ £?"A"   ;   $"X" ⊢ £?"B"],
                               $"X" ⊢ £(?"A" ∧ ?"B")).

  Definition Dissl : rule := ([£?"A" ⊢ $"X"   ;   £?"B" ⊢ $"X"],
                               £(?"A" ∨ ?"B") ⊢ $"X").

  Definition Dissrl : rule := ([$"X" ⊢ £?"A"],
                               $"X" ⊢ £(?"A" ∨ ?"B")).

  Definition Dissrr : rule := ([$"X" ⊢ £?"B"],
                                $"X" ⊢ £(?"A" ∨ ?"B")).

  Definition Impsl  : rule := ([∗ £?"A" ⊢ $"X"   ;   £?"B" ⊢ $"X"],
                                £(?"A" → ?"B") ⊢ $"X").



  (* Structural Rules *)
  Definition Isl   : rule := ([I ⊢ $"Y"],       (* special case of Iwl *)
                               ∗ I ⊢ $"Y").

  Definition Iul   : rule := ([∗ I ⊢ $"Y"],
                               I ⊢ $"Y").

  Definition Iaddl  : rule := ([$"X" ⊢ $"Y"],
                                $"X",, I ⊢ $"Y").

  Definition Idell  : rule := ([$"X",, I ⊢ $"Y"],
                                $"X" ⊢ $"Y").

  Definition Iwl   : rule := ([I ⊢ $"Y"],
                               $"X" ⊢ $"Y").

  Definition Iwr   : rule := ([$"X" ⊢ I],
                               $"X" ⊢ $"Y").

  Definition Comml : rule := ([$"X",, $"Y" ⊢ $"Z"],
                               $"Y",, $"X" ⊢ $"Z").

  Definition Contl : rule := ([$"X",, $"X" ⊢ $"Y"],
                               $"X" ⊢ $"Y").

  Definition Assol : rule := ([$"X",, ($"Y",, $"Z") ⊢ $"W"],
                               ($"X",, $"Y"),, $"Z" ⊢ $"W").



  (* Display rules *)

  Definition Mlrn : rule := ([$"X",, $"Y" ⊢ $"Z"],
                              $"X" ⊢ $"Z",, ∗ $"Y").

  Definition Mrrslln : rule := ([$"X" ⊢ $"Y",, ∗ $"Z"],
                                 $"Z" ⊢ ∗ $"X",, $"Y").

  Definition Mrls : rule := ([$"X" ⊢ ∗ $"Y",, $"Z"],
                              $"Y",, $"X" ⊢ $"Z").


  Definition Snn : rule := ([$"X" ⊢ $"Y"],
                             ∗ $"Y" ⊢ ∗ $"X").

  Definition Sns : rule := ([$"X" ⊢ ∗ $"Y"],
                             $"Y" ⊢ ∗ $"X").

  Definition DSEr : rule := ([$"X" ⊢ ∗ ∗ $"Y"],
                              $"X" ⊢ $"Y").

  
  Definition Mrrn : rule := ([$"X" ⊢ $"Y",, $"Z"],
                              $"X",, ∗ $"Z" ⊢ $"Y").

  Definition Mlrsrln : rule := ([$"X",, ∗ $"Y" ⊢ $"Z"],
                                 ∗ $"Z",, $"X" ⊢ $"Y").

  Definition Mlls : rule := ([∗ $"X",, $"Y" ⊢ $"Z"],
                              $"Y" ⊢ $"X",, $"Z").





  Definition Ssn : rule := ([∗ $"X" ⊢ $"Y"],
                             ∗ $"Y" ⊢ $"X").

  Definition Sss : rule := ([∗ $"X" ⊢ ∗ $"Y"],
                             $"Y" ⊢ $"X").

  Definition DSEl : rule := ([(∗ ∗ $"X") ⊢ $"Y"],
                              $"X" ⊢ $"Y").

  Definition Commr : rule := ([$"X" ⊢ $"Y",, $"Z"],
                               $"X" ⊢ $"Z",, $"Y").

  Definition Mlln : rule := ([$"X",, $"Y" ⊢ $"Z"],
                              $"Y" ⊢ ∗ $"X",, $"Z").

  Definition Mrrs : rule := ([$"X" ⊢ $"Y",, ∗$"Z"],
                              $"X",, $"Z" ⊢ $"Y").
  
  Definition Assolinv : rule := ([($"X",, $"Y"),, $"Z" ⊢ $"W"],
                                  $"X",, ($"Y",, $"Z") ⊢ $"W").

  Definition Wkl : rule := ([$"X" ⊢ $"Y"],
                             $"Z",, $"X" ⊢ $"Y").

  Definition Wkr : rule := ([$"X" ⊢ $"Y"],
                             $"X" ⊢ $"Y",, $"Z").

  Definition ContIl : rule := ([$"X",, $"X" ⊢ $"Y"],
                                I,, $"X" ⊢ $"Y").

  Definition Mlrs : rule := ([$"X",, ∗ $"Y" ⊢ $"Z"],
                              $"X" ⊢ $"Z",, $"Y").

  Definition Mrln : rule := ([$"X" ⊢ $"Y",, $"Z"],
                              ∗ $"Y",, $"X" ⊢ $"Z").

  Definition Iaddr : rule := ([$"X" ⊢ $"Y"],
                               $"X" ⊢ I,, $"Y").

  Definition Idelr : rule := ([$"X" ⊢ I,, $"Y"],
                               $"X" ⊢ $"Y").
  
  Definition ContWkls : rule := ([∗ $"X" ⊢ $"X"],
                                  $"Y" ⊢ $"X").
  
  Definition ContWkln : rule := ([$"X" ⊢ ∗ $"X"],
                                  $"Y" ⊢ ∗ $"X").

  Definition DSIl : rule := ([$"X" ⊢ $"Y"],
                              (∗ ∗ $"X") ⊢ $"Y").

  Definition DSIr : rule := ([$"X" ⊢ $"Y"],
                              $"X" ⊢ (∗ ∗ $"Y")).

  Definition Distl : rule := ([∗ ($"X",, $"Y") ⊢ $"Z"],
                               ∗ $"X",, ∗ $"Y" ⊢ $"Z").

  Definition Factl : rule := ([∗ $"X",, ∗ $"Y" ⊢ $"Z"],
                               ∗ ($"X",, $"Y") ⊢ $"Z").
  
  Definition Distr : rule := ([$"X" ⊢ ∗ ($"Y",, $"Z")],
                               $"X" ⊢ ∗ $"Y",, ∗ $"Z").

  Definition Factr : rule := ([$"X" ⊢ ∗ $"Y",, ∗ $"Z"],
                               $"X" ⊢ ∗ ($"Y",, $"Z")).

End CPLRules.
