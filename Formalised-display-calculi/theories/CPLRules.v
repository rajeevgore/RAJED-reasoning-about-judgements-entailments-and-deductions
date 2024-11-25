Require Import String.
Open Scope string_scope.
Require Import Ensembles.
Require Import List.
Import ListNotations.

Require Import Tactics.
Require Import Utils.
Require Import Llang.
Require Import Sequents.
Require Import PL.
Import PLNotations.

Module CPLRules.
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

End CPLRules.
