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
Require Import Derivability.


Section CommonRules.

  Context `{SL : STRLANG}.

  (* Reflexivity axioms *)
  Definition atrefl : rule := ([],
                               FS (Atm "p") ⊢ FS (Atm "p")).

  Definition frefl (A : formula) : rule := ([],
                                            FS A ⊢ FS A).

  Definition refl  : rule := ([],
                              FS (FV "A") ⊢ FS (FV "A")).

End CommonRules.
