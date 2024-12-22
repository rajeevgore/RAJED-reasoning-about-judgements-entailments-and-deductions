Require Import String.
Open Scope string_scope.

Require Import Lang.
Require Import Sequents.
Require Import Derivation.
Require Import Derivability.
Require Import Cuts.
Require Import CutElim.
Require Import Rules.
Require Import PL.
Require Import CPLRules.
Import CPLRules.
Require Import CPLDC.
Import CPLNotations.

Require Import List.
Import ListNotations.

Require Extraction.
Require Import Coq.extraction.ExtrOcamlNativeString.


Definition cpl_cutElim := cutElim cpldc cpldcBel.



Definition impcon_impr : rule := ([], (£(%"p" → (%"q" ∧ %"r")) ⊢ £(%"p" → %"r"))).

#[export] Instance derr_impcon_impr : DerivRule cpldc impcon_impr.
Proof.
  Import CPLDeriv.
  set (p := %"p"). set (q := %"q"). set (r := %"r").
  apply (Extend_DerivRule_expl _ (frefl (q ∧ r))).
  apply cpldc_derr_frefl.
  unfold fmlNoFV. rewrite (noVar_iff_noVar_cpt FV).
  simpl; unfold eq_rect_r; simpl. tauto.
  apply (Extend_DerivRule_expl _ Wkl).
  apply (SubDC_DerivRule cpldc). apply (alr_DerivRule _ _).
  apply incl_appl, incl_refl.
  set (d := Der (£(p → (q ∧ r)) ⊢ £(p → r)) Impr
           [Der (£(p → (q ∧ r)),, £ p ⊢ £ r) Comml
           [Der (£ p,, £(p → (q ∧ r)) ⊢ £ r) CUT
           [Der (£ p,, £(p → (q ∧ r)) ⊢ £(q ∧ r)) Mrls
              [Der (£(p → (q ∧ r)) ⊢ ∗ £ p,, £(q ∧ r)) Impl
              [Der (£ p ⊢ £ p) atrefl [];
               Der (£(q ∧ r) ⊢ £(q ∧ r)) (frefl (q ∧ r)) []]];
            Der (£(q ∧ r) ⊢ £ r) Conl
           [Der (£q,, £ r ⊢ £ r) Wkl
           [Der (£ r ⊢ £ r) atrefl []]]]]]).
  confirm_derr d.
Defined.

(*
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

Extraction "cpl_cutelim.ml" cpl_cutElim derr_impcon_impr.
*)
