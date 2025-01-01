Require Import String.
Open Scope string_scope.

Require Import Lang.
Require Import Sequents.
Require Import Derivation.
Require Import Derivability.
Require Import Cuts.
Require Import CutElim.
Require Import Rules.
Require Import Kt.
Require Import KtRules.
Import KtRules.
Require Import KtDC.
Import KtNotations.

Require Import List.
Import ListNotations.

Require Extraction.
Require Import Coq.extraction.ExtrOcamlNativeString.


Definition Kt_cutElim := cutElim Kt_DC Kt_DCBel.



Definition box_con_dis : rule := ([], £(◻ (%"p" ∧ %"q")) ⊢ £(◻ %"p" ∨ ◻ %"q")).

#[export] Instance derr_box_con_dis : DerivRule Kt_DC box_con_dis.
Proof.
  Import KtDeriv.
  set (p := %"p"). set (q := %"q").
  apply (Extend_DerivRule_expl _ (frefl (◻p))).
  apply dernc_frefl. unfold fmlNoFV.
  rewrite (noVar_iff_noVar_cpt FV). simpl. tauto.
  confirm_derr (Der (£ ◻(p ∧ q) ⊢ £ ◻p ∨ ◻q) CUT
               [Der (£ ◻(p ∧ q) ⊢ £ ◻p) Boxnr
                  [Der (● £ ◻(p ∧ q) ⊢ £ p) Scr
                  [Der (£ ◻(p ∧ q) ⊢ ● £ p) Boxnl
                  [Der (£ p ∧ q ⊢ £ p) Conl
                  [Der (£ p,, £ q ⊢ £ p) Comml
                  [Der (£ q,, £ p ⊢ £ p) Wkl
                  [Der (£ p ⊢ £ p) atrefl []]]]]]];
                Der (£ ◻p ⊢ £ ◻p ∨ ◻q) Disr
                  [Der (£ ◻p ⊢ £ ◻p,, £ ◻q) Wkr
                  [Der (£ ◻p ⊢ £ ◻p) (frefl (◻p)) []]]]).
Defined.

(*
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

Extraction "Kt_cutelim.ml" Kt_cutElim derr_box_con_dis.
*)
