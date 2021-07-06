
(* assortment of theorems of linear logic, and derivations *)

Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT swappedT.
Require Import fmlsext.
Require Import Coq.Program.Basics.
Require Import lldefs ll_exch.

Lemma lolli_sI {V} A B fs :
  derrec maell_rules emptyT (dual A :: B :: fs) ->
  derrec maell_rules emptyT (@lolli V A B :: fs).
Proof. intro. unfold lolli.  eapply derI.  apply princ_maellI.  
eapply (OSgctxt_eq _ _ _ [] _).  apply Par_p.  apply Parrule_I.
reflexivity. reflexivity.  apply dersrec_singleI. exact X. Qed.

Lemma lolli_2sI {V} A B f fs :
  derrec maell_rules emptyT (f :: dual A :: B :: fs) ->
  derrec maell_rules emptyT (f :: @lolli V A B :: fs).
Proof. intro. unfold lolli.  eapply derI.  apply princ_maellI.  
eapply (OSgctxt_eq _ _ _ [_] _).  apply Par_p.  apply Parrule_I.
reflexivity. reflexivity.  apply dersrec_singleI. exact X. Qed.

Lemma lolli_refl {V} A : derrec maell_rules emptyT [@lolli V A A].
Proof. apply lolli_sI.  apply maell_idr. Qed.

Lemma wpc_lem {V} A B :
  derrec maell_rules emptyT [plus (dual A) (dual B); @wth V B A].
Proof. (* proof rather similar to that of maell_id *)
eapply derI.  eapply princ_maellI.
eapply (OSgctxt_eq _ _ _ [_] []). apply Wth_p.
eapply Wthrule_I. reflexivity. reflexivity.
simpl. unfold fmlsext. simpl.  apply dlCons. eapply derI.
eapply princ_maellI. eapply (OSgctxt_eq _ _ _ [] [B]). apply PlusR_p.
apply PlusRrule_I. reflexivity. reflexivity.
simpl. unfold fmlsext. simpl. apply dersrec_singleI. apply maell_idr.
apply dersrec_singleI. eapply derI.
eapply princ_maellI. eapply (OSgctxt_eq _ _ _ [] [A]). apply PlusL_p.
apply PlusLrule_I. reflexivity. reflexivity.
simpl. unfold fmlsext. simpl. apply dersrec_singleI. apply maell_idr. Qed.

Lemma wth_comm {V} A B : 
  derrec maell_rules emptyT [@lolli V (wth A B) (wth B A)].
Proof. apply lolli_sI. apply wpc_lem. Qed.

Lemma ptc_lem {V} A B :
  derrec maell_rules emptyT [tens (dual A) (dual B) ; @par V B A].
Proof. (* proof rather similar to that of maell_id *)
eapply derI.  eapply princ_maellI.
eapply (OSgctxt_eq _ _ _ [tens _ _] []). apply Par_p.
eapply Parrule_I. reflexivity. reflexivity.
apply dersrec_singleI. unfold fmlsext. simpl.
eapply derI. apply tens_maellI.
eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [] [] [A] [B]). apply Tensrule_I.
apply merge_nil. apply (mergeRI _ (mergeLI _ merge_nil)).
reflexivity. simpl.
apply (dlCons (maell_idr _) (dlCons (maell_idr _) (dlNil _ _))). Qed.

Lemma par_comm {V} A B : 
  derrec maell_rules emptyT [@lolli V (par A B) (par B A)].
Proof.  apply lolli_sI. apply ptc_lem. Qed.

(* can do tens_comm and plus_comm similar to above, 
  but a bit quicker to use exchange as follows *)
Lemma tens_comm {V} A B : 
  derrec maell_rules emptyT [@lolli V (tens A B) (tens B A)].
Proof.  apply lolli_sI.  eapply exch_maell. 2: apply swapped_cc.
pose (ptc_lem (dual B) (dual A)).
clearbody d. rewrite !dual_dual in d. exact d. Qed.

Lemma plus_comm {V} A B : 
  derrec maell_rules emptyT [@lolli V (plus A B) (plus B A)].
Proof.  apply lolli_sI.  eapply exch_maell. 2: apply swapped_cc.
pose (wpc_lem (dual B) (dual A)).
clearbody d. rewrite !dual_dual in d. exact d. Qed.

Lemma lolli_dual {V} A B : derrec maell_rules emptyT 
  [@lolli V (lolli A B) (lolli (dual B) (dual A))].
Proof. apply lolli_sI.  unfold lolli. simpl. rewrite !dual_dual.
pose (ptc_lem (dual A) B).
clearbody d. rewrite !dual_dual in d. exact d. Qed.

(* some rules in form using lolli *)
Lemma tensI {V} A B : derrec maell_rules emptyT
  [@lolli V A (lolli B (tens A B))].
Proof. apply lolli_sI. apply lolli_2sI.  
eapply derI.  apply tens_maellI.
eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [_] [_] [] []). apply Tensrule_I.
apply (mergeLI _ (mergeRI _ merge_nil)).
apply merge_nil.
reflexivity. simpl.
apply (dlCons (maell_idr _) (dlCons (maell_idr _) (dlNil _ _))). Qed.

Lemma wthD1 {V} A B : derrec maell_rules emptyT [@lolli V (wth A B) A].
Proof. apply lolli_sI.  eapply derI.  apply princ_maellI.
eapply (OSgctxt_eq _ _ _ [] [_]).  apply PlusL_p.
apply PlusLrule_I. reflexivity. reflexivity.
apply dersrec_singleI. sfs. apply maell_idr. Qed.

Lemma wthD2 {V} A B : derrec maell_rules emptyT [@lolli V (wth A B) B].
Proof. apply lolli_sI.  eapply derI.  apply princ_maellI.
eapply (OSgctxt_eq _ _ _ [] [_]).  apply PlusR_p.
apply PlusRrule_I. reflexivity. reflexivity.
apply dersrec_singleI. sfs. apply maell_idr. Qed.

Lemma PlusI1 {V} A B : derrec maell_rules emptyT [@lolli V A (plus A B)].
Proof. apply lolli_sI.  eapply derI.  apply princ_maellI.
eapply (OSgctxt_eq _ _ _ [_] []).  apply PlusL_p.
apply PlusLrule_I. reflexivity. reflexivity.
apply dersrec_singleI. sfs. apply maell_idr. Qed.

Lemma PlusI2 {V} A B : derrec maell_rules emptyT [@lolli V B (plus A B)].
Proof. apply lolli_sI.  eapply derI.  apply princ_maellI.
eapply (OSgctxt_eq _ _ _ [_] []).  apply PlusR_p.
apply PlusRrule_I. reflexivity. reflexivity.
apply dersrec_singleI. sfs. apply maell_idr. Qed.

Lemma lolli_mp {V} A B : derrec maell_rules emptyT
  [@lolli V (tens (lolli A B) A) B].
Proof. apply lolli_sI.  unfold lolli. simpl. rewrite dual_dual.
eapply derI.  apply princ_maellI.
eapply (OSgctxt_eq _ _ _ [] [_]).
apply Par_p.  apply Parrule_I.
reflexivity.  reflexivity.
sfs.  apply dersrec_singleI.
eapply derI.  apply tens_maellI.
eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [] [] [_] [_]). apply Tensrule_I.
apply merge_nil.
apply (mergeLI _ (mergeRI _ merge_nil)).
reflexivity. simpl.
apply (dlCons (maell_id _) (dlCons (maell_idr _) (dlNil _ _))). Qed.

(* and todo also associativity of binary operators, and curry/uncurry *)


