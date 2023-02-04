

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
(* Require Import ll_camq. below - to show where we use cut adm *)

Lemma query_csI {V} lc A fs :
  derrec maell_rules emptyT (lc ++ A :: fs) ->
  derrec maell_rules emptyT (lc ++ @Query V A :: fs).
Proof. intros.  eapply derI.  apply query_maellI.
eapply (OSgctxt_eq _ _ _ lc _).  eapply Queryrule_I.
reflexivity.  reflexivity.  apply (dersrec_singleI X). Qed.

Definition query_sI {V} A fs := @query_csI V [] A fs.

Lemma bang_csI {V} lc A fs :
  derrec maell_rules emptyT (map (@Query V) lc ++ A :: map (@Query V) fs) ->
  derrec maell_rules emptyT (map (@Query V) lc ++ Bang A :: map (@Query V) fs).
Proof. intros.  eapply derI.  eapply bang_maellI.
eapply (fmlsrulegq_I _ _ lc fs). eapply Bangrule_I.
reflexivity.  reflexivity.  reflexivity.  reflexivity.
apply (dersrec_singleI X). Qed.

Lemma ctr_csI {V} lc A fs :
  derrec maell_rules emptyT (lc ++ Query A :: Query A :: fs) ->
  derrec maell_rules emptyT (lc ++ @Query V A :: fs).
Proof. intros.  eapply derI.  eapply ctr_maellI.
eapply (OSgctxt_eq _ _ _ lc _).  apply ctrrule_I.
reflexivity.  reflexivity.  apply (dersrec_singleI X). Qed.

Lemma wk_csI {V} lc A fs :
  derrec maell_rules emptyT (lc ++ fs) ->
  derrec maell_rules emptyT (lc ++ @Query V A :: fs).
Proof. intros.  eapply derI.  eapply wk_maellI.
eapply (OSgctxt_eq _ _ _ lc _).  apply wkrule_I.
reflexivity.  reflexivity.  apply (dersrec_singleI X). Qed.

Definition wk_sI {V} A fs := @wk_csI V [] A fs.

Lemma wth_csI {V} lc A B fs :
  derrec maell_rules emptyT (lc ++ A :: fs) ->
  derrec maell_rules emptyT (lc ++ B :: fs) ->
  derrec maell_rules emptyT (lc ++ @wth V A B :: fs).
Proof. intros.  eapply derI.  apply princ_maellI.  
eapply (OSgctxt_eq _ _ _ lc _).  apply Wth_p.  apply Wthrule_I.
reflexivity. reflexivity.  apply (dlCons X (dersrec_singleI X0)). Qed.

Definition wth_sI {V} A B fs := @wth_csI V [] A B fs.
Definition wth_2sI {V} A B f fs := @wth_csI V [f] A B fs.

Lemma plusL_csI {V} lc A B fs :
  derrec maell_rules emptyT (lc ++ A :: fs) ->
  derrec maell_rules emptyT (lc ++ @plus V A B :: fs).
Proof. intro.  eapply derI.  apply princ_maellI.  
eapply (OSgctxt_eq _ _ _ lc _).  apply PlusL_p.  apply PlusLrule_I.
reflexivity. reflexivity.  apply (dersrec_singleI X). Qed.

Lemma plusR_csI {V} lc A B fs :
  derrec maell_rules emptyT (lc ++ B :: fs) ->
  derrec maell_rules emptyT (lc ++ @plus V A B :: fs).
Proof. intro.  eapply derI.  apply princ_maellI.  
eapply (OSgctxt_eq _ _ _ lc _).  apply PlusR_p.  apply PlusRrule_I.
reflexivity. reflexivity.  apply (dersrec_singleI X). Qed.

Definition plusL_sI {V} A B fs := @plusL_csI V [] A B fs.
Definition plusL_2sI {V} A B f fs := @plusL_csI V [f] A B fs.
Definition plusR_sI {V} A B fs := @plusR_csI V [] A B fs.
Definition plusR_2sI {V} A B f fs := @plusR_csI V [f] A B fs.

Lemma par_csI {V} lc A B fs :
  derrec maell_rules emptyT (lc ++ A :: B :: fs) ->
  derrec maell_rules emptyT (lc ++ @par V A B :: fs).
Proof. intro.  eapply derI.  apply princ_maellI.  
eapply (OSgctxt_eq _ _ _ lc _).  apply Par_p.  apply Parrule_I.
reflexivity. reflexivity.  apply (dersrec_singleI X). Qed.

Definition par_sI {V} A B fs := @par_csI V [] A B fs.
Definition par_2sI {V} A B f fs := @par_csI V [f] A B fs.
Definition par_3sI {V} A B f1 f2 fs := @par_csI V [f1 ; f2] A B fs.

Lemma lolli_refl {V} A : derrec maell_rules emptyT [@lolli V A A].
Proof. apply par_sI.  apply maell_idr. Qed.

Lemma wpc_lem {V} A B :
  derrec maell_rules emptyT [plus (dual A) (dual B); @wth V B A].
Proof. apply wth_2sI. apply plusR_sI. apply maell_idr.
apply plusL_sI. apply maell_idr. Qed.

Lemma wth_comm {V} A B : 
  derrec maell_rules emptyT [@lolli V (wth A B) (wth B A)].
Proof. apply par_sI. apply wpc_lem. Qed.

Lemma ptc_lem {V} A B :
  derrec maell_rules emptyT [tens (dual A) (dual B) ; @par V B A].
(* proof rather similar to that of maell_id *)
Proof. apply par_2sI.
eapply derI. apply tens_maellI.  eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [] [] [A] [B]). apply Tensrule_I.
apply merge_nil. apply merge_simple_appr.  reflexivity. simpl.
apply (dlCons (maell_idr _) (dlCons (maell_idr _) (dlNil _ _))). Qed.

Lemma par_comm {V} A B : 
  derrec maell_rules emptyT [@lolli V (par A B) (par B A)].
Proof.  apply par_sI. apply ptc_lem. Qed.

(* can do tens_comm and plus_comm similar to above, 
  but a bit quicker to use exchange as follows *)
Lemma tens_comm {V} A B : 
  derrec maell_rules emptyT [@lolli V (tens A B) (tens B A)].
Proof.  apply par_sI.  eapply exch_maell. 2: apply swapped_cc.
pose (ptc_lem (dual B) (dual A)).
clearbody d. rewrite !dual_dual in d. exact d. Qed.

Lemma plus_comm {V} A B : 
  derrec maell_rules emptyT [@lolli V (plus A B) (plus B A)].
Proof.  apply par_sI.  eapply exch_maell. 2: apply swapped_cc.
pose (wpc_lem (dual B) (dual A)).
clearbody d. rewrite !dual_dual in d. exact d. Qed.

Lemma lolli_dual {V} A B : derrec maell_rules emptyT 
  [@lolli V (lolli A B) (lolli (dual B) (dual A))].
Proof. apply par_sI.  unfold lolli. simpl. rewrite !dual_dual.
pose (ptc_lem (dual A) B).
clearbody d. rewrite !dual_dual in d. exact d. Qed.

(* some rules in form using lolli *)
Lemma tensI {V} A B : derrec maell_rules emptyT
  [@lolli V A (lolli B (tens A B))].
Proof. apply par_sI. apply par_2sI.  
eapply derI.  apply tens_maellI.  eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [_] [_] [] []). apply Tensrule_I.
apply merge_simple_app.  apply merge_nil.  reflexivity. simpl.
apply (dlCons (maell_idr _) (dlCons (maell_idr _) (dlNil _ _))). Qed.

Lemma wthD1 {V} A B : derrec maell_rules emptyT [@lolli V (wth A B) A].
Proof. apply par_sI.  eapply derI.  apply princ_maellI.
eapply (OSgctxt_eq _ _ _ [] [_]).  apply PlusL_p.
apply PlusLrule_I. reflexivity. reflexivity.
apply dersrec_singleI. sfs. apply maell_idr. Qed.

Lemma wthD2 {V} A B : derrec maell_rules emptyT [@lolli V (wth A B) B].
Proof. apply par_sI.  eapply derI.  apply princ_maellI.
eapply (OSgctxt_eq _ _ _ [] [_]).  apply PlusR_p.
apply PlusRrule_I. reflexivity. reflexivity.
apply dersrec_singleI. sfs. apply maell_idr. Qed.

Lemma PlusI1 {V} A B : derrec maell_rules emptyT [@lolli V A (plus A B)].
Proof. apply par_sI.  eapply derI.  apply princ_maellI.
eapply (OSgctxt_eq _ _ _ [_] []).  apply PlusL_p.
apply PlusLrule_I. reflexivity. reflexivity.
apply dersrec_singleI. sfs. apply maell_idr. Qed.

Lemma PlusI2 {V} A B : derrec maell_rules emptyT [@lolli V B (plus A B)].
Proof. apply par_sI.  eapply derI.  apply princ_maellI.
eapply (OSgctxt_eq _ _ _ [_] []).  apply PlusR_p.
apply PlusRrule_I. reflexivity. reflexivity.
apply dersrec_singleI. sfs. apply maell_idr. Qed.

Lemma lolli_mp {V} A B : derrec maell_rules emptyT
  [@lolli V (tens (lolli A B) A) B].
Proof. apply par_sI.  unfold lolli. simpl. rewrite dual_dual.  apply par_sI.
eapply derI.  apply tens_maellI.  eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [] [] [_] [_]). apply Tensrule_I.
apply merge_nil.  apply merge_simple_app.  reflexivity. simpl.
apply (dlCons (maell_id _) (dlCons (maell_idr _) (dlNil _ _))). Qed.

(* associativity of binary operators, and curry/uncurry *)
Lemma tens_lem {V} A B fs : derrec maell_rules emptyT (B ::fs) ->
  derrec maell_rules emptyT (@tens V A B :: dual A ::fs).
Proof. intro. 
eapply derI.  apply tens_maellI.  eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [] [] [_]). apply Tensrule_I.
apply merge_nil.  apply merge_simple_app.  reflexivity. simpl.
apply (dlCons (maell_id _)). exact (dersrec_singleI X). Qed.

Lemma tens_lemd {V} A B fs : derrec maell_rules emptyT (B ::fs) ->
  derrec maell_rules emptyT (@tens V (dual A) B :: A ::fs).
Proof. intro b. pose (tens_lem (dual A) b). 
clearbody d. rewrite dual_dual in d. exact d. Qed.

Lemma tens_assoc1_lem {V} A B C : derrec maell_rules emptyT
  [@tens V A (tens B (dual C)) ; dual A ; dual B ; C].
Proof. apply tens_lem.  apply tens_lem. apply maell_idr. Qed.

Lemma tens_assoc2_lem {V} A B C : derrec maell_rules emptyT
  [@tens V (tens A B) (dual C) ; dual A ; dual B ; C].
Proof. eapply derI.  apply tens_maellI.  eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [] [] [_ ; _]). apply Tensrule_I.
apply merge_nil.  apply merge_simple_app.  reflexivity. simpl.
apply dlCons. apply tens_lem. apply maell_id. 
apply dersrec_singleI. apply maell_idr.  Qed.

Lemma ll_uncurry {V} A B C : derrec maell_rules emptyT
  [@lolli V (lolli A (lolli B C)) (lolli (tens A B) C)].
Proof. apply par_sI.  apply par_2sI.  simpl. rewrite !dual_dual.
apply par_2sI. apply tens_lem. apply tens_lem.  apply maell_idr. Qed.

Lemma ll_curry {V} A B C : derrec maell_rules emptyT
  [@lolli V (lolli (tens A B) C) (lolli A (lolli B C))].
Proof. apply par_sI.  apply par_2sI.  apply par_3sI.
simpl. rewrite !dual_dual. apply tens_assoc2_lem. Qed.

Lemma par_assoc1 {V} A B C : derrec maell_rules emptyT
  [@lolli V (par A (par B C)) (par (par A B) C)].
Proof. apply par_sI.  apply par_2sI.  apply par_2sI. simpl.
pose (tens_assoc1_lem (dual A) (dual B) C).
clearbody d. rewrite !dual_dual in d. exact d. Qed.

Lemma par_assoc2 {V} A B C : derrec maell_rules emptyT
  [@lolli V (par (par A B) C) (par A (par B C))].
Proof. apply par_sI.  apply par_2sI.  apply par_3sI. simpl.
pose (tens_assoc2_lem (dual A) (dual B) C).
clearbody d. rewrite !dual_dual in d. exact d. Qed.

(* similarly tens_assoc1/2 *)

Lemma lolli_trans {V} A B C : derrec maell_rules emptyT
  [@lolli V (lolli A B) (lolli (lolli B C) (lolli A C))].
Proof. apply par_sI.  apply par_2sI. simpl.  rewrite !dual_dual.
apply par_3sI. eapply exch_maell.
2: apply (swapped_I [_] [_] [_] [_] eq_refl eq_refl). 
apply tens_lem.  eapply exch_maell. 2: apply swapped_cc. simpl.
apply tens_lem. apply maell_idr. Qed.

Lemma ll_C {V} A B C : derrec maell_rules emptyT
  [@lolli V (lolli A (lolli B C)) (lolli B (lolli A C))].
Proof. apply par_sI.  apply par_2sI.  apply par_3sI. simpl.
rewrite !dual_dual.  eapply exch_maell.
2: apply (swapped_I [_] [_] [_] [_] eq_refl eq_refl). 
apply tens_lem.  apply tens_lem. apply maell_idr. Qed.

Lemma plus_assoc1 {V} A B C : derrec maell_rules emptyT
  [@lolli V (plus A (plus B C)) (plus (plus A B) C)].
Proof. apply par_sI. simpl. apply wth_sI.
apply plusL_2sI. apply plusL_2sI.  apply maell_idr.
apply wth_sI.  apply plusL_2sI. apply plusR_2sI.  apply maell_idr.
apply plusR_2sI.  apply maell_idr. Qed.

Lemma plus_assoc2 {V} A B C : derrec maell_rules emptyT
  [@lolli V (plus (plus A B) C) (plus A (plus B C))].
Proof. apply par_sI. simpl. apply wth_sI.
apply wth_sI.  apply plusL_2sI.  apply maell_idr.
apply plusR_2sI. apply plusL_2sI.  apply maell_idr.
apply plusR_2sI. apply plusR_2sI.  apply maell_idr. Qed.

Lemma wth_assoc1 {V} A B C : derrec maell_rules emptyT
  [@lolli V (wth A (wth B C)) (wth (wth A B) C)].
Proof. apply par_sI. simpl. apply wth_2sI.
apply wth_2sI.  apply plusL_sI.  apply maell_idr.
apply plusR_sI. apply plusL_sI.  apply maell_idr.
apply plusR_sI. apply plusR_sI.  apply maell_idr. Qed.

Lemma wth_assoc2 {V} A B C : derrec maell_rules emptyT
  [@lolli V (wth (wth A B) C) (wth A (wth B C))].
Proof. apply par_sI. simpl. apply wth_2sI.
apply plusL_sI. apply plusL_sI.  apply maell_idr.
apply wth_2sI.  apply plusL_sI. apply plusR_sI.  apply maell_idr.
apply plusR_sI.  apply maell_idr. Qed.

Definition tens_lem' {V} A B := @tens_lem V A B _ (maell_id _).

Lemma dpar_lem {V} A B : derrec maell_rules emptyT
  (dual (@par V A B) :: [A ; B]).
Proof. pose (tens_lem' (dual A) (dual B)).
clearbody d.  rewrite !dual_dual in d. exact d. Qed.

(* results involving invertibility of rules, etc, need cut adm,
  not required for results above *)
Require Import ll_camq.

Lemma par_inv {V} A B rc : 
  derrec maell_rules emptyT (@par V A B :: rc) -> 
  derrec maell_rules emptyT (A :: B :: rc).
Proof. intro dp.
pose (cut_adm_maell_Q (par A B) dp (dpar_lem A B)).
inversion o. clear o X0. inversion X.
exact (X0 _ _ _ eq_refl eq_refl (merge_simple_appr _ _)). Qed.

Lemma use_lolli {V} A B rc : derrec maell_rules emptyT [@lolli V A B] ->
  derrec maell_rules emptyT (A :: rc) -> derrec maell_rules emptyT (B :: rc).
Proof. intros lab ac.
pose (cut_adm_maell_Q A ac (par_inv lab)).
inversion o. clear o X0. inversion X.
exact (X0 _ _ _ eq_refl eq_refl (merge_simple_appr _ _)). Qed.

(* -o and so eqv are congruences *)
Lemma parL_cong {V} A B C rc : derrec maell_rules emptyT (@lolli V A B :: rc) ->
  derrec maell_rules emptyT (lolli (par C A) (par C B) :: rc).
Proof. intro lab. apply par_sI. apply par_2sI. simpl.
apply tens_lemd.  apply par_inv. exact lab. Qed.

Lemma tensL_cong {V} A B C rc : 
  derrec maell_rules emptyT (@lolli V A B :: rc) ->
  derrec maell_rules emptyT (lolli (tens C A) (tens C B) :: rc).
Proof. intro lab.
eapply (use_lolli (lolli_dual _ _)) in lab.
apply (parL_cong (dual C)) in lab.
apply (use_lolli (lolli_dual _ _)) in lab.
simpl in lab. rewrite !dual_dual in lab. exact lab. Qed.

Lemma plusL_cong {V} A B C : 
  derrec maell_rules emptyT [@lolli V A B] ->
  derrec maell_rules emptyT [lolli (plus C A) (plus C B)].
Proof. intro lab. apply par_sI. simpl. apply wth_sI.
apply plusL_2sI. apply maell_idr.
apply plusR_2sI. exact (par_inv lab). Qed.

Lemma wthL_cong {V} A B C : 
  derrec maell_rules emptyT [@lolli V A B] ->
  derrec maell_rules emptyT [lolli (wth C A) (wth C B)].
Proof. intro lab. apply par_sI. simpl. apply wth_2sI.
apply plusL_sI. apply maell_idr.
apply plusR_sI. exact (par_inv lab). Qed.

Lemma query_cong {V} A B : 
  derrec maell_rules emptyT [@lolli V A B] ->
  derrec maell_rules emptyT [lolli (Query A) (Query B)].
Proof. intro lab. apply par_sI. simpl.
apply (bang_csI [] _ [_]). apply (query_csI [_]). exact (par_inv lab). Qed.

Lemma bang_cong {V} A B : 
  derrec maell_rules emptyT [@lolli V A B] ->
  derrec maell_rules emptyT [lolli (Bang A) (Bang B)].
Proof. intro lab.
eapply (use_lolli (lolli_dual _ _)) in lab.
apply query_cong in lab.
apply (use_lolli (lolli_dual _ _)) in lab.
simpl in lab. rewrite !dual_dual in lab. exact lab. Qed.

(* from these could get congruence of eqv *)

(* equivalences in the wikipedia page *)
Lemma par_wth_fwd {V} A B C : derrec maell_rules emptyT
  [@lolli V (par A (wth B C)) (wth (par A B) (par A C))].
Proof. apply par_sI.  simpl. apply wth_2sI ; apply par_2sI ; apply tens_lemd.
- apply plusL_sI. apply maell_idr.
- apply plusR_sI. apply maell_idr. Qed.

Lemma par_wth_bwd {V} A B C : derrec maell_rules emptyT
  [@lolli V (wth (par A B) (par A C)) (par A (wth B C))].
Proof. apply par_sI.  simpl. apply par_2sI.  apply (wth_csI [_ ; _]).
- apply plusL_sI. apply tens_lemd. apply maell_idr.
- apply plusR_sI. apply tens_lemd. apply maell_idr. Qed.

Lemma tens_plus_fwd {V} A B C : derrec maell_rules emptyT
  [@lolli V (tens A (plus B C)) (plus (tens A B) (tens A C))].
Proof. pose (par_wth_bwd (dual A) (dual B) (dual C)).
eapply (use_lolli (lolli_dual _ _)) in d. simpl in d.
rewrite !dual_dual in d. exact d. Qed.

Lemma tens_plus_bwd {V} A B C : derrec maell_rules emptyT
  [@lolli V (plus (tens A B) (tens A C)) (tens A (plus B C))].
Proof. pose (par_wth_fwd (dual A) (dual B) (dual C)).
eapply (use_lolli (lolli_dual _ _)) in d. simpl in d.
rewrite !dual_dual in d. exact d. Qed.

Lemma bang_wth_bwd {V} A B : derrec maell_rules emptyT
  [@lolli V (tens (Bang A) (Bang B)) (Bang (wth A B))].
Proof. apply par_sI. simpl. apply par_sI. simpl.
apply (bang_csI [_ ; _] _ []).  simpl.  apply (wth_csI [_ ; _]).
- apply (wk_csI [_]).  apply query_sI.  apply maell_idr.
- apply wk_sI.  apply query_sI.  apply maell_idr. Qed.

Lemma bang_wth_fwd {V} A B : derrec maell_rules emptyT
  [@lolli V (Bang (wth A B)) (tens (Bang A) (Bang B))].
Proof. apply par_sI. simpl. apply (ctr_csI []).
eapply derI.  apply tens_maellI.  eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [_] [_] [] []). apply Tensrule_I.
apply merge_simple_app.  apply merge_nil.  reflexivity. simpl.
apply dlCons.  apply (bang_csI [_] _ []). apply query_sI.
apply plusL_sI. apply maell_idr.
apply dersrec_singleI.  apply (bang_csI [_] _ []). apply query_sI.
apply plusR_sI. apply maell_idr. Qed.

Lemma query_plus_fwd {V} A B : derrec maell_rules emptyT
  [@lolli V (Query (plus A B)) (par (Query A) (Query B))].
Proof. pose (bang_wth_bwd (dual A) (dual B)).
eapply (use_lolli (lolli_dual _ _)) in d. simpl in d.
rewrite !dual_dual in d. exact d. Qed.

Lemma query_plus_bwd {V} A B : derrec maell_rules emptyT
  [@lolli V (par (Query A) (Query B)) (Query (plus A B))].
Proof. pose (bang_wth_fwd (dual A) (dual B)).
eapply (use_lolli (lolli_dual _ _)) in d. simpl in d.
rewrite !dual_dual in d. exact d. Qed.

Print Implicit query_plus_bwd.

(* linear distribution *)
Lemma lin_dist {V} A B C : derrec maell_rules emptyT
  [@lolli V (tens A (par B C)) (par (tens A B) C)].
Proof. apply par_sI. simpl. apply par_2sI.  apply par_sI.  eapply exch_maell.
2: apply (swapped_I [] [_] [_ ; _] [_] eq_refl eq_refl). 
apply tens_lem.  eapply exch_maell.
2: apply (swapped_I [] [_] [_] [_] eq_refl eq_refl). 
apply tens_lemd. apply maell_idr. Qed.

(* one-directional distributivity formulae *)
Lemma bang_tens {V} A B : derrec maell_rules emptyT
  [@lolli V (tens (Bang A) (Bang B)) (Bang (tens A B))].
Proof. apply par_sI. simpl. apply par_sI.
apply (bang_csI [_ ; _] _ []). simpl.
eapply derI.  apply tens_maellI.  eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [_] [_] [] []). apply Tensrule_I.
apply merge_simple_app.  apply merge_nil.  reflexivity. simpl.
apply dlCons. apply query_sI. apply maell_idr.
apply dersrec_singleI. apply query_sI. apply maell_idr. Qed.

Lemma bang_plus {V} A B : derrec maell_rules emptyT
  [@lolli V (plus (Bang A) (Bang B)) (Bang (plus A B))].
Proof. apply par_sI. simpl. 
apply wth_sI ; apply (bang_csI [_] _ []) ; apply query_sI ; simpl.
apply plusL_2sI. apply maell_idr.  apply plusR_2sI. apply maell_idr. Qed.

Lemma query_par {V} A B : derrec maell_rules emptyT
  [@lolli V (Query (par A B)) (par (Query A) (Query B))].
Proof. pose (bang_tens (dual A) (dual B)).
eapply (use_lolli (lolli_dual _ _)) in d. simpl in d.
rewrite !dual_dual in d. exact d. Qed.

Lemma query_wth {V} A B : derrec maell_rules emptyT
  [@lolli V (Query (wth A B)) (wth (Query A) (Query B))].
Proof. pose (bang_plus (dual A) (dual B)).
eapply (use_lolli (lolli_dual _ _)) in d. simpl in d.
rewrite !dual_dual in d. exact d. Qed.

Lemma par_plus {V} A B C : derrec maell_rules emptyT
  [@lolli V (plus (par A C) (par B C)) (par (plus A B) C)].
Proof. apply par_sI. simpl. apply par_2sI. simpl.
apply wth_sI. apply plusL_2sI. apply tens_lemd. apply maell_idr.
apply plusR_2sI. apply tens_lemd. apply maell_idr. Qed.

Lemma tens_wth {V} A B C : derrec maell_rules emptyT
  [@lolli V (tens (wth A B) C) (wth (tens A C) (tens B C))].
Proof. pose (par_plus (dual A) (dual B) (dual C)).
eapply (use_lolli (lolli_dual _ _)) in d. simpl in d.
rewrite !dual_dual in d. exact d. Qed.

Lemma plus_wth {V} A B C : derrec maell_rules emptyT
  [@lolli V (plus (wth A B) C) (wth (plus A C) (plus B C))].
Proof. apply par_sI. simpl. apply wth_2sI ; apply wth_sI.
- apply plusL_sI. apply plusL_2sI. apply maell_idr.
- apply plusR_2sI. apply maell_idr.
- apply plusR_sI. apply plusL_2sI. apply maell_idr.
- apply plusR_2sI. apply maell_idr. Qed.

Lemma wth_plus {V} A B C : derrec maell_rules emptyT
  [@lolli V (plus (wth A C) (wth B C)) (wth (plus A B) C)].
Proof. pose (plus_wth (dual A) (dual B) (dual C)).
eapply (use_lolli (lolli_dual _ _)) in d. simpl in d.
rewrite !dual_dual in d. exact d. Qed.

(* also, lolli A bot is equivalent (inter-derivable) to dual A *)



