
Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT ddT.
Require Import fmlsext.
Require Import lldefs.
Require Import gstep.

Lemma princ_paramL W (A : W) rules dual any prs x xs ys psa psb ca cb :
  fmlsrule (x :: xs) ys prs psa ca -> 
  rsub (fmlsruleg prs) rules -> 
  gen_step2 (ossca dual rules) A any (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb.
Proof. intros fpa rsr. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpr.
apply osscaI. intros. subst.
inversion fpa. subst. clear fpa.
eapply derI. apply (rsubD rsr). rewrite - !app_assoc.
eapply OSgctxt_eq. apply X. reflexivity. reflexivity.
apply dersrecI_forall. intros c0 inmf.
apply InT_mapE in inmf. cD.
eapply ForallTD_forall in fpl.
2: apply (InT_map _ inmf1).
destruct fpl. destruct o. subst.
unfold fmlsext.  unfold fmlsext in d0. simpl in d0.
specialize (d0 _ _ eq_refl eq_refl).
rewrite - !app_assoc in d0. exact d0. Qed.

Lemma princ_paramR W (A : W) rules dual any prs x xs ys psa psb ca cb :
  fmlsrule (x :: xs) ys prs psb cb -> 
  rsub (fmlsruleg prs) rules -> 
  gen_step2 (ossca dual rules) A any (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb.
Proof. intros fpb rsr. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpl.
apply osscaI. intros. subst.
inversion fpb. subst. clear fpb.
eapply derI. apply (rsubD rsr). rewrite app_assoc.
eapply OSgctxt_eq. apply X. reflexivity. reflexivity.
apply dersrecI_forall. intros c0 inmf.
apply InT_mapE in inmf. cD.
eapply ForallTD_forall in fpr.
2: apply (InT_map _ inmf1).
destruct fpr. destruct o. subst.
unfold fmlsext.  unfold fmlsext in d0. simpl in d0.
specialize (d0 _ _ eq_refl eq_refl).
rewrite - !app_assoc. exact d0. Qed.

Check princ_paramL.  Check princ_paramR.

Lemma merge_paramL V (A : LLfml V) rules dual any prs x xs ys psa psb ca cb :
  merge_ctxt (x :: xs) ys prs psa ca -> rsub (merge_ctxtg prs) rules -> 
  gen_step2 (ossca dual rules) A any (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb.
Proof. intros mcp rsmr. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpr.
apply osscaI. intros. subst.
inversion mcp. clear mcp. inversion H2 ; subst ; clear H2. 
- apply ForallT_2D in fpl. cD. clear fpl fpl1.
destruct fpl2. simpl in d.
specialize (d _ _ eq_refl eq_refl).
rewrite <- !app_assoc in d. clear dl dr.
eapply derI. apply (rsubD rsmr). 
eapply merge_ctxtgI. rewrite - !app_assoc.
apply (merge_ctxtI _ _ _ _ X H7 (merge_app H3 (merge_Rnil rs))).
rewrite app_nil_r.
apply dersrecI_all. apply ForallT_2I ; assumption. 
- apply ForallT_2D in fpl. cD. clear fpl0 fpl2.
destruct fpl1. 
specialize (d _ _ eq_refl eq_refl).
rewrite <- !app_assoc in d. clear dl dr.
eapply derI. apply (rsubD rsmr). 
eapply merge_ctxtgI. rewrite - !app_assoc.
apply (merge_ctxtI _ _ _ _ X H7 (merge_app H3 (merge_Lnil rs))).
rewrite app_nil_r.
apply dersrecI_all. apply ForallT_2I ; assumption. Qed.

Lemma merge_paramR V (A : LLfml V) rules dual any prs x xs ys psa psb ca cb :
  merge_ctxt (x :: xs) ys prs psb cb -> rsub (merge_ctxtg prs) rules -> 
  gen_step2 (ossca dual rules) A any (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb.
Proof. intros mcp rsmr. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpl dl dr.
apply osscaI. intros. subst.
inversion mcp. clear mcp. inversion H2 ; subst ; clear H2. 
- apply ForallT_2D in fpr. cD. clear fpr fpr1.
destruct fpr2. simpl in d.
specialize (d _ _ eq_refl eq_refl).
eapply derI. apply (rsubD rsmr). 
eapply merge_ctxtgI. rewrite app_assoc.
apply (merge_ctxtI _ _ _ _ X (merge_app (merge_Rnil ls) H7) H3).
simpl. rewrite - !app_assoc.
apply dersrecI_all. apply ForallT_2I ; assumption. 
- apply ForallT_2D in fpr. cD. clear fpr0 fpr2.
destruct fpr1. simpl in d.
specialize (d _ _ eq_refl eq_refl).
eapply derI. apply (rsubD rsmr). 
eapply merge_ctxtgI. rewrite app_assoc.
apply (merge_ctxtI _ _ _ _ X (merge_app (merge_Lnil ls) H7) H3).
simpl. rewrite - app_assoc.
apply dersrecI_all. apply ForallT_2I ; assumption. Qed.

Check merge_paramL.  Check merge_paramR.

Lemma plusL_wth V (A : LLfml V) rules ys zs psa psb ca cb :
  fmlsrule [] ys PlusLrule psa ca -> 
  fmlsrule [] zs Wthrule psb cb -> 
  gen_step2 (ossca dual rules) A isubfml (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb.
Proof. intros psca pscb. unfold gen_step2.
intros sub fpl fpr dl dr. clear dl dr.
apply osscaI. intros. subst.
inversion psca. subst. clear psca. 
inversion pscb. subst. clear pscb. 
destruct X. destruct X0.
unfold fmlsext in H1. unfold fmlsext in H2.
simpl in H1. simpl in H2.
injection H1 as. injection H2 as.
subst. simpl in H1. injection H1 as. subst.
simpl in fpl. simpl in fpr.
unfold fmlsext in fpl. unfold fmlsext in fpr.
simpl in fpl. simpl in fpr.
inversion fpl. inversion fpr. clear X0 X2 fpl fpr.
cD. clear X0 X2. subst.
specialize (sub A0 (isub_plusL _ _) _ X _ X1).
destruct sub.  exact (d _ _ eq_refl eq_refl).  Qed.

Lemma plusR_wth V (A : LLfml V) rules ys zs psa psb ca cb :
  fmlsrule [] ys PlusRrule psa ca -> 
  fmlsrule [] zs Wthrule psb cb -> 
  gen_step2 (ossca dual rules) A isubfml (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb.
Proof. intros psca pscb. unfold gen_step2.
intros sub fpl fpr dl dr. clear dl dr.
apply osscaI. intros. subst.
inversion psca. subst. clear psca. 
inversion pscb. subst. clear pscb. 
destruct X. destruct X0.
unfold fmlsext in H1. unfold fmlsext in H2.
simpl in H1. simpl in H2.
injection H1 as. injection H2 as.
subst. simpl in H1. injection H1 as. subst.
simpl in fpl. simpl in fpr.
unfold fmlsext in fpl. unfold fmlsext in fpr.
simpl in fpl. simpl in fpr.
inversion fpl. inversion fpr. inversion X2. clear X0 X2 X4 fpl fpr.
cD. clear X0 X2. subst.
specialize (sub B (isub_plusR _ _) _ X _ X3).
destruct sub.  exact (d _ _ eq_refl eq_refl).  Qed.

Check plusL_wth.  Check plusR_wth.

(* won't work because of conclusion changes from
  derrec rules emptyT (ls ++ rs) to derrec rules emptyT (rs ++ ls)
how about a version of cut where any merge of the contexts is derivable?
Lemma gs2_ossca_dual V (A : LLfml V) rules sub psa ca psb cb :
  gen_step2 (ossca dual rules) A sub (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb ->
  gen_step2 (ossca dual rules) (dual A) sub (derrec rules emptyT)
         (derrec rules emptyT) psb cb psa ca.
*)	

Lemma wth_plusL V (A : LLfml V) rules ys zs psa psb ca cb :
  fmlsrule [] ys Wthrule psa ca -> 
  fmlsrule [] zs PlusLrule psb cb -> 
  gen_step2 (ossca dual rules) A isubfml (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb.
Proof. intros psca pscb. unfold gen_step2.
intros sub fpl fpr dl dr. clear dl dr.
apply osscaI. intros. subst.
inversion psca. subst. clear psca. 
inversion pscb. subst. clear pscb. 
destruct X. destruct X0.
unfold fmlsext in H1. unfold fmlsext in H2.
simpl in H1. simpl in H2.
injection H1 as. injection H2 as.
subst. simpl in H1. injection H1 as. subst.
simpl in fpl. simpl in fpr.
unfold fmlsext in fpl. unfold fmlsext in fpr.
simpl in fpl. simpl in fpr.
inversion fpl. inversion fpr. inversion X0. clear X0 X2 X4 fpl fpr.
cD. clear X0 X2. subst.
specialize (sub A0 (isub_wthL _ _) _ X _ X1).
destruct sub.  exact (d _ _ eq_refl eq_refl).  Qed.

Lemma wth_plusR V (A : LLfml V) rules ys zs psa psb ca cb :
  fmlsrule [] ys Wthrule psa ca -> 
  fmlsrule [] zs PlusRrule psb cb -> 
  gen_step2 (ossca dual rules) A isubfml (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb.
Proof. intros psca pscb. unfold gen_step2.
intros sub fpl fpr dl dr. clear dl dr.
apply osscaI. intros. subst.
inversion psca. subst. clear psca. 
inversion pscb. subst. clear pscb. 
destruct X. destruct X0.
unfold fmlsext in H1. unfold fmlsext in H2.
simpl in H1. simpl in H2.
injection H1 as. injection H2 as.
subst. simpl in H1. injection H1 as. subst.
simpl in fpl. simpl in fpr.
unfold fmlsext in fpl. unfold fmlsext in fpr.
simpl in fpl. simpl in fpr.
inversion fpl. inversion fpr. inversion X0. clear X0 X2 X4 fpl fpr.
cD. clear X0 X2. subst.
specialize (sub B (isub_wthR _ _) _ X3 _ X1).
destruct sub.  exact (d _ _ eq_refl eq_refl).  Qed.

Check wth_plusL.  Check wth_plusR.

