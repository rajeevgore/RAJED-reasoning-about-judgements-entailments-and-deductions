
(* LJA logic, using lists of formulae - cut-admissibility *)
(* lemmas in Roy Dyckhoff and Sara Negri,
Admissibility of Structural Rules for Contraction-Free Systems of
Intuitionistic Logic, JSL 65 (2000), 1499-1518 *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT dd_fc.
Require Import List_lemmasT swappedT.
Require Import gen_tacs.
Require Import gen_seq gstep gentree rtcT.
Require Import ljt ljt_inv ljt_dn ljt_ctr ljt_ca ljt_dncc.
Require Import Coq.Program.Basics.
(* Require Import ljt_dnca. TMP *)

Check (gs2_sr_princ_sub_mono (@isub_dnsub _)).

Definition lja_lrlsR_rrlsL V fml la lc rc G1 G2 D psl psr :=
  @gen_lrlsR_rrlsL V LJAncrules fml la lc rc G1 G2 D psl psr (@lctr_adm_lja V).
Definition lja_lrlsR_rrlsLe V fml lc rc G1 G2 D psl psr :=
  @gen_lrlsR_rrlsL V LJAncrules fml [] lc rc G1 G2 D psl psr (@lctr_adm_lja V).

Lemma lja_ImpR_ImpL V fml la lc rc Γ1 Γ2 D psl psr :
  @ImpLrule V psr ([fml], D) -> ImpRrule psl (la, fml) ->
  gs2_sr_princ LJAncrules isubfml fml la lc rc Γ1 Γ2 D psl psr.
Proof. intros ir il sub fpl fpr.
inversion ir. inversion il. subst.
inversion H5.  subst. clear ir il H5.
(* first, use IH to cut A -> B from first premise of right premise *)
inversion fpr. subst. clear fpr.
destruct (snd X). clear X.
specialize (d _ _ _ _ eq_refl eq_refl).
(* now cut on A with premise of left premise *)
inversion fpl. subst. clear fpl X1.
pose (sub _ (isub_ImpL _ _) _ d _ (fst X)).
destruct c.  specialize (d0 _ _ _ _ eq_refl eq_refl).
(* now cut on B with second premise of right premise *)
inversion X0. clear X0 X2. subst.
specialize (sub _ (isub_ImpR _ _) _ d0 _ (fst X1)).
destruct sub.  specialize (d1 _ _ _ _ eq_refl eq_refl).
(* now lots of contraction *)
clear d X d0 X1.
lctr_tac lctr_adm_lja d1 lc.  lctr_tac lctr_adm_lja d1 Γ1.
lctr_tac lctr_adm_lja d1 Γ2.  lctr_tac lctr_adm_lja d1 rc.

apply (eq_rect _ _ d1). list_eq_assoc. Qed.

About lja_ImpR_ImpL.

Lemma lja_ImpR_IIL V fml la lc rc Γ1 Γ2 E psl psr :
  ImpL_Imp_rule psr ([fml], E) -> @ImpRrule V psl (la, fml) ->
  gs2_sr_princ LJAncrules dnsubfml fml la lc rc Γ1 Γ2 E psl psr.
Proof. intros ir il sub fpl fpr.
inversion ir. inversion il. subst. 
inversion H5. clear il ir H5. subst.
(* first, get premises derivable *)
inversion fpl.  inversion fpr. inversion X2. subst. clear X0 X2 X4 fpl fpr.
apply fst in X.  apply fst in X1. apply fst in X3.
(* apply Prop 5.3 to left premise (paper uses cut on Imp C D) *)
epose (ImpL_inv_adm_lja X).  unfold l53prop in l.
specialize (l _ _ eq_refl _ _ _ eq_refl).
(* apply ImpR *)
epose (derI' _ (dersrec_singleI l)).
require d.  apply (@fextI _ _ _ Γ1 Γ2).
eapply (rmI_eqp _ _ [([D], B)]).
apply ImpR_anc'. reflexivity. clear l.
(* now cut on Imp D B *)
pose (sub _ (dnsub_Imp_ImpL _ _ _) _ d _ X1).
destruct c.  clear d X1.
specialize (d0 _ lc (C :: rc) D eq_refl eq_refl).
(* apply ImpR *)
epose (derI' _ (dersrec_singleI d0)).
require d.  apply (@fextI _ _ _ (lc ++ fmlsext Γ1 Γ2 []) rc).
eapply (rmI_eqp _ _ [([C], D)]).
apply ImpR_anc'. simpl. unfold fmlsext. list_eq_assoc. clear d0.
(* now cut on Imp C D *)
pose (sub _ (dnsub_ImpL _ _) _ d _ X).
destruct c. clear d X.
specialize (d0 _ Γ1 Γ2 B eq_refl eq_refl).
(* now cut on B *)
specialize (sub _ (dnsub_ImpR _ _) _ d0 _ X3).
destruct sub. clear d0 X3.
specialize (d _ lc rc E eq_refl eq_refl).
(* now necessary contraction *)
unfold fmlsext in d. simpl in d. simpl.
lctr_tac lctr_adm_lja d lc.  lctr_tac lctr_adm_lja d Γ1.
lctr_tac lctr_adm_lja d Γ2.  lctr_tac lctr_adm_lja d rc.
apply (eq_rect _ _ d). list_eq_assoc. Qed.

Lemma lja_ImpR_Ail V fml la lc rc Γ1 Γ2 D G psl psr :
  rlsmap (flip pair G) LJAilrules psr ([fml], D) -> @ImpRrule V psl (la, fml) ->
  gs2_sr_princ LJAncrules dnsubfml fml la lc rc Γ1 Γ2 D psl psr.
Proof. intros ir il sub fpl fpr.
inversion ir. inversion il. subst. clear il ir.
inversion H1 ; inversion H ; subst ; clear H H1.
- (* ImpL_And_rule on right *)
(* first, get premises derivable *)
inversion fpl.  inversion fpr. subst.
apply fst in X.  apply fst in X1.  clear X0 X2 fpl fpr.
(* apply inversion of AndL *)
apply LJA_can_rel_AndLinv in X.
unfold can_rel in X.  unfold fmlsext in X.
erequire X.  require X. 
apply srs_ext_relI.  apply AndLinv_I.
(* apply ImpR twice *)
epose (derI' _ (dersrec_singleI X)).
require d.  apply (@fextI _ _ _ (Γ1 ++ [C]) Γ2).
eapply (rmI_eqp _ _ [([D0], B)]).
apply ImpR_anc'. simpl.  unfold fmlsext. list_eq_assoc. clear X.
epose (derI' _ (dersrec_singleI d)).
require d0.  apply (@fextI _ _ _ Γ1 Γ2).
eapply (rmI_eqp _ _ [([C], Imp D0 B)]).
apply ImpR_anc'. simpl.  unfold fmlsext. list_eq_assoc. clear d.
(* now apply cut by induction on the formula *)
specialize (sub _ (dnsub_Imp_AndL _ _ _) _ d0 _ X1). clear d0 X1.
destruct sub.  exact (d (Γ1 ++ [] ++ Γ2) lc rc D eq_refl eq_refl).

- (* ImpL_Or_rule on right *)
(* first, get premises derivable *)
inversion fpl.  inversion fpr. subst.
apply fst in X.  apply fst in X1.  clear X0 X2 fpl fpr.
(* apply inversion of OrL *)
pose (LJA_can_rel_OrLinv1 X).
pose (LJA_can_rel_OrLinv2 X).
unfold can_rel in c.  unfold fmlsext in c.
erequire c.  require c. 
apply srs_ext_relI.  apply OrLinv1_I.
unfold can_rel in c0.  unfold fmlsext in c0.
erequire c0.  require c0. 
apply srs_ext_relI.  apply OrLinv2_I. clear X.
(* apply ImpR to each *)
epose (derI' _ (dersrec_singleI c)).
require d.  apply (@fextI _ _ _ Γ1 Γ2).
eapply (rmI_eqp _ _ [([C], B)]).
apply ImpR_anc'.  unfold fmlsext. list_eq_assoc. clear c.
epose (derI' _ (dersrec_singleI c0)).
require d0.  apply (@fextI _ _ _ Γ1 Γ2).
eapply (rmI_eqp _ _ [([D0], B)]).
apply ImpR_anc'.  unfold fmlsext. list_eq_assoc. clear c0.
(* now apply cut by induction on the formula, twice *)
pose (sub _ (dnsub_Imp_OrL1 _ _ _) _ d _ X1). 
destruct c.  specialize (d1 _ lc (Imp D0 B :: rc) D eq_refl eq_refl).
specialize (sub _ (dnsub_Imp_OrL2 _ _ _) _ d0 _ d1). 
destruct sub.
specialize (d2 _ (lc ++ fmlsext Γ1 Γ2 []) rc D eq_refl).
require d2. list_eq_assoc. clear d d0 d1 X1.
(* now require contraction *)
eapply lctr_adm_lja in d2.
unfold can_rel in d2. apply d2.
apply (srs_ext_relI_eqp _ 
  (fmlsext Γ1 Γ2 [] ++ fmlsext Γ1 Γ2 []) (fmlsext Γ1 Γ2 []) lc rc).
eapply eq_rect.  apply (lsctr_relI (fmlsext Γ1 Γ2 []) []).
apply app_nil_r.  list_eq_assoc.
Qed.
  
(* lemma for right principal cases, lc and rc are left and right context
  of the right premise of the cut and the last rule on the right *)
Lemma lja_gs2_rp V fml la lc rc G1 G2 (D : PropF V) psl psr 
  (ljl : LJAncrules psl (la, fml))
  (ljr : LJAncrules psr ([fml], D))
  (dl : derrec (fst_ext_rls LJAncrules) emptyT (G1 ++ la ++ G2, fml))
  (dr : derrec (fst_ext_rls LJAncrules) emptyT (lc ++ fml :: rc, D)) :
  gs2_sr_princ LJAncrules dnsubfml fml la lc rc G1 G2 D psl psr.
Proof. inversion ljr ; subst. 
- (* left A rules on the right *)
inversion ljl ; subst.
+ (* left A rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpL_Imp on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL.
eapply fextI. apply (rmI_eqc _ _ _ _ H). reflexivity.
+ (* ImpL_p on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_pL.
eapply fextI. apply (rmI_eqc _ _ _ _ H). reflexivity.
+ (* ImpR on the left *)
eapply lja_ImpR_Ail ; eassumption.
+ (* Id on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* left rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* right rules on the left - formulae different *)
clear dl dr ljl ljr.
inversion X. inversion X0. subst. clear X0 X.
destruct (gen_AilR_rrlsL H1 H5).
- (* ImpL_Imp on the right *)
inversion ljl ; subst.
+ (* left A rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
+ (* ImpL_Imp on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL.
eapply fextI. apply (rmI_eqc _ _ _ _ H0). reflexivity.
+ (* ImpL_p on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_pL.
eapply fextI. apply (rmI_eqc _ _ _ _ H0). reflexivity.
+ (* ImpR on the left *)
apply lja_ImpR_IIL ; assumption.
+ (* Id on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
+ (* left rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
+ (* right rules on the left - formulae different *)
clear dl dr ljl ljr.
inversion X. inversion H. subst. clear H X.
inversion H2 ; inversion H.
- (* ImpL_p on the right *)
inversion ljl ; subst. 
+ (* left A rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
+ (* ImpL_Imp on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL.
eapply fextI. apply (rmI_eqc _ _ _ _ H0). reflexivity.
+ (* ImpL_p on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_pL.
eapply fextI. apply (rmI_eqc _ _ _ _ H0). reflexivity.
+ (* ImpR on the left *)
apply (gs2_sr_princ_sub_mono (@isub_dnsub _)).
eapply lja_ImpR_ImpL.  apply (ImpLrule_p_rsub H).  eassumption.
+ (* Id on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
+ (* left rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
+ (* right rules on the left - formulae different *)
clear dl dr ljl ljr.
inversion X. inversion H. subst. clear H X.
inversion H2 ; inversion H.
- (* ImpR on the right *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpRR_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ H). reflexivity.
- (* Id on the right *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idR_gen.
apply rsubI. intros ps c idp.  eapply (Id_anc idp).
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
- (* left rules on the right *)
inversion ljl ; subst.
+ (* left A rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpL_Imp on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL.
eapply fextI. apply (rmI_eqc _ _ _ _ H). reflexivity.
+ (* ImpL_p on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_pL.
eapply fextI. apply (rmI_eqc _ _ _ _ H). reflexivity.
+ (* ImpR on the left *)
clear dl dr ljl ljr.
inversion X. inversion H. subst. clear X H.
inversion X0.  inversion H.  inversion H.  inversion X.
+ (* Id on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* left rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* right rules on the left *)
inversion X0.  inversion X. subst.
apply (gs2_sr_princ_sub_mono (@isub_dnsub _)).
eapply lja_lrlsR_rrlsLe ; try eassumption.
- (* right rules on the right *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_rrlsR_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
Qed.

About lja_gs2_rp.

