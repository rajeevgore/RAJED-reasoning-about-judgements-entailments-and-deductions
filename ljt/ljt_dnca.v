
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

Definition lja_ImpR_ImpL V fml la lc rc Γ1 Γ2 D psl psr :=
  @ljg_ImpR_ImpL V LJAncrules fml la lc rc Γ1 Γ2 D psl psr (@lctr_adm_lja V).

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
inversion X ; inversion X0 ; subst ; clear X X0.
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
Lemma lja_gs2_rp {V} fml la lc rc G1 G2 (D : PropF V) psl psr 
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
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpL_p on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_pL.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
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
destruct (gen_AilR_rrlsL X1 X2).
- (* ImpL_Imp on the right *)
inversion ljl ; subst.
+ (* left A rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpL_Imp on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpL_p on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_pL.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpR on the left *)
apply lja_ImpR_IIL ; assumption.
+ (* Id on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* left rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* right rules on the left - formulae different *)
clear dl dr ljl ljr.
inversion X. inversion X0. subst. clear X0 X.
inversion X1 ; inversion X.
- (* ImpL_p on the right *)
inversion ljl ; subst. 
+ (* left A rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpL_Imp on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpL_p on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_pL.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpR on the left *)
apply (gs2_sr_princ_sub_mono (@isub_dnsub _)).
eapply lja_ImpR_ImpL.  apply (ImpLrule_p_rsub X).  eassumption.
+ (* Id on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* left rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* right rules on the left - formulae different *)
clear dl dr ljl ljr.
inversion X. inversion X0. subst. clear X0 X.
inversion X1 ; inversion X.
- (* ImpR on the right *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpRR_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
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
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpL_p on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_pL.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpR on the left *)
clear dl dr ljl ljr.
inversion X. inversion X0. subst. clear X X0.
inversion X1 ; inversion X.
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

Lemma ljg_gs2 U rules subf fml psl psr cl cr
  (r_seL : forall ps cl cr, rules ps (cl, cr) -> sing_empty cl)
  (ljg_gs2_rp : forall fml la lc rc G1 G2 D psl psr,
    rules psl (la, fml) -> rules psr ([fml : U], D) ->
     derrec (fst_ext_rls rules) emptyT (G1 ++ la ++ G2, fml) ->
     derrec (fst_ext_rls rules) emptyT (lc ++ fml :: rc, D) ->
     gs2_sr_princ rules subf fml la lc rc G1 G2 D psl psr) :
  (fst_ext_rls rules) psl cl -> (fst_ext_rls rules) psr cr ->
  gen_step2 (cedc (fst_ext_rls rules)) fml subf
    (derrec (fst_ext_rls rules) emptyT)
    (derrec (fst_ext_rls rules) emptyT) psl cl psr cr.
Proof. intros ljl ljr.  destruct ljl.  destruct ljr.
intros sub fpl fpr dl dr. apply cedcI. intros * cle cre.
destruct r0. destruct c0 as [cra crs].
inversion cre. unfold fmlsext in H0. subst. clear cre.
acacD'T2 ; subst.
- clear sub fpl ; 
eapply derI ; [ eapply (fextI_eqc' _ ra (la ++ ra') _ _ r0) ; sfea | ] ;
apply dersrecI_forall ;  intros c incm ;
apply InT_mapE in incm ; cD ;
inversion incm0 ; clear incm0 ; subst ;
unfold fmlsext ; simpl ;
destruct (ForallTD_forall fpr (InT_map _ incm1)) ;
clear d ; destruct c ;
specialize (d _ (ra ++ incm) ra' c0 eq_refl) ;
require d ; [ sfea | apply (eq_rect _ _ d) ; list_eq_assoc ].

- pose (r_seL _ _ _ r0). inversion s. subst. simpl.
simpl in *. unfold fmlsext in fpl. unfold fmlsext in dr.
rewrite app_nil_r in fpl.  rewrite app_nil_r in fpr. rewrite app_nil_r in dr.
inversion r.  destruct c.  inversion H1. subst. clear H1 r.
apply (ljg_gs2_rp _ _ _ _ _ _ _ _ _ X r0 dl dr sub fpl fpr).

- clear sub fpl. 
eapply derI.  eapply (fextI_eqc' _ (ra ++ la ++ H2) Γ3 _ _ r0). sfea.
apply dersrecI_forall.  intros c incm.
apply InT_mapE in incm. cD.
inversion incm0. clear incm0. subst.
unfold fmlsext. simpl.
eapply ForallTD_forall in fpr.  2: apply (InT_map _ incm1).
destruct fpr. clear d. destruct c.
specialize (d _ ra (H2 ++ incm ++ Γ3) c0 eq_refl).
require d.  sfea.  apply (eq_rect _ _ d). list_eq_assoc.

- clear sub fpl. 
eapply derI.  eapply (fextI_eqc' _ Γ0 (la ++ ra') _ _ r0).  sfea.
apply dersrecI_forall.  intros c incm.
apply InT_mapE in incm. cD.
inversion incm0. clear incm0. subst.
unfold fmlsext. simpl.
eapply ForallTD_forall in fpr.  2: apply (InT_map _ incm1).
destruct fpr. clear d. destruct c.
specialize (d _ (Γ0 ++ incm) ra' c0 eq_refl).
require d.  sfea.  apply (eq_rect _ _ d). list_eq_assoc.

- pose (r_seL _ _ _ r0). inversion s. list_eq_ncT. inversion H1.
list_eq_ncT. sD ; inversion H2. subst.
simpl in *. unfold fmlsext in *.  rewrite app_nil_r.
inversion r.  destruct c.  inversion H1. subst. clear H1 r.
apply (ljg_gs2_rp _ _ _ _ _ _ _ _ _ X r0 dl dr sub fpl fpr).

- clear sub fpl. 
eapply derI.  eapply (fextI_eqc' _ Γ0 (H2 ++ la ++ ra') _ _ r0).  sfea.
apply dersrecI_forall.  intros c incm.
apply InT_mapE in incm. cD.
inversion incm0. clear incm0. subst.
unfold fmlsext. simpl.
eapply ForallTD_forall in fpr.  2: apply (InT_map _ incm1).
destruct fpr. clear d. destruct c.
specialize (d _ (Γ0 ++ incm ++ H2) ra' c0 eq_refl).
require d.  sfea.  apply (eq_rect _ _ d). list_eq_assoc.
Qed.

Definition lja_gs2 V fml psl psr cl cr :=
  @ljg_gs2 _ LJAncrules dnsubfml fml psl psr cl cr (@LJAnc_seL V) lja_gs2_rp.

Theorem lja_cut_adm V fml cl cr: derrec (@LJArules V) emptyT cl ->  
  derrec LJArules emptyT cr -> cedc LJArules fml cl cr.
Proof. intros dl dr.
eapply (@gen_step2_lemT _ _ _ (cedc (@LJArules V)) fml dnsubfml).
apply AccT_dnsubfml.
intros * ra rb.  apply (lja_gs2 ra rb).
exact dl. exact dr.
Qed.

Check lja_cut_adm.
Print Assumptions lja_cut_adm.

