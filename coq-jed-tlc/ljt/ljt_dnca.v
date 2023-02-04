
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

Definition ljt_lrlsR_rrlsL V fml la lc rc G1 G2 D psl psr :=
  @gen_lrlsR_rrlsL V LJTncrules fml la lc rc G1 G2 D psl psr (@lctr_adm_ljt V).
Definition ljt_lrlsR_rrlsLe V fml lc rc G1 G2 D psl psr :=
  @gen_lrlsR_rrlsL V LJTncrules fml [] lc rc G1 G2 D psl psr (@lctr_adm_ljt V).

Definition ljt_ImpR_ImpL V fml la lc rc Γ1 Γ2 D psl psr :=
  @ljg_ImpR_ImpL V LJTncrules fml la lc rc Γ1 Γ2 D psl psr (@lctr_adm_ljt V).

Definition lja_lrlsR_rrlsL V fml la lc rc G1 G2 D psl psr :=
  @gen_lrlsR_rrlsL V LJAncrules fml la lc rc G1 G2 D psl psr (@lctr_adm_lja V).
Definition lja_lrlsR_rrlsLe V fml lc rc G1 G2 D psl psr :=
  @gen_lrlsR_rrlsL V LJAncrules fml [] lc rc G1 G2 D psl psr (@lctr_adm_lja V).

Definition lja_ImpR_ImpL V fml la lc rc Γ1 Γ2 D psl psr :=
  @ljg_ImpR_ImpL V LJAncrules fml la lc rc Γ1 Γ2 D psl psr (@lctr_adm_lja V).

About lja_ImpR_ImpL.

Lemma ljg_ImpR_IIL V rules fml la lc rc Γ1 Γ2 E psl psr
  (lctr_adm_ljg : forall fmls seq, derrec (fst_ext_rls rules) emptyT seq ->
     can_rel (fst_ext_rls rules)
         (fun fmls' => srs_ext_rel (lsctr_rel fmls')) fmls seq)
  (ImpL_inv_adm_ljg : forall (D : PropF V) seq,
       derrec (fst_ext_rls rules) emptyT seq -> l53propg rules D seq)
  (ImpR_gnc' : forall A B, rules [([A], B)] ([], Imp A B)) :
  ImpL_Imp_rule psr ([fml], E) -> @ImpRrule V psl (la, fml) ->
  gs2_sr_princ rules dnsubfml fml la lc rc Γ1 Γ2 E psl psr.
Proof. intros ir il sub fpl fpr.
inversion ir. inversion il. subst. 
inversion H5. clear il ir H5. subst.
(* first, get premises derivable *)
inversion fpl.  inversion fpr. inversion X2. subst. clear X0 X2 X4 fpl fpr.
apply fst in X.  apply fst in X1. apply fst in X3.
(* apply Prop 5.3 to left premise (paper uses cut on Imp C D) *)
epose (ImpL_inv_adm_ljg _ _ X).  unfold l53propg in l.
specialize (l _ _ eq_refl _ _ _ eq_refl).
(* apply ImpR *)
epose (derI' _ (dersrec_singleI l)).
require d.  apply (@fextI _ _ _ Γ1 Γ2).
eapply (rmI_eqp _ _ [([D], B)]).
apply ImpR_gnc'. reflexivity. clear l.
(* now cut on Imp D B *)
pose (sub _ (dnsub_Imp_ImpL _ _ _) _ d _ X1).
destruct c.  clear d X1.
specialize (d0 _ lc (C :: rc) D eq_refl eq_refl).
(* apply ImpR *)
epose (derI' _ (dersrec_singleI d0)).
require d.  apply (@fextI _ _ _ (lc ++ fmlsext Γ1 Γ2 []) rc).
eapply (rmI_eqp _ _ [([C], D)]).
apply ImpR_gnc'. simpl. unfold fmlsext. list_eq_assoc. clear d0.
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
lctr_tac lctr_adm_ljg d lc.  lctr_tac lctr_adm_ljg d Γ1.
lctr_tac lctr_adm_ljg d Γ2.  lctr_tac lctr_adm_ljg d rc.
apply (eq_rect _ _ d). list_eq_assoc. Qed.

Definition lja_ImpR_IIL V fml la lc rc Γ1 Γ2 E psl psr :=
 @ljg_ImpR_IIL V LJAncrules fml la lc rc Γ1 Γ2 E psl psr
 (@lctr_adm_lja V) (@ImpL_inv_adm_lja V) ImpR_anc'.
 
Definition ljt_ImpR_IIL V fml la lc rc Γ1 Γ2 E psl psr :=
 @ljg_ImpR_IIL V LJTncrules fml la lc rc Γ1 Γ2 E psl psr
 (@lctr_adm_ljt V) (@ImpL_inv_adm_ljt V) ImpR_tnc'.
 
Lemma ljg_ImpR_Ail V rules fml la lc rc Γ1 Γ2 D G psl psr 
  (lctr_adm_ljg : forall fmls seq, derrec (fst_ext_rls rules) emptyT seq ->
     can_rel (fst_ext_rls rules)
         (fun fmls' => srs_ext_rel (lsctr_rel fmls')) fmls seq)
  (ImpR_gnc' : forall A B, rules [([A], B)] ([], @Imp V A B)) 
  (LJX_can_rel_AndLinv : forall seq, derrec (fst_ext_rls rules) emptyT seq ->
       can_rel (fst_ext_rls rules) (@srs_ext_rel _ _) AndLinv seq)
  (LJX_can_rel_OrLinv1 : forall seq, derrec (fst_ext_rls rules) emptyT seq ->
       can_rel (fst_ext_rls rules) (@srs_ext_rel _ _) OrLinv1 seq)
  (LJX_can_rel_OrLinv2 : forall seq, derrec (fst_ext_rls rules) emptyT seq ->
       can_rel (fst_ext_rls rules) (@srs_ext_rel _ _) OrLinv2 seq) :
  rlsmap (flip pair G) LJAilrules psr ([fml], D) -> @ImpRrule V psl (la, fml) ->
  gs2_sr_princ rules dnsubfml fml la lc rc Γ1 Γ2 D psl psr.
Proof. intros ir il sub fpl fpr.
inversion ir. inversion il. subst. clear il ir.
inversion X ; inversion X0 ; subst ; clear X X0.
- (* ImpL_And_rule on right *)
(* first, get premises derivable *)
inversion fpl.  inversion fpr. subst.
apply fst in X.  apply fst in X1.  clear X0 X2 fpl fpr.
(* apply inversion of AndL *)
apply LJX_can_rel_AndLinv in X.
unfold can_rel in X.  unfold fmlsext in X.
erequire X.  require X. 
apply srs_ext_relI.  apply AndLinv_I.
(* apply ImpR twice *)
epose (derI' _ (dersrec_singleI X)).
require d.  apply (@fextI _ _ _ (Γ1 ++ [C]) Γ2).
eapply (rmI_eqp _ _ [([D0], B)]).
apply ImpR_gnc'. simpl.  unfold fmlsext. list_eq_assoc. clear X.
epose (derI' _ (dersrec_singleI d)).
require d0.  apply (@fextI _ _ _ Γ1 Γ2).
eapply (rmI_eqp _ _ [([C], Imp D0 B)]).
apply ImpR_gnc'. simpl.  unfold fmlsext. list_eq_assoc. clear d.
(* now apply cut by induction on the formula *)
specialize (sub _ (dnsub_Imp_AndL _ _ _) _ d0 _ X1). clear d0 X1.
destruct sub.  exact (d (Γ1 ++ [] ++ Γ2) lc rc D eq_refl eq_refl).

- (* ImpL_Or_rule on right *)
(* first, get premises derivable *)
inversion fpl.  inversion fpr. subst.
apply fst in X.  apply fst in X1.  clear X0 X2 fpl fpr.
(* apply inversion of OrL *)
pose (LJX_can_rel_OrLinv1 _ X).
pose (LJX_can_rel_OrLinv2 _ X).
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
apply ImpR_gnc'.  unfold fmlsext. list_eq_assoc. clear c.
epose (derI' _ (dersrec_singleI c0)).
require d0.  apply (@fextI _ _ _ Γ1 Γ2).
eapply (rmI_eqp _ _ [([D0], B)]).
apply ImpR_gnc'.  unfold fmlsext. list_eq_assoc. clear c0.
(* now apply cut by induction on the formula, twice *)
pose (sub _ (dnsub_Imp_OrL1 _ _ _) _ d _ X1). 
destruct c.  specialize (d1 _ lc (Imp D0 B :: rc) D eq_refl eq_refl).
specialize (sub _ (dnsub_Imp_OrL2 _ _ _) _ d0 _ d1). 
destruct sub.
specialize (d2 _ (lc ++ fmlsext Γ1 Γ2 []) rc D eq_refl).
require d2. list_eq_assoc. clear d d0 d1 X1.
(* now require contraction *)
eapply lctr_adm_ljg in d2.
unfold can_rel in d2. apply d2.
apply (srs_ext_relI_eqp _ 
  (fmlsext Γ1 Γ2 [] ++ fmlsext Γ1 Γ2 []) (fmlsext Γ1 Γ2 []) lc rc).
eapply eq_rect.  apply (lsctr_relI (fmlsext Γ1 Γ2 []) []).
apply app_nil_r.  list_eq_assoc.
Qed.
  
Definition ljt_ImpR_Ail V fml la lc rc Γ1 Γ2 D G psl psr :=
  @ljg_ImpR_Ail V LJTncrules fml la lc rc Γ1 Γ2 D G psl psr (@lctr_adm_ljt V)
  ImpR_tnc' LJT_can_rel_AndLinv LJT_can_rel_OrLinv1 LJT_can_rel_OrLinv2.

Definition lja_ImpR_Ail V fml la lc rc Γ1 Γ2 D G psl psr :=
  @ljg_ImpR_Ail V LJAncrules fml la lc rc Γ1 Γ2 D G psl psr (@lctr_adm_lja V)
  ImpR_anc' LJA_can_rel_AndLinv LJA_can_rel_OrLinv1 LJA_can_rel_OrLinv2.

Definition gs2_idR_lja V A fml any drsb psl psr cl cr :=
  @gs2_idR_gen' V _ A fml any drsb psl psr cl cr (@InT_der_LJA V).
Definition gs2_idR_ljt V A fml any drsb psl psr cl cr :=
  @gs2_idR_gen' V _ A fml any drsb psl psr cl cr (@InT_der_LJT V).

(* lemma for right principal cases, lc and rc are left and right context
  of the right premise of the cut and the last rule on the right *)
  (* uses (most in ljt_ca.v)
  Locate gs2_AilL_lja. could we use gs2_lrlsL_gen
  Locate gs2_ImpL_ImpL_lja. could we use gs2_ImpL_ImpL_gen 
  Locate gs2_ImpL_pL. not applicable to ljt
  Locate gs2_idL_lja. could we use gs2_idL_gen
  Locate gs2_lrlsL_lja. could we use gs2_lrlsL_gen
  Locate gs2_ImpRR_lja. could we use gs2_ImpRR_gen
  Locate lja_ImpR_Ail. (* above *)
 Locate gs2_idR_gen. (* this one is general *)
  *)
(* could try proofs like this, to allow commonality between different
  rule systems, but complications, need admissibility of contraction,
  exchange, invertibility of some rules for rule set rules
Lemma lja_gs2_rp' {V} rules fml la lc rc G1 G2 (D : PropF V) psl psr 
  (rs : rsub LJAncrules rules)
  (ljl : LJAncrules psl (la, fml)) (ljr : LJAncrules psr ([fml], D))
  (dl : derrec (fst_ext_rls rules) emptyT (G1 ++ la ++ G2, fml))
  (dr : derrec (fst_ext_rls rules) emptyT (lc ++ fml :: rc, D)) :
  gs2_sr_princ rules dnsubfml fml la lc rc G1 G2 D psl psr.
  *)

Lemma ljt_gs2_rp {V} fml la lc rc G1 G2 (D : PropF V) psl psr 
  (ljl : LJTncrules psl (la, fml))
  (ljr : LJTncrules psr ([fml], D))
  (dl : derrec (fst_ext_rls LJTncrules) emptyT (G1 ++ la ++ G2, fml))
  (dr : derrec (fst_ext_rls LJTncrules) emptyT (lc ++ fml :: rc, D)) :
  gs2_sr_princ LJTncrules dnsubfml fml la lc rc G1 G2 D psl psr.
Proof. inversion ljr ; subst. 
- (* TS rules on the right *)
inversion X ; subst.
-- (* left A rules on the right *)
inversion ljl ; subst.
+ (* TS rules on the left *)
inversion X1 ; subst.
++ (* left A rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* ImpL_Imp on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* ImpR on the left *)
eapply ljt_ImpR_Ail ; eassumption.
++ (* Id on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* left rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* right rules on the left - formulae different *)
clear dl dr ljl ljr.
inversion X0. inversion X2. subst. clear X0 X X1 X2.
destruct (gen_AilR_rrlsL X3 X4).
+ (* ImpL_atom_rule on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_atomL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X1). reflexivity.
+ (* exch_rule on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_exchL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X1). reflexivity.

-- (* ImpL_Imp on the right *)
inversion ljl ; subst.
+ (* TS rules on the left *)
inversion X1 ; subst.
++ (* left A rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* ImpL_Imp on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* ImpR on the left *)
apply ljt_ImpR_IIL ; assumption.
++ (* Id on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* left rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* right rules on the left - formulae different *)
clear dl dr ljl ljr.
inversion X2. inversion X0. subst. clear X0 X2.
inversion X3 ; inversion X0.
 
+ (* ImpL_atom_rule on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_atomL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X1). reflexivity.
+ (* exch_rule on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_exchL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X1). reflexivity.

-- (* ImpR on the right *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpRR_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
-- (* Id on the right *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idR_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.

-- (* left rules on the right *)
inversion ljl ; subst.
+ (* TS rules on the left *)
inversion X1 ; subst.
++ (* left A rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* ImpL_Imp on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* ImpR on the left *)
clear dl dr ljl ljr.
inversion X2. inversion X0. subst. clear X X0 X1 X2.
inversion X3 ; inversion X.
++ (* Id on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* left rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X2). reflexivity.
++ (* right rules on the left *)
inversion X0.  inversion X2. subst.
apply (gs2_sr_princ_sub_mono (@isub_dnsub _)).
eapply ljt_lrlsR_rrlsLe ; try eassumption.
+ (* ImpL_atom_rule on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_atomL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X1). reflexivity.
+ (* exch_rule on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_exchL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X1). reflexivity.

-- (* right rules on the right *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_rrlsR_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.

(* remaining right rules: cannot as rule doesn't act on a singleton *)
- (* ImpL_atom_rule on the right *)
inversion X.  inversion X0. 
- (* exch_rule on the right *)
inversion X.  inversion X0. list_eq_ncT. inversion H5.
Qed.

About ljt_gs2_rp.

(* note that ljt_gs2_rp is incomplete because it requires
  LJTncrules psr ([fml], D)) which excludes atom and exchange rules *)

Lemma gs2_sr_exch V any fml la rll rlr lc rc G1 G2 D psl psr G :
  rlsmap (flip pair G) exch_rule psr (rll ++ fml :: rlr, D : PropF V) ->
  gs2_sr_princ2 LJTncrules any fml la rll rlr lc rc G1 G2 D psl psr.
Proof. intros re sub fpl fpr. clear sub fpl.
inversion re. inversion X. subst. clear X re. 
apply ForallT_singleD in fpr. destruct fpr. clear d. destruct c.
acacD'T2 ; subst. (* 5 subgoals *)
+ do 4 (erequire d).  specialize (d eq_refl).
require d. sfs. assoc_single_mid' y. reflexivity.
apply (exchL_ljt d). apply fst_relI. swap_tac.
list_assoc_l. eapply swapped_nc. 2: reflexivity. list_eq_assoc.
+ do 4 (erequire d).  specialize (d eq_refl).
require d. sfs. assoc_single_mid' fml. reflexivity.
apply (exchL_ljt d). apply fst_relI. swap_tac.  rewrite ?app_nil_r.
list_assoc_l. eapply swapped_nc. reflexivity. list_eq_assoc.
+ do 4 (erequire d).  specialize (d eq_refl).
require d. sfs. assoc_single_mid' fml. reflexivity.
apply (exchL_ljt d). apply fst_relI. swap_tac.  
list_assoc_l. eapply swapped_nc. 2: reflexivity. list_eq_assoc.
+ do 4 (erequire d).  specialize (d eq_refl).
require d. sfs. assoc_single_mid' x. reflexivity.
apply (exchL_ljt d). apply fst_relI. swap_tac.  
list_assoc_l. eapply swapped_nc. reflexivity. list_eq_assoc.
+ do 4 (erequire d).  specialize (d eq_refl).
require d. sfs. assoc_single_mid' fml. reflexivity.
apply (exchL_ljt d). apply fst_relI. swap_tac.  
list_assoc_l. eapply swapped_nc. reflexivity. list_eq_assoc.
Qed.

Lemma ljt_gs2_ImpR_atom V la p B lc rc G1 G2 D psl :
  ImpRrule psl (la, Imp (@Var V p) B) ->
  gs2_sr_princ2 LJTncrules dnsubfml (Imp (Var p) B) la [] [
    Var p] lc rc G1 G2 D psl (map (flip pair D) [[B; Var p]]).
Proof. intros irl sub fpl fpr. 
apply ForallT_singleD in fpr.  destruct fpr.  clear c.
inversion irl. subst. 
apply ForallT_singleD in fpl.  destruct fpl.  clear c.
(* cut admissibility on B between both premises *)
specialize (sub _ (@dnsub_ImpR _ _ _) _ d0 _ d).
inversion sub. clear sub.
do 4 (erequire X).  specialize (X eq_refl).
require X. sfs. assoc_single_mid' B. reflexivity. clear d d0.
(* now need to contract Var p *)
revert X. sfs. intro X.
(* need contraction and exchange *)
eapply ctr_adm_ljt in X.  unfold can_rel in X.
specialize (X (lc ++ (G1 ++ Var p :: G2) ++ rc, D)).
require X.
apply (@srs_ext_relI_eq _ _ _ (Var p :: G2 ++ [Var p]) (Var p :: G2)
  D (lc ++ G1) rc).
apply sctr_relI. list_eq_assoc. list_eq_assoc.
apply (exchL_ljt X).  apply fst_relI. swap_tac_Rc. Qed.

(* where r_seL does not hold, need a stronger result than ljg_gs2_rp *)
Lemma ljt_gs2_rp2 {V} fml la rll rlr lc rc G1 G2 (D : PropF V) psl psr 
  (ljl : LJTncrules psl (la, fml))
  (ljr : LJTncrules psr (rll ++ fml :: rlr, D))
  (dl : derrec (fst_ext_rls LJTncrules) emptyT (G1 ++ la ++ G2, fml))
  (dr : derrec (fst_ext_rls LJTncrules) emptyT 
    (lc ++ (rll ++ fml :: rlr) ++ rc, D)) :
  gs2_sr_princ2 LJTncrules dnsubfml fml la rll rlr lc rc G1 G2 D psl psr.
Proof. inversion ljr ; subst. 
- (* TS rules on the right *)
apply LJTSnc_seL in X.
inversion X ; list_eq_ncT. inversion H0.
sD. inversion H1. subst.
apply gs2_sr_princ_2. apply ljt_gs2_rp ; assumption.
inversion H1.
- (* ImpL_atom_rule on the right *)
inversion X.  inversion X0. clear X X0. subst.
acacD'T2 ; subst. (* 3 subgoals *)
-- (* cut fml is Imp (Var p) B *)
inversion ljl ; subst.
+ (* TS rules on the left *)
inversion X ; subst.
++ (* left A rules on the left *)
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
++ (* ImpL_Imp_rule on the left *)
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
++ (* ImpRrule on the left *)
apply ljt_gs2_ImpR_atom. exact X0.
++ (* Idrule on the left, wrong formula *) inversion X0.
++ (* left rules on the left *)
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
++ (* right rules on the left, wrong formula *)
inversion X0.  inversion X1 ; inversion X2.
+ (* ImpL_atom_rule on the left *)
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_atomL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
+ (* exch_rule on the left *)
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_exchL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.

-- (* cut fml is Var p *)
inversion ljl ; subst.
+ (* TS rules on the left *)
inversion X ; subst.
++ (* left A rules on the left *)
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
++ (* ImpL_Imp_rule on the left *)
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
++ (* ImpRrule on the left, wrong formula *)
inversion X0.
++ (* Idrule on the left *) 
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_idL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
++ (* left rules on the left *)
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_lrlsL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
++ (* right rules on the left, wrong formula *)
inversion X0.  inversion X1 ; inversion X2.
+ (* ImpL_atom_rule on the left *)
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_atomL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
+ (* exch_rule on the left *)
eapply (gs2_rp2 _ _ _ _ _ _ _ _ _ dl dr).  eapply gs2_exchL_ljt.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
-- list_eq_ncT. inversion H3.
- (* exchange rule on the right *)
eapply gs2_sr_exch. exact X.
Qed.

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
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL_lja.
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
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL_lja.
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
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL_lja.
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
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_idR_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X). reflexivity.
- (* left rules on the right *)
inversion ljl ; subst.
+ (* left A rules on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_AilL_lja.
eapply fextI. apply (rmI_eqc _ _ _ _ X0). reflexivity.
+ (* ImpL_Imp on the left *)
eapply (gs2_rp _ _ _ _ _ _ _ dl dr).  eapply gs2_ImpL_ImpL_lja.
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

Lemma ljg_gs2_2 U rules subf fml psl psr cl cr
  (ljg_gs2_rp2 : forall fml la rll rlr lc rc G1 G2 D psl psr,
    rules psl (la, fml) -> rules psr (rll ++ fml :: rlr, D) ->
    derrec (fst_ext_rls rules) emptyT (G1 ++ la ++ G2, fml : U) ->
    derrec (fst_ext_rls rules) emptyT
        (lc ++ (rll ++ fml :: rlr) ++ rc, D) ->
    gs2_sr_princ2 rules subf fml la rll rlr lc rc G1 G2 D psl psr) :
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

- inversion r. destruct c. inversion H1. subst. clear r H1.
rewrite ?app_nil_r in dr.
rewrite ?app_nil_r in fpl.
rewrite ?app_nil_r in fpr.
specialize (ljg_gs2_rp2 fml l [] H3 ra Γ3 Γ1 Γ2 _ _ _ X r0 dl dr sub fpl fpr).
clear sub fpl fpr.
eapply eq_rect. apply ljg_gs2_rp2. sfs. list_eq_assoc.

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

- inversion r. destruct c. inversion H2. subst. clear r H2.
specialize (ljg_gs2_rp2 fml l H0 H4 Γ0 Γ3 Γ1 Γ2 _ _ _ X r0 dl dr sub fpl fpr).
clear sub fpl fpr.
eapply eq_rect. apply ljg_gs2_rp2. sfs. list_eq_assoc.

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

(* what needs changing in the above for the case where r_seL does not hold?
  obviously a correspondingly stronger result than ljg_gs2_rp ;
  the goals at those points is 
      r0 : rules ps0 (fml :: H3, D)
    dl : derrec (fst_ext_rls rules) emptyT (la, fml)
 dr : derrec (fst_ext_rls rules) emptyT
         (apfst (fmlsext (ra ++ []) Γ3) (fml :: H3, D))
  derrec (fst_ext_rls rules) emptyT (ra ++ la ++ H3 ++ Γ3, D)
and
    r0 : rules ps0 (H0 ++ fml :: H4, D)
  dl : derrec (fst_ext_rls rules) emptyT (la, fml)
dr : derrec (fst_ext_rls rules) emptyT
         (apfst (fmlsext Γ0 Γ3) (H0 ++ fml :: H4, D))
  derrec (fst_ext_rls rules) emptyT ((Γ0 ++ H0) ++ la ++ H4 ++ Γ3, D)
*)

Definition lja_gs2 V fml psl psr cl cr :=
  @ljg_gs2 _ LJAncrules dnsubfml fml psl psr cl cr (@LJAnc_seL V) lja_gs2_rp.

Definition ljt_gs2 V fml psl psr cl cr :=
  @ljg_gs2_2 _ (@LJTncrules V) dnsubfml fml psl psr cl cr ljt_gs2_rp2.

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

Theorem ljt_cut_adm V fml cl cr: derrec (@LJTrules V) emptyT cl ->  
  derrec LJTrules emptyT cr -> cedc LJTrules fml cl cr.
Proof. intros dl dr.
eapply (@gen_step2_lemT _ _ _ (cedc (@LJTrules V)) fml dnsubfml).
apply AccT_dnsubfml.
intros * ra rb.  apply (ljt_gs2 ra rb).
exact dl. exact dr.
Qed.

Check ljt_cut_adm.
Print Assumptions ljt_cut_adm.

