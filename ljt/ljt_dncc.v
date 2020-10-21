
(* LJA logic, using lists of formulae - contraction (and maybe cut) *)
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
Require Import ljt ljt_inv ljt_dn ljt_ctr.
Require Import Coq.Program.Basics.

Lemma gen_sctrL_ImpL_And V W rules (B C D : PropF V)
  (Linv : rel_adm rules (srs_ext_rel (@ImpL_And_inv V))):
  (forall G : W,
    rsub (fst_ext_rls (rlsmap (flip pair G) (@ImpL_And_rule V))) rules) ->
  rel_adm rules (srs_ext_rel (sctr_rel (Imp C (Imp D B)))) ->
  rel_adm rules (srs_ext_rel (sctr_rel (Imp (And C D) B))).
Proof. intros rs ctr.  apply rel_admI.
intros * sqrc. apply radmI.
intro derp. destruct sqrc. destruct s.
(* invert one instance of Imp (And C D) B *)
eapply Linv in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ Φ1 (S ++ [Imp _ B] ++ Φ2)).
apply fslr_I. apply (ImpL_And_invs_I B C D).
list_assoc_r. simpl. reflexivity.  reflexivity.
(* invert 2nd instance of Imp (And C D) B *)
eapply Linv in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ (Φ1 ++ [Imp _ _] ++ S) Φ2).
apply fslr_I. apply (ImpL_And_invs_I B C D).
list_assoc_r. simpl. reflexivity.  reflexivity.
revert derp. list_assoc_r. simpl. intro derp.
(* contract premise *)
destruct ctr. erequire r.  erequire r.  require r.
eapply (srs_ext_relI_eq _ _ _ Φ1 Φ2).
apply (sctr_relI _ S).  reflexivity.  reflexivity.
destruct r. revert d. list_assoc_r'. simpl.  intro d.
apply d in derp. clear d.
(* apply rule to contracted premise *)
eapply derI. apply (rsubD (rs G)).
eapply (@fextI _ _ _ Φ1 (S ++ Φ2)).
eapply rmI_eq. apply rmI. apply ImpL_And_rule_I.
reflexivity. simpl.  reflexivity.
simpl. apply dersrec_singleI. apply derp.  Qed.

Print Implicit gen_sctrL_ImpL_And.

Lemma lja_ra_ImpL_And V B C D : 
  rel_adm LJArules (srs_ext_rel (sctr_rel (Imp C (Imp D B)))) ->
  rel_adm LJArules (srs_ext_rel (sctr_rel (@Imp V (And C D) B))).
Proof. intros. apply gen_sctrL_ImpL_And.
apply crd_ra.  apply LJA_can_rel_ImpL_And_inv.
unfold LJArules. intro. apply fer_mono.
intros ps' c' ra.  eapply il_anc.
epose (rsubD (rm_mono (rsubI _ _ And_ail))).  exact (r _ _ ra).
exact X. Qed.

Print Implicit lja_ra_ImpL_And.

(* left contraction of Imp (Or C D) B by induction on the formula *)
Lemma gen_sctrL_ImpL_Or V W rules (B C D : PropF V)
  (Linv : rel_adm rules (srs_ext_rel (@ImpL_Or_inv V))):
  (forall G : W,
    rsub (fst_ext_rls (rlsmap (flip pair G) (@ImpL_Or_rule V))) rules) ->
  rel_adm rules (srs_ext_rel (sctr_rel (Imp C B))) ->
  rel_adm rules (srs_ext_rel (sctr_rel (Imp D B))) ->
  rel_adm rules (srs_ext_rel (sctr_rel (Imp (Or C D) B))).
Proof. intros rs ctra ctrb.  apply rel_admI.
intros * sqrc. apply radmI.
intro derp. destruct sqrc. destruct s.
(* invert one instance of Imp (Or C D) B *)
eapply Linv in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ Φ1 (S ++ [Imp (Or C D) B] ++ Φ2)).
apply fslr_I. apply (ImpL_Or_invs_I B C D).
list_assoc_r. simpl. reflexivity.  reflexivity.
(* invert 2nd instance of Imp (Or C D) B *)
eapply Linv in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ (Φ1 ++ [Imp C B; Imp D B] ++ S) Φ2).
apply fslr_I. apply (ImpL_Or_invs_I B C D).
list_assoc_r. simpl. reflexivity.  reflexivity.
revert derp. list_assoc_r. simpl. intro derp.
(* contract Imp C B *)
destruct ctra. erequire r.  erequire r.  require r.
eapply (srs_ext_relI_eq _ _ _ Φ1 (Imp D B :: Φ2)).
apply (sctr_relI (Imp C B) (Imp D B :: S)).  reflexivity.  reflexivity.
destruct r. revert d. list_assoc_r'. simpl.  intro d.
apply d in derp. clear d.
(* contract Imp D B *)
destruct ctrb.  erequire r.  erequire r.  require r.
eapply (srs_ext_relI_eq _ _ _ (Φ1 ++ [Imp C B]) Φ2).
apply (sctr_relI (Imp D B) S).  
list_assoc_r'. simpl.  reflexivity.
list_assoc_r'. simpl.  reflexivity.
destruct r.  apply d in derp. clear d.
(* apply ImpL_Or_rule rule to contracted premises *)
eapply derI. apply (rsubD (rs G)).
eapply (@fextI _ _ _ Φ1 (S ++ Φ2)).
eapply rmI_eq. apply rmI. apply ImpL_Or_rule_I.
reflexivity. simpl.  reflexivity.
simpl. apply dersrec_singleI. apply derp.  Qed.

Print Implicit gen_sctrL_ImpL_Or.

Lemma lja_ra_ImpL_Or V B C D : 
  rel_adm LJArules (srs_ext_rel (sctr_rel (Imp C B))) ->
  rel_adm LJArules (srs_ext_rel (sctr_rel (Imp D B))) ->
  rel_adm LJArules (srs_ext_rel (sctr_rel (@Imp V (Or C D) B))).
Proof. intros. apply gen_sctrL_ImpL_Or.
apply crd_ra.  apply LJA_can_rel_ImpL_Or_inv.
unfold LJArules. intro. apply fer_mono.
intros ps' c' ra.  eapply il_anc.
epose (rsubD (rm_mono (rsubI _ _ Or_ail))).  exact (r _ _ ra).
exact X. exact X0. Qed.

Print Implicit lja_ra_ImpL_Or.

Lemma lja_ctr_il {V} ps s (l : @LJAilrules V ps [s])
  (sub : forall A', dnsubfml A' s -> forall x, derrec LJArules emptyT x ->
    can_rel LJArules (fun fml' : PropF V => srs_ext_rel (sctr_rel fml')) A' x) :
  rel_adm LJArules (srs_ext_rel (sctr_rel s)).
Proof. inversion l ; subst ; clear l.
+ inversion H. subst. clear H.  apply lja_ra_ImpL_And.
apply crd_ra.  exact (sub _ (dnsub_Imp_AndL _ _ _)).
+ inversion H. subst. clear H.  apply lja_ra_ImpL_Or.
apply crd_ra.  exact (sub _ (dnsub_Imp_OrL1 _ _ _)).
apply crd_ra.  exact (sub _ (dnsub_Imp_OrL2 _ _ _)).
Qed.

Definition gs_lja_ilrules V A Γ1 Γ2 G ps c := @gs_ljg_glrules V
  A _ _ _ Γ1 Γ2 G ps c LJAil_single il_anc' lja_ctr_il.

(* tactic for srs_ext_rel ... X Y where X is given,
  where relation is (eg) contraction on or inversion of A,
  strips off all before and after A in goal *)
Ltac sertacR1 A := ((apply (ser_appR (single A)) ; fail 1) || 
  (apply ser_appR)).
(* for some reason we need eapply using ser_appR *)
Ltac sertacR1e A := ((eapply (ser_appR (single A)) ; fail 1) || 
  (apply ser_appR)).
Ltac sertacL1 A := 
  (apply (ser_appc A) ; fail 1) || (apply ser_appL || apply ser_appc).

Ltac sertac A := rewrite ?(cons_app_single A) ;
  list_assoc_l' ; rewrite ?(cons_app_single _ (single A)) ;
  rewrite ?app_nil_r ; list_assoc_l' ; repeat (sertacR1e A) ;
  rewrite - ?app_assoc ; repeat (sertacL1 A).

(* for contraction on A , X is can_rel ... *)
Ltac sersctrtac X A := 
unfold can_rel in X ; erequire X ; require X ; [ sertac A ;
apply srs_ext_relI_nil ; eapply sctr_relI_eqp ;
list_assoc_r' ; apply f_equal ; list_assoc_l' ; reflexivity | ].

Ltac appii fml X sub := 
assoc_single_mid' fml ;
eapply derI ; [ eapply fextI ; eapply rmI_eqc ; [ apply Imp_anc' |
simpl ; unfold fmlsext ; reflexivity ] |
apply dlCons ; [
apply (eq_rect _ _ X) ; simpl ; unfold fmlsext ; list_eq_assoc |
apply dersrec_singleI ;
apply (eq_rect _ _ sub) ; simpl ; unfold fmlsext ; list_eq_assoc ]].

Ltac appii2 A B X1 sub := 
apply LJA_can_rel_ImpL_Imp_inv2 in X1 ;
unfold can_rel in X1 ;  erequire X1 ;  require X1 ; [
sertac A ;
apply srs_ext_relI_nil ; apply fslr_I ;  apply ImpL_Imp_inv2s_I | 
(* now contract B in X1 *)
specialize (sub _ (tT_step _ _ _ (dnsub_ImpR _ _)) _ X1) ;
sersctrtac sub B ;
(* now apply ImpL_Imp_rule *)
simpl in sub ; clear X1 ].

Ltac app42i fp X A := 
simpl in fp ; unfold fmlsext in fp ; simpl in fp ; 
inversion fp ; apply fst in X ; subst ; clear fp ;
(* apply Lemma 4.2 to X *)
apply can_rel_dn42inv in X ;
unfold can_rel in X ;  erequire X ;  require X ; [
assoc_single_mid' A ;
eapply srs_ext_relI_c1 ;  apply dn42inv_I | ].

Lemma tc_dns_ii V B C D : clos_transT dnsubfml C (@Imp V (Imp C D) B).
Proof. eapply tT_trans ; apply tT_step ; apply dnsub_ImpL. Qed.


(* difficult case of contraction for Lemma 5.1, as top of pg 1505 *)

Lemma gs_lja_ImpL_Imp V A Γ1 Γ2 ps c : ImpL_Imp_rule ps c ->
  gen_step (can_rel (fst_ext_rls LJAncrules)
      (fun fml' : PropF V => srs_ext_rel (sctr_rel fml'))) A 
    (clos_transT dnsubfml) (derrec (fst_ext_rls LJAncrules) emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof.  intro r. destruct r.  unfold gen_step.
intros sub fp dc seq' sc.
inversion sc. destruct X. clear sc. subst.
unfold fmlsext in H0.  simpl in H0.
acacD'T2 ; subst ; repeat (list_eq_ncT ; cD ; subst). (* 7 subgoals *)

- (* principal formula is occurrence of contracted formula *)
app42i fp X (Imp (Imp C D) B).

(* now contract Imp D B, twice *)
pose (sub _ (tT_step _ _ _ (dnsub_Imp_ImpL _ _ _))).
apply c in X. sersctrtac X (Imp D B).
apply c in X. sersctrtac X (Imp D B).

(* now contract C *) clear c ;  pose (sub C (tc_dns_ii _ _ _) _ X) ; 
sersctrtac c C ; simpl in c ; clear X.

inversion X0. subst. clear X0 X1. apply fst in X.
(* apply inversion to Imp (Imp C D) B in X to get B *)
appii2 (Imp (Imp C D) B) B X sub.
appii (Imp (Imp C D) B) c sub.

- clear sub. eapply derI. eapply fextI_eqc'. apply Imp_anc'.
simpl. unfold fmlsext. simpl.
list_assoc_r'. reflexivity.
eapply usefm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr). clear fpdcr.
destruct p. simpl. unfold fmlsext. simpl.
apser'.  apply (sctr_relI A S).

- (* principal formula is occurrence of contracted formula *)
app42i fp X (Imp (Imp C D) B).
(* now contract Imp D B, twice *)
pose (sub _ (tT_step _ _ _ (dnsub_Imp_ImpL _ _ _))).
apply c in X. sersctrtac X (Imp D B).
apply c in X. sersctrtac X (Imp D B).
(* now contract C *) clear c ;  pose (sub C (tc_dns_ii _ _ _) _ X) ; 
sersctrtac c C ; simpl in c ; clear X.
inversion X0. subst. clear X0 X1. apply fst in X.
(* apply inversion to Imp (Imp C D) B in X to get B *)
appii2 (Imp (Imp C D) B) B X sub.
appii (Imp (Imp C D) B) c sub.

- acacD'T2 ; subst. (* why is this necessary? *)
+ (* principal formula is occurrence of contracted formula *)

app42i fp X (Imp (Imp C D) B).
(* now contract Imp D B, twice *)
pose (sub _ (tT_step _ _ _ (dnsub_Imp_ImpL _ _ _))).
apply c in X. sersctrtac X (Imp D B).
apply c in X. sersctrtac X (Imp D B).
(* now contract C *) clear c ;  pose (sub C (tc_dns_ii _ _ _) _ X) ; 
sersctrtac c C ; simpl in c ; clear X.
inversion X0. subst. clear X0 X1. apply fst in X.
(* apply inversion to Imp (Imp C D) B in X to get B *)
appii2 (Imp (Imp C D) B) B X sub.
appii (Imp (Imp C D) B) c sub.

+ (* principal formula between occurrences of contracted formula *)
clear sub. eapply derI. eapply fextI_eqc'. apply Imp_anc'.
simpl. unfold fmlsext. simpl.
assoc_single_mid' (Imp (Imp C D) B). reflexivity.
eapply usefm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr). clear fpdcr.
destruct p. simpl. unfold fmlsext. simpl.
apser'.  eapply arg1_cong_imp.
2: apply sctr_relI.  list_eq_assoc.

- clear sub. eapply derI. eapply fextI_eqc'. apply Imp_anc'.
simpl. unfold fmlsext. simpl.
list_assoc_l'. reflexivity.
eapply usefm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr). clear fpdcr.
destruct p. simpl. unfold fmlsext. simpl.
apser'.  apply (sctr_relI A S).

- (* principal formula is occurrence of contracted formula *)
app42i fp X (Imp (Imp C D) B).
(* now contract Imp D B, twice *)
pose (sub _ (tT_step _ _ _ (dnsub_Imp_ImpL _ _ _))).
apply c in X. sersctrtac X (Imp D B).
apply c in X. sersctrtac X (Imp D B).
(* now contract C *) clear c ;  pose (sub C (tc_dns_ii _ _ _) _ X) ; 
sersctrtac c C ; simpl in c ; clear X.
inversion X0. subst. clear X0 X1. apply fst in X.
(* apply inversion to Imp (Imp C D) B in X to get B *)
appii2 (Imp (Imp C D) B) B X sub.
appii (Imp (Imp C D) B) c sub.

- clear sub. eapply derI. eapply fextI_eqc'. apply Imp_anc'.
simpl. unfold fmlsext. simpl.
list_assoc_l'. reflexivity.
eapply usefm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr). clear fpdcr.
destruct p. simpl. unfold fmlsext. simpl.
apser'.  apply (sctr_relI A S).

Qed.

Check gs_lja_ImpL_Imp.

(*
Lemma ctr_adm_lja V (fml : PropF V) :
  forall seq, derrec LJArules emptyT seq ->
  can_rel LJArules (fun fml' => srs_ext_rel (sctr_rel fml')) fml seq.
Proof. eapply gen_step_lemT. apply AccT_dnsubfml.
intros * ljpc. destruct ljpc.
destruct r. destruct l.
- (* LJAilrules *)
exact (gs_lja_ilrules _ _ r).
- (* ImpL_Imp_rule *)
exact (gs_lja_ImpL_Imp _ _ i).
- (* ImpLrule *)
exact (gs_lja_ImpL _ _ i).
- (* ImpRrule *)
exact (gs_lja_ImpR _ _ _ i).
- (* Idrule *)
eapply gs_sctr_Id. 2: exact i. apply rsubI. apply Id_anc.
- (* left rules *)
exact (gs_lja_lrules _ _ r).
- (* right rules *)
exact (gs_lja_rrules _ _ _ r).

Qed.

*)

