
(* LJA logic, using lists of formulae - contraction *)
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
Require Import ljt ljt_inv ljt_dn ljt_ctr ljt_ca.
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
eapply crd_ra2I in ctra. 2: exact derp.
sersctrtac ctra (Imp C B). clear derp.
(* contract Imp D B *)
eapply crd_ra2I in ctrb. 2: exact ctra.
sersctrtac ctrb (Imp D B). clear ctra.
(* apply ImpL_Or_rule rule to contracted premise *)
eapply derI. apply (rsubD (rs G)).
eapply (@fextI _ _ _ Φ1 (S ++ Φ2)).
eapply rmI_eq. apply rmI. apply ImpL_Or_rule_I.
reflexivity. simpl.  reflexivity.
simpl. apply dersrec_singleI. 
unfold fmlsext. apply (eq_rect _ _ ctrb). list_eq_assoc.  Qed.

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
+ inversion X. subst. clear X.  apply lja_ra_ImpL_And.
apply crd_ra.  exact (sub _ (dnsub_Imp_AndL _ _ _)).
+ inversion X. subst. clear X.  apply lja_ra_ImpL_Or.
apply crd_ra.  exact (sub _ (dnsub_Imp_OrL1 _ _ _)).
apply crd_ra.  exact (sub _ (dnsub_Imp_OrL2 _ _ _)).
Qed.

Definition gs_lja_ilrules V A Γ1 Γ2 G ps c := @gs_ljg_glrules V
  A _ _ _ Γ1 Γ2 G ps c LJAil_single il_anc' lja_ctr_il.

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
apply srs_ext_relI_alt ; apply fst_relI ; ertac A ; 
apply ext_relI_nil ; apply fslr_I ;  apply ImpL_Imp_inv2s_I | 
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

(* Proposition 5.1, contraction admissibility for LJA *)
Lemma ctr_adm_lja V (fml : PropF V) :
  forall seq, derrec LJArules emptyT seq ->
  can_rel LJArules (fun fml' => srs_ext_rel (sctr_rel fml')) fml seq.
Proof. eapply gen_step_lemT. apply AccT_tc.  apply AccT_dnsubfml.
intros * ljpc. destruct ljpc.
destruct r. destruct l.
- (* LJAilrules *)
eapply gen_step_sub_mono. intro. apply tT_step.
exact (gs_lja_ilrules _ _ r).
- (* ImpL_Imp_rule *)
exact (gs_lja_ImpL_Imp _ _ i).
- (* ImpLrule *)
eapply gen_step_sub_mono. intro. apply tT_step.
exact (gs_lja_ImpL _ _ i).
- (* ImpRrule *)
exact (gs_lja_ImpR _ _ _ i).
- (* Idrule *)
eapply gs_sctr_Id. 2: exact i. apply rsubI. apply Id_anc.
- (* left rules *)
eapply gen_step_sub_mono. intro. apply tT_step.
exact (gs_lja_lrules _ _ r).
- (* right rules *)
exact (gs_lja_rrules _ _ _ r).
Qed.

Check ctr_adm_lja.

(* for contracting a list of formulae in LJA *)
Definition lctr_adm_lja V fmls :=
  @lctr_adm_gen _ _ (@LJArules V) fmls (@ctr_adm_lja V).

(* Proposition 5.2, admissibility of LJ in LJA *)
Lemma lj_ImpL_adm_lja {V} : rsub (fst_ext_rls ImpLrule) (adm (@LJArules V)).
Proof. split. destruct X.
inversion r. subst. clear r. destruct X.
simpl. unfold fmlsext. intro drs.
inversion drs. inversion X0. subst. clear drs X0 X2.
(* weaken second premise *) apply (insL_lja _ _ [Imp A B]) in X1.
(* apply Lemma 4.1 *) eapply LJA_ImpL_adm in X.
unfold l41prop in X.
specialize (X (Γ1 ++ [Imp A B]) Γ2).  require X. list_eq_assoc.
simpl in X. unfold fmlsext in X. 
specialize (X B G). require X. apply (eq_rect _ _ X1). list_eq_assoc.
eapply ctr_adm_lja in X.
(* contract Imp A B *) sersctrtac X (Imp A B). 
apply (eq_rect _ _ X). list_eq_assoc. Qed.

(* at this point we have that LJA is complete wrt LJ *)
Lemma der_lj_lja V :
  (forall c (d : derrec (@LJrules V) emptyT c), derrec LJArules emptyT c) *
  (forall cs (ds : dersrec (@LJrules V) emptyT cs), dersrec LJArules emptyT cs).
Proof. apply derrec_dersrec_rect_mut.
- intros. destruct p.
- intros.  clear d. destruct r. destruct r. destruct l.
+ apply derrec_adm.
apply (derI' _ (dersrec_rmono (rsub_adm _) X)).
apply lj_ImpL_adm_lja. eapply fextI. apply rmI. apply i.
+ apply (derI' _ X). eapply fextI. apply rmI. apply (ImpR_anc i).
+ apply (derI' _ X). eapply fextI. apply rmI. apply (Id_anc i).
+ apply (derI' _ X). eapply fextI. apply rmI. apply (lrls_anc r).
+ apply (derI' _ X). eapply fextI. apply rmI. apply (rrls_anc r).
- apply dlNil.
- intros. apply dlCons ; assumption.
Qed.

(* cut adm in LJA via equivalence to LJ *)
Theorem lja_cut_adm_alt V fml cl cr: derrec (@LJArules V) emptyT cl ->
  derrec LJArules emptyT cr -> cedc LJArules fml cl cr.
Proof. intros dl dr. split. intros * cle cre.
apply (fst (der_lja_lj V)) in dl.  apply (fst (der_lja_lj V)) in dr.
apply (fst (der_lj_lja V)).  destruct (lj_cut_adm fml dl dr).
exact (d _ _ _ _ cle cre). Qed.

(* Proposition 5.3 of Dyckhoff & Negri JSL 2000 *)
(* relevant property of sequent to be proved by induction *)
Definition l53prop {V} (AB : PropF V) seq :=
  forall A B, AB = Imp A B -> 
  forall G1 G2 E, seq = (G1 ++ AB :: G2, E) -> 
  derrec LJArules emptyT (G1 ++ B :: G2, E).

Ltac inv53tac X B fp dl grls_anc :=
eapply derI ; [ eapply fextI ;
eapply (rmI_eqc _ _ _ _ (grls_anc _ _ _ _ (rmI _ _ _ _ X))) ;
simpl ;  unfold fmlsext ;  reflexivity |
eapply (usefmm _ _ _ _ _ fp) ;
intro ; simpl ; intro dl ; apply snd in dl ;
unfold l53prop in dl ; specialize (dl _ _ eq_refl) ;
unfold fmlsext ; assoc_single_mid' B ; apply dl ;
unfold fmlsext ; list_eq_assoc ].

Lemma gs_LJA_53_sl V (D : PropF V) any ps c Γ1 Γ2 G 
  (r : rlsmap (flip pair G) LJslrules ps c) :
  gen_step l53prop D any (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad.
unfold l53prop. intros * deq * ceq. subst.
inversion r. subst. clear r. 
inversion ceq. subst. clear ceq. unfold fmlsext in H0.
acacD'T2 ; subst. (* 6 subgoals *)

- apply LJsl_sing in X. cD. inversion X0.

- inversion X ; subst ; rename_last slr ; inversion slr.

- assoc_mid c0.  inv53tac X B fp dl @lrls_anc.

- rewrite ?app_nil_r in X. assoc_mid H0. inv53tac X B fp dl @lrls_anc.

- pose (LJsl_sing X). cD. list_eq_ncT. sD.
+ inversion s1. subst. clear s1.
simpl in X.
inversion X ; subst ; rename_last slr ; inversion slr.
+ inversion s1.

- assoc_mid c0.  inv53tac X B fp dl @lrls_anc.
Qed.

Lemma gs_LJA_53_Ail V (D : PropF V) ps c Γ1 Γ2 G 
  (r : rlsmap (flip pair G) LJAilrules ps c) :
  gen_step l53prop D (clos_transT dnsubfml) (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. 
unfold l53prop. intros * deq * ceq. subst.
inversion r. subst. clear r. 
inversion ceq. subst. clear ceq. unfold fmlsext in H0.
acacD'T2 ; subst. (* 6 subgoals *)

- apply LJAil_sing in X. cD. inversion X0.

- clear dc. inversion X ; subst ; inversion X0 ; subst ; clear X X0 ;
inversion fp ; subst ; clear fp X0 ; apply fst in X.
+ (* Imp_AndL *) pose (sad _ (tT_step _ _ _ (dnsub_Imp_AndL _ _ _)) _ X).
specialize (l _ _ eq_refl G1 Γ2 E).
require l. unfold fmlsext. list_eq_assoc. clear X.
specialize (sad (Imp D B)).
require sad.  eapply tT_trans ; apply tT_step.
apply dnsub_ImpR.  apply dnsub_Imp_AndL.
specialize (sad _ l _ _ eq_refl _ _ _ eq_refl). exact sad.
+ (* Imp_OrL *) pose (sad _ (tT_step _ _ _ (dnsub_Imp_OrL1 _ _ _)) _ X).
specialize (l _ _ eq_refl G1 (Imp D B :: Γ2) E).
require l. unfold fmlsext. list_eq_assoc. clear X.
specialize (sad _ (tT_step _ _ _ (dnsub_Imp_OrL2 _ _ _)) _ l).
specialize (sad _ _ eq_refl (G1 ++ [B]) Γ2 E).
require sad. unfold fmlsext. list_eq_assoc. clear l.
(* now need to contract B *)
eapply ctr_adm_lja in sad.  sersctrtac sad B.
apply (eq_rect _ _ sad). list_eq_assoc.

- clear sad. assoc_mid c0.  inv53tac X B fp dl @il_anc.

- rewrite ?app_nil_r in X. assoc_mid H0. inv53tac X B fp dl @il_anc.

- pose (LJAil_sing X). cD. list_eq_ncT. sD.
+ inversion s1. subst. clear s1.
simpl in X.  clear dc.
inversion X ; subst ; inversion X0 ; subst ; clear X X0 ;
inversion fp ; subst ; clear fp X0 ; apply fst in X.
++ (* Imp_AndL *) pose (sad _ (tT_step _ _ _ (dnsub_Imp_AndL _ _ _)) _ X).
specialize (l _ _ eq_refl Γ1 Γ2 E).
require l. unfold fmlsext. list_eq_assoc. clear X.
specialize (sad (Imp D B)).
require sad.  eapply tT_trans ; apply tT_step.
apply dnsub_ImpR.  apply dnsub_Imp_AndL.
rewrite ?app_nil_r.
specialize (sad _ l _ _ eq_refl _ _ _ eq_refl). exact sad.
++ (* Imp_OrL *) pose (sad _ (tT_step _ _ _ (dnsub_Imp_OrL1 _ _ _)) _ X).
specialize (l _ _ eq_refl Γ1 (Imp D B :: Γ2) E).
require l. unfold fmlsext. list_eq_assoc. clear X.
specialize (sad _ (tT_step _ _ _ (dnsub_Imp_OrL2 _ _ _)) _ l).
specialize (sad _ _ eq_refl (Γ1 ++ [B]) Γ2 E).
require sad. unfold fmlsext. list_eq_assoc. clear l.
(* now need to contract B *)
eapply ctr_adm_lja in sad.  sersctrtac sad B.
apply (eq_rect _ _ sad). list_eq_assoc.

+ inversion s1.

- clear sad. assoc_mid c0.  inv53tac X B fp dl @il_anc.

Qed.

Check gs_LJA_53_Ail.

Ltac inv53itac B fp c dl grls_anc :=
eapply derI ; [ eapply fextI ;
eapply (rmI_eqc _ _ _ _ (grls_anc _ _ _)) ;
simpl ;  unfold fmlsext ;  reflexivity |
eapply (usefm _ _ _ fp) ; clear fp ;
intro c ; destruct c ; simpl ; unfold fmlsext ;
intro dl ; apply snd in dl ;
unfold l53prop in dl ; specialize (dl _ _ eq_refl) ;
assoc_single_mid' B ; apply dl ; list_eq_assoc ].

Lemma gs_LJA_53_Imp V D any ps c Γ1 Γ2 (r : @ImpL_Imp_rule V ps c) :
  gen_step l53prop D any (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad dc.
unfold l53prop. intros * deq * ceq. subst.
destruct r.
inversion ceq. subst. clear ceq. unfold fmlsext in H0.
acacD'T2 ; subst. (* 7 subgoals *)

- inversion fp.  inversion X0.
apply (eq_rect _ _ (fst X1)).  unfold fmlsext. list_eq_assoc.

- assoc_mid [Imp (Imp C D) B0].  inv53itac B fp c dl (@Imp_anc' V B0).

- inversion H4.

- list_eq_ncT. cD. subst. clear H0.
assoc_mid [Imp (Imp C D) B0].  inv53itac B fp c dl (@Imp_anc' V B0).

- inversion H5. subst. clear H5.  inversion fp.  inversion X0.
apply (eq_rect _ _ (fst X1)).  unfold fmlsext. list_eq_assoc.

- list_eq_ncT. inversion H8.

- assoc_mid [Imp (Imp C D) B0].  inv53itac B fp c dl (@Imp_anc' V B0).
Qed.

Check gs_LJA_53_Imp.

Lemma gs_LJA_53_ImpL_p V D any ps c Γ1 Γ2 (r : @ImpLrule_p V ps c) :
  gen_step l53prop D any (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad dc.
unfold l53prop. intros * deq * ceq. subst.
destruct r.
inversion ceq. subst. clear ceq. unfold fmlsext in H0.
acacD'T2 ; subst. (* 7 subgoals *)

- inversion fp.  inversion X0.
apply (eq_rect _ _ (fst X1)).  unfold fmlsext. list_eq_assoc.

- assoc_mid [Imp (Var p) B0].  inv53itac B fp c dl (@ImpL_anc' V).

- inversion H4.

- list_eq_ncT. cD. subst. clear H0.
assoc_mid [Imp (Var p) B0].  inv53itac B fp c dl (@ImpL_anc' V).

- inversion H5. subst. clear H5.  inversion fp.  inversion X0.
apply (eq_rect _ _ (fst X1)).  unfold fmlsext. list_eq_assoc.

- list_eq_ncT. inversion H8.

- assoc_mid [Imp (Var p) B0].  inv53itac B fp c dl (@ImpL_anc' V).
Qed.

Check gs_LJA_53_ImpL_p.

Lemma gs_LJA_53_sr V (D : PropF V) ps c Γ1 Γ2 
  (r : rlsmap (pair []) LJsrrules ps c) :
  gen_step l53prop D (clos_transT dnsubfml) (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad.
unfold l53prop. intros * deq * ceq. subst.
inversion r. subst. clear r. 
inversion ceq. subst. clear ceq. 
assert (map (apfst (fmlsext Γ1 Γ2)) (map (pair []) ps0) =
  map (pair (G1 ++ Imp A B :: G2)) ps0).
{ clear X fp.  induction ps0 ; simpl.
reflexivity. rewrite IHps0. rewrite H0. reflexivity. }
rewrite H in fp.
eapply derI.  eapply fextI.  eapply rmI_eqc.
apply rrls_anc.  apply rmI.  exact X.
simpl. unfold fmlsext. reflexivity.
eapply (usefm12 _ _ _ _ fp). clear fp.
intro ; simpl ; intro dl ; apply snd in dl ;
unfold l53prop in dl ; specialize (dl _ _ eq_refl _ _ _ eq_refl) ;
unfold fmlsext ; exact dl.
Qed.

Lemma gs_LJA_53_Id V D p ps c Γ1 Γ2 (r : Idrule (@Var V p)ps c) :
  gen_step l53prop D (clos_transT dnsubfml) (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad fp.
unfold l53prop. intros * deq * ceq. subst.
inversion r. subst. clear r.
inversion ceq. subst. clear ceq.
unfold fmlsext in H0.
eapply gen_der_Id. unfold rsub. apply Id_anc.
acacD'T2 ; subst ; try solve_InT ; rename_last vi ; inversion vi.
Qed.

Lemma gs_LJA_53_ImpR V D ps c Γ1 Γ2 (r : @ImpRrule V ps c) :
  gen_step l53prop D (clos_transT dnsubfml) (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad dc.
unfold l53prop. intros * deq * ceq. subst.
destruct r.  inversion ceq. subst. clear ceq.
unfold fmlsext in H0. simpl in H0.
simpl in fp. unfold fmlsext in fp.
inversion fp. subst. clear fp X0.
apply snd in X. unfold l53prop in X. specialize (X _ _ eq_refl).
acacD'T2 ; subst.
- specialize (X (G1 ++ [A0]) G2 B0). require X. list_eq_assoc.
eapply derI.  eapply fextI. eapply rmI_eqc. apply ImpR_anc'.  reflexivity.
apply dersrec_singleI.  apply (eq_rect _ _ X). list_eq_assoc.
- specialize (X G1 (H2 ++ A0 :: Γ2) B0). require X. list_eq_assoc.
eapply derI.  eapply fextI. eapply rmI_eqc. apply ImpR_anc'.  
list_assoc_l'.  reflexivity.
apply dersrec_singleI.  apply (eq_rect _ _ X).
simpl. unfold fmlsext.  list_eq_assoc.
- specialize (X (Γ1 ++ A0 :: H0) G2 B0). require X. list_eq_assoc.
eapply derI.  eapply fextI. eapply rmI_eqc. apply ImpR_anc'.  
list_assoc_r'. simpl. unfold fmlsext. simpl.  reflexivity.
apply dersrec_singleI.  apply (eq_rect _ _ X).  list_eq_assoc.
Qed.

Lemma gs_LJA_53 V D ps c Γ1 Γ2 (r : @LJAncrules V ps c) :
  gen_step l53prop D (clos_transT dnsubfml) (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. destruct r.
- eapply gs_LJA_53_Ail. exact r.
- apply gs_LJA_53_Imp. exact i.
- apply gs_LJA_53_ImpL_p. exact i.
- apply gs_LJA_53_ImpR. exact i.
- eapply gs_LJA_53_Id. exact i.
- eapply gs_LJA_53_sl. exact r.
- apply gs_LJA_53_sr. exact r.
Qed.

Lemma ImpL_inv_adm_lja V (D : PropF V) :
  forall seq, derrec LJArules emptyT seq -> l53prop D seq.
Proof. eapply gen_step_lemT. apply AccT_tc.  apply AccT_dnsubfml.
intros * ljpc. destruct ljpc. destruct r. apply gs_LJA_53. apply l. Qed.

Check ImpL_inv_adm_lja.

(* cut admissibility *)
(* when trying to Load in 8.11 this seems to fail with message 
File "/home/jeremy/coq/lnt/tense-logic-in-Coq/ljt/ljt_dncc.v",
line 581, characters 56-71:
Error: Anomaly "Uncaught exception Not_found."
Please report at http://coq.inria.fr/bugs/.

Definition lja_lrlsR_rrlsL V fml la lc rc D psl psr :=
  @gen_lrlsR_rrlsL V LJAncrules fml la lc rc D psl psr (@lctr_adm_lja V).
  *)
