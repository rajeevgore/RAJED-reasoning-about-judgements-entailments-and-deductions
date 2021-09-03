
(* current proofs in progress
hs2_Query_maell_Q done
hs2_Bangrule_maell_Q done
gs2_Bangrule_mall_Q done
hs2_maell_Q 
*)

(* for maell_rules, using osscamq *)

Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT ddT dd_fc.
Require Import gen_tacs swappedT.
Require Import List_lemmasT.
Require Import fmlsext.
Require Import lldefs.
Require Import ll_lems.
Require Import ll_exch.
Require Import ll_cam.
Require Import gstep gentree.

Lemma merge_dbl_ctr_lem W rules xs ys zs 
  (ctrm : forall q : W, InT q ys -> rsub (fmlsruleg (ctrrule q)) rules) :
  merge xs ys zs -> {zsd : _ & merge xs (doubles ys) zsd &
    forall us vs ps, derrec rules ps (us ++ zsd ++ vs) -> 
     derrec rules ps (us ++ zs ++ vs)}.
Proof. intro m.  induction m.
- destruct (IHm ctrm).  exists (x :: x0).  exact (mergeLI _ m0).
intros.  specialize (d (us ++ [x]) vs ps).
rewrite - !app_assoc in d. exact (d X).
- require IHm. { intros. apply ctrm. exact (InT_cons y X). }
cD. exists (y :: y :: IHm).  exact (mergeRI _ (mergeRI _ IHm0)).
intros.  specialize (IHm1 (us ++ [y;y]) vs ps).
rewrite - !app_assoc in IHm1.  specialize (IHm1 X).
specialize (ctrm _ (InT_eq _ _)).
eapply derI. apply ctrm.  eapply OSgctxt_eq.
apply ctrrule_I.  simpl. reflexivity.  reflexivity.
sfs.  exact (dersrec_singleI IHm1).
- exists []. exact merge_nil. easy.  Qed.

Print Implicit merge_dbl_ctr_lem.

Definition merge_dbl_ctr_lem' W rules xs ys zs cc m :=
  @merge_dbl_ctr_lem W rules xs ys zs m cc.

(* according to Dirk Roorda's thesis, shouldn't need this in general
  but do need revised version, rh rule is principal Bangrule
  dual and isubfml are generic *)

Lemma merge_paramL_ngl V (A : LLfml V) rules dual n any prsl prsr xs ys zs
  drsb psa psb ca cb :
  rsub prsl (fun _ => sing) -> rsub prsr (fun _ => sing) ->
  merge_ctxt xs ys prsl psa ca -> leT n (length xs) ->
  fmlsrule [] (map (@Query V) zs) prsr psb cb -> 
  rsub (fmlsruleg ctrqrules) rules -> rsub (merge_ctxtg prsl) rules -> 
  gen_step2 (osscangl dual rules n) (Query A) any (derrec rules emptyT)
    drsb psa ca psb cb.
Proof. intros pls prs mcp lxs mqr rsq rsmr. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpr dl dr. 
apply osscanglI. intros. apply osscanI.
intros * cae cbe mrg.
inversion mcp. clear mcp. subst.
pose (rsubD pls _ c X). simpl in s. destruct s.
pose (leT_trans H lxs) as lmxs.
pose (get_prefix _ lmxs). cD. subst xs.
rewrite <- app_assoc in H3.
apply strip_prefixes in H3.  cD.
2: rewrite s0 ; rewrite repeat_length ; reflexivity.
clear lmxs s0. subst. 
apply merge_ctns_singleL in mrg. cD. subst.
apply merge_splitM in H0. cD. subst.
apply merge_repeat in H5. cD. subst.

assert (forall q, InT q (mrg ++ mrg0) -> {q' : _ & q = Query q'}).
{ intros q inq. inversion mqr.
apply prs in X0. destruct X0. inversion H6.
rewrite - H10 in inq.
apply InT_mapE in inq. cD. subst. exists inq. reflexivity. }

(* cut with lh premise of merging rule *)
inversion fpl. subst. cD. clear X0.  destruct X2.
specialize (o H5 (leT_trans (leT_plus_l _ _) H)).
destruct o. rewrite <- !app_assoc in d.

(* cut with rh premise of merging rule *)
inversion X1. subst. cD. clear fpl X0 X1 X2. destruct X3.
specialize (o H7 (leT_trans (leT_plus_r _ _) H)).
destruct o. rewrite <- !app_assoc in d0.

(* now use merge_assoc4, and merge_doubles for mrg and mrg0 
  need to get versions of mrg1 amd mrg2 with formulae from mrg and mrg0
  doubled, and show that mrg and mrg0 are Query formulae,
  and show that contraction makes it equivalent *)

eapply merge_dbl_ctr_lem' in mrg3.
eapply merge_dbl_ctr_lem' in mrg6.  cD.

pose (merge_assoc4 H8 (merge_doubles mrg) mrg4).
pose (merge_assoc4 H1 (merge_doubles mrg0) mrg7). cD.

specialize (d _ _ (s ++ pl ++ s0) eq_refl eq_refl).
specialize (d0 _ _ (s7 ++ pr ++ s3) eq_refl eq_refl).

require d.  apply (merge_app s6).  apply (merge_app (merge_Rnil _) s2).
require d0.  apply (merge_app s8).  apply (merge_app (merge_Rnil _) s4).

(* now apply contractions *)
apply (mrg5 [] ([a] ++ mrg2)).
eapply eq_rect.  apply (mrg8 (mrg3 ++ [a]) []).
rewrite - app_assoc. rewrite app_nil_r.

(* now apply rule to d and d0 *)
eapply derI. apply rsmr. eapply merge_ctxtgI.
eapply merge_ctxtI. exact X. exact s9. exact s5.
exact (dlCons d (dersrec_singleI d0)).
rewrite - app_assoc. rewrite app_nil_r. reflexivity.

intros q inq.  eapply (rsub_trans _ rsq).
intros q inq.  eapply (rsub_trans _ rsq).

Unshelve.
apply fmlsruleg_mono.
specialize (H0 _ (InT_appR _ inq)). cD.  subst.
intros u v. apply ctrqrules_I.

apply fmlsruleg_mono.
specialize (H0 _ (InT_appL _ inq)). cD.  subst.
intros u v. apply ctrqrules_I. Qed.

Print Implicit merge_paramL_ngl.

Lemma merge_paramL_ngl_QT V (A : LLfml V) rules dual n any prsr xs ys zs
  drsb psa psb ca cb :
  rsub prsr (fun _ => sing) ->
  merge_ctxt xs ys Tensrule psa ca -> 
  fmlsrule [] (map (@Query V) zs) prsr psb cb -> 
  rsub (fmlsruleg ctrqrules) rules -> rsub (merge_ctxtg Tensrule) rules -> 
  gen_step2 (osscangl dual rules n) (Query A) any (derrec rules emptyT)
    drsb psa ca psb cb.
Proof. intros prs mcp mqr rsq rsmr.
pose (leT_or_gt n (length xs)) as lg. destruct lg.
eapply (merge_paramL_ngl _ _ _ (rsubI _ _ tens_sing)
  prs mcp l mqr rsq rsmr).
epose (merge_paramL_ngl _ _ _ (rsubI _ _ tens_sing) 
  prs mcp (leT_n _) mqr rsq rsmr).
pose (leT_trans (leT_S (leT_n _)) l) as lxn. 
apply leT_ex_plus in lxn. cD. subst. 
(* lxn not zero *)
destruct lxn. apply leT_S_F in l. destruct l.
apply (gs_osscan_gl_lem2 g).
intros m lml.  apply osscanI.  intros * cae cbe mrg.
destruct mcp. inversion t. subst.
rewrite PeanoNat.Nat.add_comm in cae.
rewrite repeat_add in cae.
clear m0 l g.  induction xs ; simpl in cae ; inversion cae.
simpl in IHxs. exact (IHxs H1). Qed.

Print Implicit merge_paramL_ngl_QT.

Lemma plusL_wth_q V (A : LLfml V) rules ys zs drsa drsb psa psb ca cb :
  fmlsrule [] ys PlusLrule psa ca -> 
  fmlsrule [] zs Wthrule psb cb -> 
  gen_step2 (osscamq dual rules) A isubfml drsa drsb psa ca psb cb.
Proof. intros psca pscb. apply gs_osscamq_lem.  intros * caes cbes.
inversion psca. subst.  inversion pscb. subst.
destruct X. destruct X0.
unfold fmlsext in caes. unfold fmlsext in cbes.
simpl in caes. simpl in cbes.
apply gs_osscam_q_lem.
- intros * ae. subst.
sD ; repeat ((inversion caes ; subst) || (inversion cbes ; subst)).
- intros * ae. subst.
sD ; repeat ((inversion caes ; subst) || (inversion cbes ; subst)).
- exact (plusL_wth drsa drsb psca pscb). Qed.

Lemma plusR_wth_q V (A : LLfml V) rules ys zs drsa drsb psa psb ca cb :
  fmlsrule [] ys PlusRrule psa ca -> 
  fmlsrule [] zs Wthrule psb cb -> 
  gen_step2 (osscamq dual rules) A isubfml drsa drsb psa ca psb cb.
Proof. intros psca pscb. apply gs_osscamq_lem.  intros * caes cbes.
inversion psca. subst.  inversion pscb. subst.
destruct X. destruct X0.
unfold fmlsext in caes. unfold fmlsext in cbes.
simpl in caes. simpl in cbes.
apply gs_osscam_q_lem.
- intros * ae. subst.
sD ; repeat ((inversion caes ; subst) || (inversion cbes ; subst)).
- intros * ae. subst.
sD ; repeat ((inversion caes ; subst) || (inversion cbes ; subst)).
- exact (plusR_wth drsa drsb psca pscb). Qed.

Check plusL_wth_q.  Check plusR_wth_q.

Definition wth_plusL_q V A rules ys zs drsa drsb psa psb ca cb rla rlb :=
  gs2_osscamq_dual' 
    (@plusL_wth_q V (dual A) rules ys zs drsb drsa psb psa cb ca rlb rla).
Definition wth_plusR_q V A rules ys zs drsa drsb psa psb ca cb rla rlb :=
  gs2_osscamq_dual' 
    (@plusR_wth_q V (dual A) rules ys zs drsb drsa psb psa cb ca rlb rla).

Check wth_plusL_q.  Check wth_plusR_q.

Lemma tens_par_q V (A : LLfml V) rules ys zs drsa psa psb ca cb :
  merge_ctxt [] ys Tensrule psa ca -> 
  fmlsrule [] zs Parrule psb cb -> 
  gen_step2 (osscamq dual rules) A isubfml drsa
         (derrec rules emptyT) psa ca psb cb.
Proof. intros psca pscb. apply gs_osscamq_lem.  intros * caes cbes.
inversion psca. subst.  inversion pscb. subst. 
inversion X. destruct X0. inversion H. subst. clear X H.
unfold fmlsext in cbes.
simpl in caes. simpl in cbes.
apply gs_osscam_q_lem.
- intros * ae. subst. simpl in cbes.
sD ; repeat ((inversion caes ; subst) || (inversion cbes ; subst)).
- intros * ae. subst. simpl in cbes.
sD ; repeat ((inversion caes ; subst) || (inversion cbes ; subst)).
- exact (tens_par _ psca pscb). Qed.

Definition par_tens_q V A rules ys zs drsb psa psb ca cb rla rlb :=
  gs2_osscamq_dual' 
    (@tens_par_q V (dual A) rules ys zs drsb psb psa cb ca rlb rla).

Check tens_par_q. Check par_tens_q.

Lemma bot_one_q V (A : LLfml V) rules any ys drsb psa psb ca cb :
  fmlsrule [] ys Botrule psa ca -> Onerule psb cb -> 
  gen_step2 (osscamq dual rules) A any (derrec rules emptyT)
         drsb psa ca psb cb.
Proof. intros psca pscb. apply gs_osscamq_lem.  intros * caes cbes.
inversion psca. subst.  inversion pscb. subst.
destruct X. 
unfold fmlsext in caes.  simpl in caes.
apply gs_osscam_q_lem.
- intros * ae. subst. simpl in cbes.
sD ; repeat ((inversion caes ; subst) || (inversion cbes ; subst)).
- intros * ae. subst. simpl in cbes.
sD ; repeat ((inversion caes ; subst) || (inversion cbes ; subst)).
- exact (bot_one any drsb psca pscb). Qed.

Definition one_bot_q V A rules ys drsa psa psb ca cb rla rlb :=
  gs2_osscamq_dual' 
    (@bot_one_q V (dual A) rules _ ys drsa psb psa cb ca rlb rla).

Lemma query_bang V (A : LLfml V) rules ys zs drsa drsb psa psb ca cb :
  fmlsrule [] ys Queryrule psa ca -> fmlsrule [] zs Bangrule psb cb -> 
  gen_step2 (osscam dual rules) A isubfml drsa drsb psa ca psb cb.
Proof. intros fqa fbb saa fpl fpr da db.
inversion fqa.  inversion fbb. destruct X. destruct X0. subst. sfs.
apply osscamI. intros * qe be mrg. inversion qe. inversion be. subst.
simpl in H2. inversion H2. subst.
simpl in fpl. unfold fmlsext in fpl. simpl in fpl.
simpl in fpr. unfold fmlsext in fpr. simpl in fpr.
apply ForallT_singleD in fpl.  apply ForallT_singleD in fpr. cD.
specialize (saa _ (isub_Query _) _ fpl _ fpr). destruct saa.
exact (d _ _ _ eq_refl eq_refl mrg). Qed.

Definition adm_exch_maell_d V c c' d sw := admDs (@adm_exch_maell V c c' sw) d.
Print Implicit adm_exch_maell_d.

Lemma map_eq_single A B (f : A -> B) xs y :
  map f xs = [y] -> { x : A & xs = [x] & y = f x}.
Proof. intro. destruct xs ; simpl in H ; inversion H.
apply map_eq_nil in H2. subst. exists a ; reflexivity. Qed.

(* lemma for Query and Bang rules, where Bang principal 
  as with gs_ctr_ng and gs_wk_ng can't express whether Query rule principal *)

Lemma query_bang_mQ_ht V (A : LLfml V) zs 
  (dta dtb : derrec_fc maell_rules emptyT) psa psb ca cb 
  (btra : botRule_fc dta psa ca) (btrb : botRule_fc dtb psb cb) :
  fmlsruleg Queryrule psa ca -> 
  fmlsrule [] (map (@Query V) zs) Bangrule psb cb -> 
  height_step2_tr (dt2fun (osscamQ dual maell_rules)) (Query A) isubfml dta dtb.

Proof. intros fqa fbb saa fpl fpr.  unfold dt2fun.
rewrite (botRule_fc_concl btra).  rewrite (botRule_fc_concl btrb).
destruct dta.  pose (botRule_fc_concl btra).
rewrite -> der_fc_concl_eq in e. subst.
destruct dtb.  pose (botRule_fc_concl btrb).
rewrite -> der_fc_concl_eq in e. subst.
pose (botRule_fc_prems btra). cD. subst. 
pose (botRule_fc_prems btrb). cD. subst. 
clear p p0. apply osscaQ_mQ.
apply osscaQI. intros A0 qq. clear A0 qq.
apply osscangI. intro n.
pose (fmlsrule_g_ex fqa) as fxy. cD.
pose (leT_or_gt n (length fxy)) as lg. destruct lg.

- (* parametric case *) 
(* would be simpler to use usenX above if it is valid, and gs_osscan_g_ht_lem *)
epose (princ_paramL_n empty_relT (derrec maell_rules emptyT)
  (derrec maell_rules emptyT) (@query_sing _) fxy1 l (rsubI _ _ query_maellI)).
(* eapply gs2_gs2c in g. fails *)
epose (fst (gs2_gs2c _ _ _ d d0) g).
eapply gs2c_gs2tr in g0.  eapply gs2_tr_height in g0.
destruct g0. (* this does a lot! *)
+ intros A' eaa. inversion eaa.
+ intros dtp m.  specialize (fpl dtp m).
unfold dt2fun in fpl.  unfold dt2fun.  destruct fpl.  destruct p.
destruct o0.  specialize (o0 A eq_refl).  destruct o0. exact (o0 n).
+ intros dtq m.  specialize (fpr dtq m).
unfold dt2fun in fpr.  unfold dt2fun.  destruct fpr.  destruct p.
destruct o0.  specialize (o0 A eq_refl).  destruct o0. exact (o0 n).
+ apply osscanI.  rewrite !der_fc_concl_eq in d1.  exact d1.

- (* two parametric cases, excluded by n > length fxy, and principal case *)
destruct fxy1. destruct q. unfold fmlsext. simpl.
apply osscanI. intros * cae cbe mrg.
acacD'T2 ; subst.
(* two parametric cases, excluded by condition n > length fxy *)
+ rewrite app_length in l. rewrite repeat_length in l.
destruct (leT_S_F (leT_trans l (leT_plus_l _ _))).
+ rewrite app_nil_r in cae0. subst. rewrite repeat_length in l.
destruct (leT_S_F l).
+ (* principal case *)
apply repeat_eq_app in cae0. cD. destruct cae3 ; inversion cae4.
clear cae4. subst.
simpl in btra. unfold fmlsext in btra. simpl in btra.
(* inversion d. inversion H.
this doesn't tell you that d is of the form derI ... *)
(* revert btra. dependent inversion d. fails *) (* destruct d. fails *)
pose (botRule_fc_ps btra).
apply map_eq_single in e. cD.
assert (InT e (nextup (fcI d))). rewrite e0. apply InT_eq.
apply nextup_height in X.
(* need to do height-preserving exchange *)
unfold measure in fpl.  
destruct e. rewrite der_fc_concl_eq in e1.
pose (@exch_maell_ht _ _ d1 (repeat (Query A) (cae0 + cae3) ++ A :: ls)).
require s. subst.  rewrite repeat_add. swap_tac_Rc. cD.
(* now induction on height of derivation, as height <= left derivation *)
specialize (fpl (fcI s)).  require fpl.
eapply PeanoNat.Nat.lt_le_trans.
2: apply X. simpl. apply Lt.le_lt_n_Sm. exact s0.
clear fqa btra.  unfold dt2fun in fpl.
destruct fpl.  destruct p.  destruct o0.  specialize (o0 _ eq_refl).
destruct o0.  specialize (o0 (Nat.add cae0 cae3)).  destruct o0.
rewrite !der_fc_concl_eq in d2.
specialize (d2 _ _ _ eq_refl eq_refl (mergeLI A mrg)).

(* now induction on the formula using d2 and nextup of d0 *)
specialize (saa A (isub_Query A) (fcI d2)).
inversion fbb.  destruct X0.  unfold fmlsext in H. simpl in H.
inversion H. subst. clear H.
simpl in H0. unfold fmlsext in H0. simpl in H0.
pose (botr_ps_der d0).
(* rewrite <- H in d3. fails - why ?? *)
pose (eq_rect_r _ d3 H0).  apply dersrec_singleD in d4.
specialize (saa (fcI d4) (AccT_measure _ _) (AccT_measure _ _)).
unfold dt2fun in saa. destruct saa.
rewrite !der_fc_concl_eq in o0.  destruct o0.  simpl in d5.
epose (merge_doubles_via_der mrg) as mrgd. cD.
require mrgd. intros q inmq.  apply InT_mapE in inmq. cD. subst.
apply rsubI.  apply ctrqrules_I.
cD.  specialize (d5 _ _ _ eq_refl eq_refl mrgd2).
apply (derl_mono ctrq_maell) in mrgd1.
exact (derl_derrec_trans mrgd1 (dersrec_singleI d5)).
Qed.

(* note goal for this one is osscam because of the complications
  for merge_paramL where Bang or Query involved *) 
Lemma gs_tens_maell V (A : LLfml V) rules psa psb ca cb
  (rs : rsub maell_rules rules)
  (adm_exch : forall seq seq' : list (LLfml V),
             swapped seq' seq -> adm rules [seq'] seq)
  (ma : merge_ctxtg Tensrule psa ca) (mb : maell_rules psb cb) :
  gen_step2 (osscam dual rules) A isubfml (derrec rules emptyT)
    (derrec rules emptyT) psa ca psb cb.
Proof. inversion ma. subst. rename_last mca.  
pose mca as mca'. destruct mca'. destruct cl.
(* tensor rule with no context on left, cut formula is tensor *)
- inversion m. clear m. apply gs_osscam_lem.
intros * cae cbe. destruct t. simpl in cae.  inversion cae.
subst. clear cae.
simpl. simpl in mb.
simpl in ma.  inversion mb ; subst.
+ exact (gs_tens_mall' (rsub_trans (rsubI _ _ mall_maellI) rs) adm_exch ma X).
+ inversion X.  unfold fmlsext in H1. destruct Φ1 ; simpl in H1.
* destruct X0. inversion H1.

* exact (princ_paramR (@wk_sing _ _) (OSctxt _ _ _ _ _ X0)
    (rsub_trans (rsubI _ _ (@wk_maellI _ _)) rs)).
+ inversion X.  unfold fmlsext in H1. destruct Φ1 ; simpl in H1.
* destruct X0. inversion H1.
* exact (princ_paramR (@ctr_sing _ _) (OSctxt _ _ _ _ _ X0)
    (rsub_trans (rsubI _ _ (@ctr_maellI _ _)) rs)).
+ inversion X.  unfold fmlsext in H. destruct Φ1 ; simpl in H.
* destruct X0. inversion H1.
* exact (princ_paramR (@query_sing _) (OSctxt _ _ _ _ _ X0)
    (rsub_trans (rsubI _ _ (@query_maellI _)) rs)).
+ inversion X. subst. destruct cl ; destruct X0 ; inversion H2.
- (* tensor rule with context on the left *)
  exact (merge_paramL _ tens_sing mca (rsub_trans (rsubI _ _ tens_maellI) rs)).
Qed.

Definition gs_maell_tens V A rules psa psb ca cb rs ae ma mb :=
  gs2_osscam_dual' 
    (@gs_tens_maell V (dual A) rules psb psa cb ca rs ae mb ma).

Check gs_tens_maell.  Check gs_maell_tens.

Lemma gs_mall_q V (A : LLfml V) rules any drsa psa psb ca cb
  (rsmr : rsub mall_rules rules)
  (adm_exch : forall (seq seq' : list (LLfml V)),
    swapped seq' seq -> adm rules [seq'] seq) :
   mall_rules psb cb -> 
  gen_step2 (osscaQ dual rules) A any drsa
         (derrec rules emptyT) psa ca psb cb.
Proof. intros mb.  apply gs_osscaQ_lem.  intros.
inversion mb ; subst. inversion X. destruct Φ1.
- (* llprinc, no left context, principal formulae different from Bang _ *)
unfold fmlsext in H1. simpl in H1.
destruct X0 as [ ps c r | ps c r | ps c r | ps c r | ps c r | ps c r ] ;
destruct r ; simpl in H1 ; inversion H1.
- (* llprinc, non-null left context *)
apply (gen_step2_sub_mono (rsub_emptyT _)).  apply gs_osscang_Q_lem.
apply gs_osscan_g_lem. intro n.
exact (princ_paramR_n_e _ _ llprinc_sing 
  (OSctxt _ _ _ _ _ X0) (rsub_trans princ_mallI rsmr)).
- (* tensor rule *)
inversion X. subst.  destruct cl. 
+ inversion X0. destruct X1. inversion H. 
+ apply (gen_step2_sub_mono (rsub_emptyT _)).  apply gs_osscang_Q_lem.
apply gs_osscan_g_lem. intro n.
exact (merge_paramR_n_e _ tens_sing X0 (rsub_trans tens_mallI rsmr)).
- (* Onerule *) inversion X.
- (* Idrule *) inversion X.
- (* Idrule *) inversion X.
Qed.

Definition gs_mall_q' V A rules drsb psa psb ca cb rsmr ae ma :=
  gs2_Q_Q' (@gs_mall_q V (dual A) rules _ drsb psb psa cb ca rsmr ae ma).

Check gs_mall_q.  Check gs_mall_q'.

Lemma useX (X Y : Type) : (X -> Y) -> (X + Y) -> Y. Proof. tauto. Qed.
(* not sure if this holds
Lemma usenX nt (X : nt -> Type) Y : 
  ((forall n, X n) -> Y) -> (forall n, X n + Y) -> Y.
  *)

(* TODO see if we can use general result princ_paramL_nn for parametric case 

Lemma gs_wk_ng' W (A : W) rules dual any drsa drsb psa psb ca cb :
  rsub (fmlsruleg (wkrule A)) rules -> fmlsruleg (wkrule A) psa ca ->
  gen_step2 (osscang dual rules) A any drsa drsb psa ca psb cb.
Proof. intros rsfw fwa saa fpl fpr da db.
split. intro.
inversion fwa.  unfold fmlsext in H0. simpl in H0. subst.
apply (@useX (leT n (length Φ1))).
intro lenl.
can't make this work as need to get goal osscan to get n to do
cases on leT n (length Φ1), but then have fpl, fpr, saa involving osscang
so can't use princ_paramL_n
*)

(* gs_wcn_ng accommodates both weakening and contraction *)
Lemma gs_wcn_ng W (A : W) ncw rules dual any drsa drsb psa psb ca cb :
  rsub (fmlsruleg (wcnrule ncw A)) rules -> fmlsruleg (wcnrule ncw A) psa ca ->
  gen_step2 (osscang dual rules) A any drsa drsb psa ca psb cb.
Proof. intros rsfw fwa saa fpl fpr da db.  split. intro n.
pose (fmlsrule_g_ex fwa) as fxy. cD. clear fwa.
pose (leT_or_gt n (length fxy)) as lg. destruct lg.
- (* parametric case *) (* next step unfolds gen_step2 *)
  eapply (princ_paramL_n any drsa drsb (@wcn_sing _ _ _) fxy1 l rsfw).
+ intros A' aaa dl dls dr drs.  specialize (saa A' aaa dl dls dr drs).
destruct saa.  exact (o n).
+ fpxtac'' fpl.  destruct (snd fpxa). exact (o n).
+ fpxtac'' fpr.  destruct (snd fpxa). exact (o n).
+ exact da.  + exact db.
- (* two parametric cases, excluded by n > length fxy, and principal case *)
clear fpr saa.
destruct fxy1. destruct w. unfold fmlsext. simpl.
apply osscanI. intros * cae cbe mrg.
acacD'T2 ; subst.
(* two parametric cases, excluded by condition n > length fxy *)
+ rewrite app_length in l. rewrite repeat_length in l.
destruct (leT_S_F (leT_trans l (leT_plus_l _ _))).
+ rewrite app_nil_r in cae0. subst. rewrite repeat_length in l.
destruct (leT_S_F l).
+ (* principal case *)
apply repeat_eq_app in cae0. cD. destruct cae3 ; inversion cae4.
clear cae4. subst.
simpl in fpl.  unfold fmlsext in fpl.  simpl in fpl.
inversion fpl. clear fpl X0. destruct X.  inversion o.

specialize (X (Nat.add ncw (Nat.add cae0 cae3))).  inversion X.
rewrite -> repeat_add in X0.
rewrite -> !app_assoc in X0.
apply (X0 ls rs ms).
rewrite - !repeat_add.
rewrite (PeanoNat.Nat.add_comm cae0 ncw).
rewrite (PeanoNat.Nat.add_assoc). reflexivity.
reflexivity. exact mrg. Qed.

Check gs_wcn_ng.

Lemma wcn_neq_paramL V (A B : LLfml V) ncw rules drsa drsb psa ca psb cb :
  rsub (fmlsruleg (wcnrule ncw (Query B))) rules -> 
  fmlsruleg (wcnrule ncw (Query B)) psa ca -> A <> Query B -> 
  gen_step2 (osscamQ dual rules) A empty_relT drsa drsb psa ca psb cb.
Proof. intros rscr ctra anb.
apply fmlsrule_g_ex in ctra. cD.
apply gs_ossca_mQ_lem.
- eapply gs2_eq.  intro.  apply req_sym.  apply osscam_nn_eq.
eapply princ_paramL_nn_ne.
+ apply wcn_sing.
+ exact ctra1.
+ intros * ctrpc.  destruct ctrpc.
eexists. reflexivity.  intro ba.  exact (anb (eq_sym ba)).
+ exact rscr.

- apply gs_osscaQ_lem. intros. subst.
apply gs_osscang_Q_lem.  apply gs_osscan_g_lem.
intro n.  apply gs2_osscann_n.
eapply princ_paramL_nn_ne.
+ apply wcn_sing.
+ exact ctra1.
+ intros * ctrpc.  destruct ctrpc.
eexists. reflexivity.  intro ba.  exact (anb (eq_sym ba)).
+ exact rscr.

- apply gs_osscaQ'_lem. intros. subst.
apply gs_osscang_Q'_lem.  apply gs_osscan_g_lem.
intro n.  apply gs2_osscann_n.
apply gs2_osscann_dual_e'.
eapply princ_paramL_nn_ne.
+ apply wcn_sing.
+ exact ctra1.
+ intros * ctrpc.  destruct ctrpc.
eexists. reflexivity. simpl. rewrite dual_dual.
intro ba.  exact (anb (eq_sym ba)).
+ exact rscr.
Qed.

Check wcn_neq_paramL.

Lemma Q_or_not {V} A : {A' : _ & A = @Query V A'} + forall A', A <> @Query V A'.
destruct A.
12 : left ; eexists ; reflexivity.
all: right ; intros A' H ; inversion H. Qed.

Axiom fml_eq_or_not : forall {V} (A : LLfml V), forall B, (A = B) + (A <> B).

Lemma gs2_wcn_Q V (A B : LLfml V) ncw rules any drsa drsb psa psb ca cb :
  rsub (fmlsruleg (wcnrule ncw (Query B))) rules ->
  fmlsruleg (wcnrule ncw (Query B)) psa ca ->
  gen_step2 (osscamQ dual rules) A any drsa drsb psa ca psb cb.
Proof. intros rswr fwa.
pose (fml_eq_or_not A (Query B)). sD.
+ subst.  apply gen_step2_empty.
apply gs2_ng_mQ. exact (gs_wcn_ng _ _ _ rswr fwa).
(* where cut-formula is different from formula that is conclusion of rule,
must be a parametric case *)
+ apply (gen_step2_sub_mono (rsub_emptyT _)).
exact (wcn_neq_paramL _ _ rswr fwa s).
Qed.

Lemma gs2_wc_Q V (A B : LLfml V) ncw wcrule
  (wcreq : req (wcrule (Query B)) (wcnrule ncw (Query B)))
  rules any drsa drsb psa psb ca cb :
  rsub (fmlsruleg (wcrule (Query B))) rules ->
  fmlsruleg (wcrule (Query B)) psa ca ->
  gen_step2 (osscamQ dual rules) A any drsa drsb psa ca psb cb.
Proof. intros rs fra. eapply gs2_wcn_Q.
eapply rsub_trans. 2: exact rs.
apply fmlsruleg_mono.  exact (snd wcreq).
revert fra.  apply (fmlsruleg_mono (fst wcreq)). Qed.

Definition gs2_wk_Q V (A B : LLfml V) := @gs2_wc_Q V A B _ _ (wk_wcn _).
Definition gs2_ctr_Q V (A B : LLfml V) := @gs2_wc_Q V A B _ _ (ctr_wcn _).

Check gs2_ctr_Q.  Check gs2_wk_Q.
  
(* cut-formula Query, mall_rules on the right *)
Lemma gs2_Query_mall_Q V A rules drsl psl psr cl cr  
  (rsr : rsub mall_rules rules) : @mall_rules V psr cr ->
  gen_step2 (osscamQ dual rules) (Query A) empty_relT drsl 
    (derrec rules emptyT) psl cl psr cr.
Proof. intro mr. apply gs2_ng_mQ. apply gs_osscan_g_lem.
intro n.  apply gs2_osscan_lem. intros. subst.
inversion mr ; subst.
- apply fmlsrule_g_ex in X. cD. destruct X.
+ (* no left context, so principal formula should be Bang *)
inversion X1. unfold fmlsext in H1. simpl in H1.
destruct X as [ psb cb rb|psb cb rb|psb cb rb|psb cb rb|psb cb rb|psb cb rb] ; 
(* following gets all cases of cut where formulae not duals *)
(destruct rb ; simpl in H1 ; inversion H1).
+ eapply princ_paramR_n_e. apply llprinc_sing. exact X1. 
exact (rsub_trans (rsubI _ _ princ_mallI) rsr).
- (* merge_ctxtg Tensrule on right *)
inversion X. destruct cl. subst.
+ (* no left context, so principal formula should be Bang *)
inversion X0. destruct X1. inversion H.
+ eapply merge_paramR_n_e.  apply tens_sing. exact X0.
exact (rsub_trans (rsubI _ _ tens_mallI) rsr).
- inversion X.  - inversion X.  - inversion X. Qed.

Print Implicit gs2_Query_mall_Q.

Lemma gs2_osscan0_Bang V A drsr psl cl cr :
  gen_step2 (osscan dual maell_rules 0) (Query (dual A)) empty_relT
    (derrec maell_rules emptyT) drsr psl cl [A :: map (@Query V) cr]
    (Bang A :: map (@Query V) cr).
Proof.  unfold gen_step2. intros saa fpl fpr dl dr. clear saa fpl fpr dr.
apply osscanI. intros * cle cre mrg. 
inversion cre. simpl in cle. subst. clear H0 cre.
eapply derl_derrec_trans.
eapply merge_wk in mrg.
revert mrg. apply derl_mono.
apply (rsubI _ _ wkq_maell).
intros q inq. apply InT_mapE in inq.  cD. subst. 
apply rsubI.  apply wkqrules_I.
exact (dersrec_singleI dl). Qed.

Lemma gs2_Bangrule_mall_Q V A drsl psl psr cl cr : @mall_rules V psr cr ->
  fmlsrulegq (@Query V) Bangrule psl cl -> 
  gen_step2 (osscamQ dual maell_rules) A empty_relT drsl
    (derrec maell_rules emptyT) psl cl psr cr.
Proof. intros mr fbl. inversion fbl. subst.
apply gs2_osscamQ_lem ; intros * cle cre. 
destruct cl0. 
- (* no left context, so cut-formula is Bang or Query *)
unfold fmlsext. simpl. destruct X.
unfold fmlsext in cle. simpl in cle. destruct cle.
-- inversion e. (* cut formula is Bang *)
apply gs2_osscamQ_dual_e'. (* now cut formula is Query, mall rules on left *)
simpl. clear A' cre e fbl H0 H1 ls rs.
apply gs2_ng_mQ.  apply gs_osscang_l_lem. intro n.
destruct mr.
++ (* llprinc, parametric as different formula *)
apply gs_osscan_gl_lem. intros m l. clear l.
destruct m.  apply gs2_osscan0_Bang.  apply gs2_osscann_n.
apply (princ_paramL_nn_ne' _ _ _ llprinc_sing f).
(* prove llprinc ps0 c0 -> {c' : LLfml V & c0 = [c'] & c' <> Query (dual A0)}
  justifies separate lemma ?? *)
intros * llp. 
destruct llp as [psa ca ra|psa ca ra|psa ca ra|psa ca ra|psa ca ra|psa ca ra] ; 
(destruct ra ; eexists ; [ reflexivity | intro eqq ; inversion eqq ]).
exact (rsub_trans (rsubI _ _ princ_mallI) (rsubI _ _ mall_maellI)).

++ (* merge_ctxtg Tensrule, parametric as different formula *)
destruct m.  eapply merge_paramL_ngl_QT.  
exact (rsubI _ _ bang_sing).  exact m.

eapply OSctxt_eq.  * apply Bangrule_I.  * reflexivity.
* reflexivity.  * exact ctrq_maell.  * exact tens_maellI.

++ (* Onerule *) destruct o.
apply gs_osscan_gl_lem. intros m lmn.
destruct m. apply gs2_osscan0_Bang.
apply gs2_osscan_lem.  intros * cle.
simpl in cle. inversion cle.

++ (* Idrule *) destruct i.
apply gs_osscan_gl_lem. intros m lmn.
destruct m. apply gs2_osscan0_Bang.
apply gs2_osscan_lem.  intros * cle.
simpl in cle. inversion cle.

++ (* Idrule *) destruct i.
apply gs_osscan_gl_lem. intros m lmn.
destruct m. apply gs2_osscan0_Bang.
apply gs2_osscan_lem.  intros * cle.
simpl in cle. inversion cle.

-- subst.  exact (gs2_Query_mall_Q _ (rsubI _ _ mall_maellI) mr).
- (* some left context to Bang rule, so cut-formula must be Query *)
destruct cle.
+ unfold fmlsext in e. simpl in e. inversion e.
exact (gs2_Query_mall_Q _ (rsubI _ _ mall_maellI) mr).
+ subst.  exact (gs2_Query_mall_Q _ (rsubI _ _ mall_maellI) mr).
Qed.

Print Implicit gs2_Bangrule_mall_Q.

(* Bangrule on both sides *)
Lemma gs2_B_B_n V A rules any n drsl drsr psl psr cl cr
  (rsbr : rsub (fmlsrulegq (@Query V) Bangrule) rules)
  (fgql : fmlsrulegq (@Query V) Bangrule psl cl)
  (fgqr : fmlsrulegq (@Query V) Bangrule psr cr) :
  gen_step2 (osscan dual rules n) (Query A) any drsl drsr psl cl psr cr.
Proof.  apply gs2_osscan_lem. intros * cle cre.
destruct fgql.  destruct fgqr.  destruct b.  destruct b0. subst.
simpl in cre.
destruct cl0 ; simpl in cre ; unfold fmlsext in cre ; inversion cre.
subst. clear cre.

intros saa fpl fpr dl dr. clear saa fpr dl dr.
simpl in fpl. inversion fpl. clear X0. cD. subst. clear fpl X cle.
simpl in X0. simpl. unfold fmlsext in X0. unfold fmlsext. simpl in X0. simpl.

apply osscanI. intros * cle cre mrg.
simpl in cre. inversion cre. clear cre.
destruct X0.
acacD'T2 ; subst.
+ rewrite cle0 in d.  rewrite - app_assoc in d.  simpl in d. 
apply merge_ctns_singleL in mrg. cD. subst.
apply map_app_ex in cle0.  apply map_app_ex in mrg4.  cD. subst.
apply merge_map_exM in mrg3.  apply merge_map_exM in mrg6.  cD. subst.
eapply derI.  apply (rsubD rsbr).  eapply fmlsrulegq_I.
eapply Bangrule_I.  reflexivity.  reflexivity.  reflexivity. reflexivity. 
simpl. unfold fmlsext. simpl.
epose (d _ _ _ eq_refl eq_refl). apply dersrec_singleI. apply d0.
clear d d0.  rewrite !map_app.  apply merge_app.  apply (merge_map _ mrg8).
apply mergeLI.  apply (merge_map _ mrg0).
+ rewrite app_nil_r in cle0. rewrite cle0 in d.  simpl in d.
apply merge_consL in mrg. cD. subst.
apply map_app_ex in mrg3.  cD. subst.
apply merge_map_exM in mrg2.  cD. subst.
eapply derI.  apply (rsubD rsbr).  eapply fmlsrulegq_I.
eapply Bangrule_I.  reflexivity.  reflexivity.  reflexivity. reflexivity. 
simpl. unfold fmlsext. simpl.
epose (d _ _ _ eq_refl eq_refl). apply dersrec_singleI. apply d0.
clear d d0.  rewrite !map_app.
apply (merge_app (merge_Lnil _)).  apply mergeLI.  apply (merge_map _ mrg0).
+ clear d.  pose (repeat_spec n (Query A) (Bang A0)).  rewrite -> cle0 in e.
require e. apply in_or_app. (* this uses In not InT *)
right. simpl. tauto. inversion e. Qed.

Lemma gs2_B_B V A rules any drsl drsr psl psr cl cr
  (rsbr : rsub (fmlsrulegq (@Query V) Bangrule) rules)
  (fgql : fmlsrulegq (@Query V) Bangrule psl cl)
  (fgqr : fmlsrulegq (@Query V) Bangrule psr cr) :
  gen_step2 (osscamQ dual rules) A any drsl drsr psl cl psr cr.
Proof.  apply gs2_osscamQ_lem. intros * cle cre.
assert ({ B : _ & (A = Query B) + (A = Bang B) }).
{ destruct cle.  destruct fgql.  destruct b.
unfold fmlsext in e3.  destruct mcl ; simpl in e3.
subst. inversion e. subst. exists A0. tauto.
destruct cl ; simpl in e0 ; inversion e0.
subst. inversion e. subst. exists l0. tauto.
subst. exists A'. tauto. }
clear cle cre.  apply (gen_step2_sub_mono (rsub_emptyT _)).  sD.
+ subst.  apply gs2_ng_mQ.  apply gs_osscan_g_lem.
intro n.  exact (gs2_B_B_n _ _ _ rsbr fgql fgqr).
+ subst.  apply (gen_step2_sub_mono (rsub_emptyT _)).
apply gs2_osscamQ_dual_e'. simpl.
apply gs2_ng_mQ.  apply gs_osscan_g_lem.
intro n.  exact (gs2_B_B_n _ _ _ rsbr fgqr fgql).
Qed.

Print Implicit gs2_B_B.

Lemma hs2_Bangrule_maell_Q V A
  cl (dl : derrec maell_rules emptyT cl)
  cr (dr : derrec maell_rules emptyT cr) 
  psl (brl : botRule_fc (fcI dl) psl cl)  
  psr (brr : botRule_fc (fcI dr) psr cr) :
  @maell_rules V psr cr -> fmlsrulegq (@Query V) Bangrule psl cl -> 
  height_step2_tr (dt2fun (osscamQ dual maell_rules))
    A isubfml (fcI dl) (fcI dr).
Proof.  intros mr fgql. destruct mr.
- (* mall_rules *)
apply (gs2_hs2 brl brr).  apply (gen_step2_sub_mono (rsub_emptyT _)).
exact (gs2_Bangrule_mall_Q _ m fgql).
- (* wkrule *)
apply (gs2_hs2 brl brr).  apply gs2_osscamQ_dual'.
eapply gs2_wk_Q.  apply (rsubI _ _ (@wk_maellI _ _)). eassumption.
- (* ctrrule *)
apply (gs2_hs2 brl brr).  apply gs2_osscamQ_dual'.
eapply gs2_ctr_Q.  apply (rsubI _ _ (@ctr_maellI _ _)). eassumption.

- (* Queryrule *)
destruct fgql. destruct cl ; simpl in e.
+ (* no left context for Bang rule, cut form is Bang _ or Query _ *)
unfold fmlsext in e2. subst mcl. simpl in e2.
apply (hs2_osscamQ_lem brl brr).  intros * cle cre. subst.
destruct b. simpl in cle.
simpl in brl. unfold fmlsext in brl. simpl in brl. simpl in dl.
destruct cle.
++ inversion e. (* cut formula is Bang *)
subst. clear e cre.
apply hs2_osscamQ_dual'. simpl.
eapply (query_bang_mQ_ht _ brr brl f).
eapply OSctxt_eq.  apply Bangrule_I.  reflexivity.  reflexivity.

++ (* cut formula is Query, Query rule on right must be parametric *)
(* TODO - this is duplicated below, in gs2_Query_maell_Q *)
clear cre. subst.
apply (gs2_hs2 brl brr). 
apply (gen_step2_sub_mono (rsub_emptyT _)).
apply gs2_ng_mQ.  apply gs_osscan_g_lem. intro n.
apply gs2_osscann_n.  apply gs2_osscann_dual_e'.
apply (princ_paramL_nn_ne' _ _ _ (rsubI _ _ query_sing) f).
intros * qpc. destruct qpc. eexists. reflexivity.
simpl. intro qb. inversion qb.
exact (rsubI _ _ query_maellI).

+ (* non-trivial left context for Bang rule 
so cut formula must be Query, so head formula on right is Bang,
whereas rule on right is Query, so parametric *)
apply (gs2_hs2 brl brr).
apply gs2_osscamQ_lem. intros * cle cre.
pose (Q_or_not A). destruct s. cD. subst A.
destruct cre. 2: inversion e3. simpl in e3.
apply (gen_step2_sub_mono (rsub_emptyT _)).
apply gs2_ng_mQ.  apply gs_osscan_g_lem. intro n.
apply gs2_osscann_n.  apply gs2_osscann_dual_e'.
apply (princ_paramL_nn_ne' _ _ _ (rsubI _ _ query_sing) f).
intros * qpc. destruct qpc. eexists. reflexivity.
simpl. intro qb. inversion qb.
exact (rsubI _ _ query_maellI).
(* cut-formula not Query - contradiction *)
subst. unfold fmlsext in cle. simpl in cle. destruct cle.
inversion e. subst. destruct (n l eq_refl).
subst. destruct (n _ eq_refl).

- (* Bangrule on both sides, one must be parametric *)
apply (gs2_hs2 brl brr).
exact (gs2_B_B _ _ _ (rsubI _ _ bang_maellI) fgql f).
Qed.

Print Implicit hs2_Bangrule_maell_Q.

Lemma hs2_Query_maell_Q V A psl psr cl cr 
  (ml : @maell_rules V psl cl) (mr : @maell_rules V psr cr)
  (dl : derrec maell_rules emptyT cl) (dr : derrec maell_rules emptyT cr) 
  (brl : botRule_fc (fcI dl) psl cl)  (brr : botRule_fc (fcI dr) psr cr) :
  height_step2_tr (dt2fun (osscamQ dual maell_rules))
    (@Query V A) isubfml (fcI dl) (fcI dr).
Proof.
pose (rsub_id (@maell_rules V)) as rsr. (* rsr was rsub maell_rules rules *)
inversion mr ; subst.
- (* mall_rules *)
apply (gs2_hs2 brl brr).
apply (gen_step2_sub_mono (rsub_emptyT _)).
exact (gs2_Query_mall_Q _ (rsub_trans (rsubI _ _ mall_maellI) rsr) X).
- (* wkrule *)
apply (gs2_hs2 brl brr).
apply gs2_osscamQ_dual'.  eapply gs2_wk_Q.
apply (rsub_trans (rsubI _ _ (@wk_maellI _ _)) rsr). eassumption.
- (* ctrrule *)
apply (gs2_hs2 brl brr).
apply gs2_osscamQ_dual'.  eapply gs2_ctr_Q.
apply (rsub_trans (rsubI _ _ (@ctr_maellI _ _)) rsr). eassumption.
- (* Queryrule - must be parametric *)
apply (gs2_hs2 brl brr).
apply (gen_step2_sub_mono (rsub_emptyT _)).
apply gs2_ng_mQ.  apply gs_osscan_g_lem. intro n.
apply gs2_osscann_n.  apply gs2_osscann_dual_e'.
apply (princ_paramL_nn_ne' _ _ _ (rsubI _ _ query_sing) X).
intros * qpc. destruct qpc. eexists. reflexivity.
simpl. intro qb. inversion qb.
exact (rsub_trans (rsubI _ _ query_maellI) rsr).
- (* Bangrule *)
apply hs2_osscamQ_dual'.
eapply hs2_Bangrule_maell_Q ; eassumption. (* ml used here only *)
Qed.

Print Implicit hs2_Query_maell_Q.

(* cut-formula Query, mall_rules on the left *)
(*
Lemma gs2_Query_mall_l_Q V A rules drsl psl psr cl cr  
  (rsr : rsub mall_rules rules) : @mall_rules V psl cl ->
  gen_step2 (osscamQ dual rules) (Query A) empty_relT drsl 
    (derrec rules emptyT) psl cl psr cr.
Proof. intro ml. apply gs2_ng_mQ. apply gs_osscan_g_lem.
intro n.  apply gs2_osscan_lem. intros. subst.
inversion ml ; subst.
*)

Lemma gs2_Q_nQ V A psl psr cl cr (X0 : fmlsruleg Queryrule psl cl) 
  (s : forall A', A <> @Query V A') :
  gen_step2 (osscamQ dual maell_rules) A isubfml (derrec maell_rules emptyT)
  (derrec maell_rules emptyT) psl cl psr cr.
Proof.  apply fmlsrule_g_ex in X0. cD. destruct X0.
* inversion X2. destruct X.  unfold fmlsext. simpl. clear X2.
apply gs2_osscamQ_lem. intros * aq. destruct aq ; subst.
inversion e. subst. destruct (s  _ eq_refl).
destruct (s  _ eq_refl).
* apply gs_ossca_mQ_lem.
** exact (princ_paramL _ (rsubI _ _ query_sing) X2 (rsubI _ _ query_maellI)).
** apply gs_osscaQ_lem. intros A' ae.
destruct (s _ ae).
** apply (gen_step2_sub_mono (rsub_emptyT _)).
apply gs_osscaQ'_lem.  intros * ae * cle. subst.
apply gs_osscang_Q'_lem. clear s.
apply gs_osscan_g_lem. intro n.
exact (princ_paramR_n_e _ _ (rsubI _ _ query_sing) X2 (rsubI _ _ query_maellI)).
Qed.

Lemma hs2_maell_Q V (A : LLfml V)
  (adm_exch : forall (seq seq' : list (LLfml V)),
    swapped seq' seq -> adm maell_rules [seq'] seq) 
  cl (dl : derrec maell_rules emptyT cl)
  cr (dr : derrec maell_rules emptyT cr) 
  psl (brl : botRule_fc (fcI dl) psl cl)  
  psr (brr : botRule_fc (fcI dr) psr cr) :
  maell_rules psl cl -> maell_rules psr cr -> 
  height_step2_tr (dt2fun (osscamQ dual maell_rules)) 
    A isubfml (fcI dl) (fcI dr).
Proof. intros ma mb. inversion mb ; subst. 
- inversion ma ; subst.
apply (gs2_hs2 brl brr).
+ apply gs_ossca_mQ_lem. 
* exact (gs_mall' (rsubI _ _ mall_maellI) adm_exch X0 X).
* exact (gs_mall_q _ _ (rsubI _ _ mall_maellI) adm_exch X).
* apply (gen_step2_sub_mono (rsub_emptyT _)).
  exact (gs_mall_q' _ (rsubI _ _ mall_maellI) adm_exch X0).
(* will want to do the same for other cases of wkrule, ctrrule *)
+ (* wkrule *) 
apply (gs2_hs2 brl brr).
eapply gs2_wk_Q.  apply (rsubI _ _ (@wk_maellI _ _)). eassumption.
+ (* ctrrule *) 
apply (gs2_hs2 brl brr).
eapply gs2_ctr_Q.  apply (rsubI _ _ (@ctr_maellI _ _)). eassumption.
+ (* Queryrule *) 
apply (gs2_hs2 brl brr).
pose (Q_or_not A). sD. 
++ subst.  apply (gen_step2_sub_mono (rsub_emptyT _)).
exact (gs2_Query_mall_Q _ (rsubI _ _ mall_maellI) X).
++ exact (gs2_Q_nQ X0 s).

+ (* Bangrule *) 
apply (gs2_hs2 brl brr).
apply (gen_step2_sub_mono (rsub_emptyT _)).
exact (gs2_Bangrule_mall_Q _ X X0).

- (* wkrule on right *)
apply (gs2_hs2 brl brr).
apply gs2_osscamQ_dual'.
eapply gs2_wk_Q.  apply (rsubI _ _ (@wk_maellI _ _)). eassumption.

- (* ctrrule on right *)
apply (gs2_hs2 brl brr).
apply gs2_osscamQ_dual'.
eapply gs2_ctr_Q.  apply (rsubI _ _ (@ctr_maellI _ _)). eassumption.

- (* Queryrule on right *)
pose (Q_or_not (dual A)). sD. 
++ apply hs2_osscamQ_dual'. rewrite s0.
eapply hs2_Query_maell_Q ; eassumption.
++ apply (gs2_hs2 brl brr).
apply gs2_osscamQ_dual'.  exact (gs2_Q_nQ X s).

- (* Bangrule on right *)
apply hs2_osscamQ_dual'.
eapply hs2_Bangrule_maell_Q ; eassumption.
Qed.

Print Implicit hs2_maell_Q.

Theorem cut_adm_maell_Q {V} (A : LLfml V) :
  forall cl, derrec maell_rules emptyT cl ->
  forall cr, derrec maell_rules emptyT cr ->
  osscamQ dual maell_rules A cl cr.
Proof. intros cl dl cr dr.
assert (dt2fun (osscamQ dual maell_rules) A (fcI dl) (fcI dr)).
all: cycle 1.
unfold dt2fun in X. simpl in X.  rewrite !der_concl_eq in X. exact X.
apply (height_step2_tr_lem _ _ (AccT_isubfml A)).
intros. clear cl dl cr dr.  destruct dta.  destruct dtb.
apply (hs2_maell_Q adm_exch_maell (get_botrule _) (get_botrule _)
 (bot_is_rule _) (bot_is_rule _)).  Qed.

Print Implicit cut_adm_maell_Q.
