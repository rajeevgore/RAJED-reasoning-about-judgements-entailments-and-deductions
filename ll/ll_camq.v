
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
Require Import lldefs ll_lems ll_exch ll_cam.
Require Import gstep gentree.

Lemma merge_ctr_lem W rules prsl a
  (ar br pl pr H2 H4 mal mar mbl mbr mrg mrg0 mrg1 mrg2 : list W)
  (adm_exch : forall seq seq' : list W,
             swapped seq' seq -> adm rules [seq'] seq)
  (ctrm : forall q : W, InT q mrg + InT q mrg0 -> 
    rsub (fmlsruleg (ctrrule q)) rules) 
  (rsmr : rsub (merge_ctxtg prsl) rules)
  (X : prsl [pl; pr] [a])
  (d : derrec rules emptyT (mal ++ pl ++ mar))
  (mal0 : merge H4 mal mrg1) (mal1 : merge H2 mrg mal)
  (mar0 : merge br mar mrg2) (mar1 : merge ar mrg0 mar)
  (d0 : derrec rules emptyT (mbl ++ pr ++ mbr))
  (mbl0 : merge H2 mbl mrg1) (mbl1 : merge H4 mrg mbl)
  (mbr0 : merge ar mbr mrg2) (mbr1 : merge br mrg0 mbr) :
  derrec rules emptyT (mrg1 ++ [a] ++ mrg2).
Proof.  epose derI.  erequire d1.  erequire d1.  erequire d1.
erequire d1.  erequire d1.  require d1.
apply (rsubD rsmr).
eapply merge_ctxtgI.  eapply merge_ctxtI.  apply X.
apply merge_simple_app.  apply merge_simple_app.
require d1.  apply (dlCons d (dersrec_singleI d0)).
epose (merge_exch adm_exch mal1 (merge_simple_app _ _) [] _).
rewrite - app_assoc in d1.
pose (admDs a0 d1). simpl in d2.
epose (merge_exch adm_exch mbl1 (merge_simple_app _ _) _ _).
pose (admDs a1 d2). 
epose (merge_exch adm_exch mar1 (merge_simple_app _ _) 
  ((H2 ++ mrg) ++ (H4 ++ mrg) ++ [a]) mbr).
rewrite <- !app_assoc in a2. simpl in a2.
rewrite <- !app_assoc in d3. 
pose (admDs a2 d3). 
epose (merge_exch adm_exch mbr1 (merge_simple_app _ _) _ []).
rewrite -> app_comm_cons in d4. 
rewrite -> !app_assoc in d4.  rewrite -> !app_nil_r in a3.
pose (admDs a3 d4).  rewrite <- !app_assoc in d5.

(* now do contraction, need to get mrg and mrg0 are all Query *)
pose (@gen_ctr_adm _ _ mrg adm_exch) as gcam.
require gcam.  intros q iqm.  exact (ctrm q (inl iqm)).
specialize (gcam H2 H4 ((a :: ar) ++ mrg0 ++ br ++ mrg0)).
pose (admDs gcam d5).
pose (@gen_ctr_adm _ _ mrg0 adm_exch) as gcam0.
require gcam0.  intros q iqm.  exact (ctrm q (inr iqm)).
specialize (gcam0 (H2 ++ mrg ++ H4 ++ (a :: ar)) br []).
pose (admDs gcam0).
require d7. rewrite app_nil_r. rewrite - !app_assoc. exact d6.
rewrite app_nil_r in d7.

epose (merge_exch adm_exch (merge_simple_app _ _) mal1 [] _).
simpl in a4.  rewrite <- !app_assoc in d7.  rewrite <- !app_assoc in a4.
destruct a4.  specialize (d8 (dersrec_singleI d7)).
epose (merge_exch adm_exch (merge_simple_app _ _) (merge_sym mal0) [] _).
simpl in a4.  rewrite <- !app_assoc in a4.
destruct a4.  specialize (d9 (dersrec_singleI d8)).

rewrite cons_app_single in d9.
epose (merge_exch adm_exch (merge_simple_app _ _) (merge_sym mbr1) _ []).
rewrite -> !app_nil_r in a4.
rewrite -> !app_assoc in a4.  rewrite -> !app_assoc in d9.
destruct a4.  specialize (d10 (dersrec_singleI d9)).
epose (merge_exch adm_exch (merge_simple_app _ _) mbr0 _ []).
rewrite -> !app_nil_r in a4.  rewrite -> !app_assoc in a4. 
destruct a4.  specialize (d11 (dersrec_singleI d10)).
rewrite - app_assoc in d11.  exact d11.
Qed.

Print Implicit merge_ctr_lem.

(* according to Dirk Roorda's thesis, shouldn't need this in general
  but do need revised version, rh rule is principal Bangrule
  dual and isubfml are generic *)
Lemma merge_paramL_ngl V (A : LLfml V) rules dual n any prsl prsr xs ys zs
  drsb psa psb ca cb 
  (adm_exch : forall seq seq', swapped seq' seq -> adm rules [seq'] seq) :
  rsub prsl (fun _ => sing) -> rsub prsr (fun _ => sing) ->
  merge_ctxt xs ys prsl psa ca -> leT n (length xs) ->
  fmlsrule [] (map (@Query V) zs) prsr psb cb -> 
  rsub (fmlsruleg ctrqrules) rules -> rsub (merge_ctxtg prsl) rules -> 
  gen_step2 (osscangl dual rules n) (Query A) any (derrec rules emptyT)
    drsb psa ca psb cb.
Proof. intros pls prs mcp lxs mqr rsq rsmr. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpr.
clear dl dr. 
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

(* cut with lh premise of merging rule *)
inversion fpl. subst. cD. clear X0.  destruct X2.
specialize (o H5 (leT_trans (leT_plus_l _ _) H)).
pose (merge_assoc mrg3 (merge_sym H8)) as mal. cD.
pose (merge_assoc mrg6 (merge_sym H1)) as mar. cD.
destruct o. rewrite <- !app_assoc in d.
specialize (d _ _ (mal ++ pl ++ mar) eq_refl eq_refl).
require d.  apply (merge_app mal1).
pose (merge_app (merge_Rnil pl) mar1). simpl in m. exact m.

(* cut with rh premise of merging rule *)
inversion X1. subst. cD. clear X0 X1 X2. destruct X3.
specialize (o H7 (leT_trans (leT_plus_r _ _) H)).
pose (merge_assoc mrg3 H8) as mbl. cD.
pose (merge_assoc mrg6 H1) as mbr. cD.
destruct o. rewrite <- !app_assoc in d0.
specialize (d0 _ _ (mbl ++ pr ++ mbr) eq_refl eq_refl).
require d0.  apply (merge_app mbl1).
pose (merge_app (merge_Rnil pr) mbr1). simpl in m. exact m.

(* so now have the result of inductive cut with both premises,
  but applying rule to these will have context from rhs twice, 
  so will need to do contraction *)
clear fpl.
(* try separate lemma from here *)
eapply (merge_ctr_lem _ _ _ adm_exch _ rsmr X d
  mal0 mal1 mar0 mar1 d0 mbl0 mbl1 mbr0 mbr1).
Unshelve. 
(* now do contraction, need to get mrg and mrg0 are all Query *)
inversion mqr.
unfold fmlsext in H6. simpl in H6.
apply prs in X0. destruct X0. inversion H6.
apply map_app_ex in H10. cD. subst.
intros q inq2.  eapply (rsub_trans _ rsq).
Unshelve.
apply fmlsruleg_mono.
intros ps0 c0 cq.
destruct inq2 ; apply InT_mapE in i ; cD ; subst q ; exact (ctrqrules_I cq).
Qed.

Print Implicit merge_paramL_ngl.

Lemma merge_paramL_ngl_QT V (A : LLfml V) rules dual n any prsr xs ys zs
  drsb psa psb ca cb 
  (adm_exch : forall seq seq', swapped seq' seq -> adm rules [seq'] seq) :
  rsub prsr (fun _ => sing) ->
  merge_ctxt xs ys Tensrule psa ca -> 
  fmlsrule [] (map (@Query V) zs) prsr psb cb -> 
  rsub (fmlsruleg ctrqrules) rules -> rsub (merge_ctxtg Tensrule) rules -> 
  gen_step2 (osscangl dual rules n) (Query A) any (derrec rules emptyT)
    drsb psa ca psb cb.
Proof. intros prs mcp mqr rsq rsmr.
pose (leT_or_gt n (length xs)) as lg. destruct lg.
eapply (merge_paramL_ngl _ _ _ adm_exch (rsubI _ _ tens_sing)
  prs mcp l mqr rsq rsmr).
epose (merge_paramL_ngl _ _ _ adm_exch (rsubI _ _ tens_sing) 
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
destruct H. destruct H0.
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
destruct H. destruct H0.
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
destruct H. destruct H2.
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
inversion fqa.  inversion fbb. 
inversion H.  inversion H2.  subst.
unfold fmlsext. simpl.
apply osscamI. intros * qe be mrg. inversion qe. inversion be. subst.
simpl in H4. inversion H4. subst.
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


(* need version of query_bang_n_ht for mQ *)
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
inversion fbb.  destruct H1.  unfold fmlsext in H0. simpl in H0.
inversion H0. subst. clear H0.
simpl in H. unfold fmlsext in H. simpl in H.
pose (botr_ps_der d0).
(* rewrite <- H in d3. fails - why ?? *)
pose (eq_rect_r _ d3 H).  apply dersrec_singleD in d4.
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

Lemma query_bang_n_ht V (A : LLfml V) zs 
  (dta dtb : derrec_fc maell_rules emptyT) psa psb ca cb 
  (btra : botRule_fc dta psa ca) (btrb : botRule_fc dtb psb cb) :
  fmlsruleg Queryrule psa ca -> 
  fmlsrule [] (map (@Query V) zs) Bangrule psb cb -> 
  height_step2_tr (dt2fun (osscang dual maell_rules)) A isubfml dta dtb.

Proof. intros fqa fbb saa fpl fpr.  unfold dt2fun.
rewrite (botRule_fc_concl btra).  rewrite (botRule_fc_concl btrb).
destruct dta.  pose (botRule_fc_concl btra).
rewrite -> der_fc_concl_eq in e. subst.
destruct dtb.  pose (botRule_fc_concl btrb).
rewrite -> der_fc_concl_eq in e. subst.
pose (botRule_fc_prems btra). cD. subst. 
pose (botRule_fc_prems btrb). cD. subst. 
apply osscangI. intro n.
pose (fmlsrule_g_ex fqa) as fxy. cD.
pose (leT_or_gt n (length fxy)) as lg. destruct lg.

- (* parametric case *) 
(* would be simpler to use usenX above if it is valid, and gs_osscan_g_ht_lem *)
epose (princ_paramL_n _ (derrec maell_rules emptyT) (derrec maell_rules emptyT)
  (@query_sing _) fxy1 l (rsubI _ _ query_maellI)).
(* eapply gs2_gs2c in g. fails *)
epose (fst (gs2_gs2c _ _ _ d d0) g).
eapply gs2c_gs2tr in g0.  eapply gs2_tr_height in g0.
destruct g0. (* this does a lot! *)
+ intros A' aaa a b Aa Ab.  specialize (saa A' aaa a b Aa Ab).
unfold dt2fun in saa.  unfold dt2fun.  destruct saa. exact (o n).
+ intros dtp m.  specialize (fpl dtp m).
unfold dt2fun in fpl.  unfold dt2fun.  destruct fpl. exact (o n).
+ intros dtq m.  specialize (fpr dtq m).
unfold dt2fun in fpr.  unfold dt2fun.  destruct fpr. exact (o n).
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
clear p p0.
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
pose (@exch_maell_ht _ _ d1 (repeat (Query A0) (cae0 + cae3) ++ A0 :: ls)).
require s. subst.  rewrite repeat_add. swap_tac_Rc. cD.
(* now induction on height of derivation, as height <= left derivation *)
specialize (fpl (fcI s)).  require fpl.
eapply PeanoNat.Nat.lt_le_trans.
2: apply X. simpl. apply Lt.le_lt_n_Sm. exact s0.
clear fqa btra.  destruct fpl.  specialize (o (Nat.add cae0 cae3)).
destruct o.  rewrite !der_fc_concl_eq in d2.
specialize (d2 _ _ _ eq_refl eq_refl (mergeLI A0 mrg)).
(* now induction on the formula using d2 and nextup of d0 *)
specialize (saa A0 (isub_Query A0) (fcI d2)).
inversion fbb.  destruct H1.  unfold fmlsext in H0. simpl in H0.
inversion H0. subst. clear H0.
simpl in H. unfold fmlsext in H. simpl in H.
pose (botr_ps_der d0).
(* rewrite <- H in d3. fails - why ?? *)
pose (eq_rect_r _ d3 H).  apply dersrec_singleD in d4.
specialize (saa (fcI d4) (AccT_measure _ _) (AccT_measure _ _)).
destruct saa.  specialize (o 1).  rewrite !der_fc_concl_eq in o.
destruct o. simpl in d5.
epose (merge_doubles_via_der mrg) as mrgd. cD.
require mrgd. intros q inmq.  apply InT_mapE in inmq. cD. subst.
apply rsubI.  apply ctrqrules_I.
cD.  specialize (d5 _ _ _ eq_refl eq_refl mrgd2).
apply (derl_mono ctrq_maell) in mrgd1.
exact (derl_derrec_trans mrgd1 (dersrec_singleI d5)).
Qed.

Print Implicit query_bang_n_ht.

(* this proof doesn't work
Proof. intros fqa fbb. apply gs_osscan_g_ht_or_lem. intro n.
destruct dta.  pose (botRule_fc_concl btra).
rewrite -> der_fc_concl_eq in e. subst.
destruct dtb.  pose (botRule_fc_concl btrb).
rewrite -> der_fc_concl_eq in e. subst.
pose (botRule_fc_prems btra). cD. subst. 
pose (botRule_fc_prems btrb). cD. subst. 
pose (fmlsrule_g_ex fqa) as fxy. cD.
pose (leT_or_gt n (length fxy)) as lg. destruct lg.
- (* parametric case *) left.
epose (princ_paramL_n _ (derrec maell_rules emptyT) (derrec maell_rules emptyT)
  (@query_sing _) fxy1 l (rsubI _ _ query_maellI)).
(* eapply gs2_gs2c in g. fails *)
epose (fst (gs2_gs2c _ _ _ d d0) g).
eapply gs2c_gs2tr in g0.  eapply gs2_tr_height in g0. exact g0.

- (* two parametric cases, excluded by n > length fxy, and principal case *)
right. intros saa fpl fpr.  unfold dt2fun.
rewrite (botRule_fc_concl btra).  rewrite (botRule_fc_concl btrb).

destruct fxy1. destruct q. unfold fmlsext. simpl.
apply osscangI. intro n. (* this doesn't work because we already have n,
  and we don't want a different one because of  condition l *)
  apply osscanI. intros * cae cbe mrg.
acacD'T2 ; subst.
*)

(*

Lemma query_bang_n V (A : LLfml V) zs drsb psa psb ca cb :
  fmlsruleg Queryrule psa ca -> fmlsrule [] zs Bangrule psb cb -> 
  gen_step2 (osscang dual maell_rules) A isubfml (derrec maell_rules emptyT)
    drsb psa ca psb cb.
Proof. intros fqa fbb saa fpl fpr da db.  split. intro n.
pose (fmlsrule_g_ex fqa) as fxy. cD.
pose (leT_or_gt n (length fxy)) as lg. destruct lg.
- (* parametric case *) (* next step unfolds gen_step2 *)
eapply (princ_paramL_n _ _ drsb (@query_sing _) fxy1 l).
+ exact (rsubI _ _ query_maellI).
+ intros A' aaa dl dls dr drs.  specialize (saa A' aaa dl dls dr drs).
destruct saa.  exact (o n).
+ fpxtac'' fpl.  destruct (snd fpxa). exact (o n).
+ fpxtac'' fpr.  destruct (snd fpxa). exact (o n).
+ exact da.  + exact db.
  
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
simpl in fpl.  unfold fmlsext in fpl.  simpl in fpl.
inversion fpl. clear fpl X0. destruct X. clear d.
(* exchange to get ?A0 to the right *)
apply (@adm_exch_maell_d _ 
  (repeat (Query A0) cae0 ++ repeat (Query A0) cae3 ++ A0 :: ls)) in d.
2: swap_tac_Rc.
rewrite app_assoc in d.
rewrite <- repeat_add in d.
(* PROBLEM - need to exchange before applying IH *)
what to do?  A different inductive principle?  Try
(1) cut of Query for any smaller n?  (2) cut of any exchanged version?
(3) height preserving exchange?

(1) would be complicated - need to do it twice, for cae0 and cae3, then
would need to contract context on rhs,
not clear whether you could use existing results for a simpler 
inductive principle (probably, but conplex)
(2) likewise, proving different property by induction, unlikely to be
able to reuse existing results
(3) seems better, since we have height-preserving exchange,
and the following - can we adapt existing results to use height_step2_tr_lem.?
*)

(* this will require repeat contraction 
Lemma gs_idL_q V (A B : LLfml V) rules any psa psb ca cb 
  (adm_exch : forall (seq seq' : list (LLfml V)),
    swapped seq' seq -> adm rules [seq'] seq) :
  Idrule B psa ca -> 
  gen_step2 (osscamq dual rules) A any (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb.
	*) 
(* doesn't work for cut-formula Query _ *)
Lemma gs_idL_q V (A B : LLfml V) any drsa psa psb ca cb 
  (adm_exch : forall (seq seq' : list (LLfml V)),
    swapped seq' seq -> adm maell_rules [seq'] seq) :
  (forall A', A <> Query A') -> Idrule B psa ca -> 
  gen_step2 (osscamq dual maell_rules) A any drsa
         (derrec maell_rules emptyT) psa ca psb cb.
Proof. intros nq id. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpl fpr dl.  split.
- apply osscamI. intros. subst.
inversion id. subst. clear id.
apply merge_singleL in H1. cD. subst.
erequire adm_exch.  erequire adm_exch.  require adm_exch.
all: cycle 1. destruct adm_exch. apply d.
exact (dersrec_singleI dr).  swap_tac_Rc. 
- repeat split ; intros A' ae * cae cbe mrg.
+ specialize (nq A' ae). inversion nq.
+ pose (f_equal dual ae). rewrite -> dual_dual in e.  simpl in e.
subst. clear ae nq.  simpl in dr.  rewrite -> dual_dual in dr.  
inversion id. simpl in H2.  rewrite -> dual_dual in H2. subst.
apply merge_singleR in mrg. cD. subst.
specialize (adm_exch (mrg ++ [Query A'] ++ mrg0) ([Query A'] ++ mrg ++ mrg0)).
destruct adm_exch. swap_tac.
apply d. clear d.  apply dersrec_singleI.
apply derrec_derl_deriv.  eapply derI.
apply (rsubD (@maell_gen_wk_ctr _ A')).
eapply (OSgctxt_eq _ _ _ []) ; split.
simpl. apply dersrec_singleI.  unfold fmlsext. simpl.
exact (derrec_rmono (rsub_derl _) dr).
Qed.

(* could change dual A <> Query A' to A <> Bang A' *)
Definition gs_idR_q' V A B drsb psa psb ca cb ae nq rlb :=
  gs2_osscamq_dual' (@gs_idL_q V (dual A) B _ drsb psb psa cb ca ae nq rlb).

Check gs_idL_q.  Check gs_idR_q'. 

(* rule on right is Onerule *)
Lemma gs_maell_one V (A : LLfml V) rules psa psb ca cb
  (rs : rsub maell_rules rules) 
  (adm_exch : forall seq seq' : list (LLfml V),
             swapped seq' seq -> adm rules [seq'] seq)
  (ma : maell_rules psa ca) (mb : Onerule psb cb) :
  gen_step2 (osscam dual rules) A isubfml (derrec rules emptyT)
    (derrec rules emptyT) psa ca psb cb.
Proof. inversion mb. subst.  apply gs_osscam_lem.
intros * e cbe. inversion cbe.
apply (f_equal dual) in H0. simpl in H0.
rewrite -> dual_dual in H0. subst A. clear cbe H1.
destruct ma.
- exact (gs_mall_one' (rsub_trans (rsubI _ _ mall_maellI) rs) adm_exch m mb).
- destruct f. unfold fmlsext in e. destruct Φ1 ; simpl in e.
+ destruct w. inversion e.
+ exact (princ_paramL _ (@wk_sing _ _) (OSctxt _ _ _ _ _ w)
    (rsub_trans (rsubI _ _ (@wk_maellI _ _)) rs)).
- destruct f. unfold fmlsext in e. destruct Φ1 ; simpl in e.
+ destruct c0. inversion e.
+ exact (princ_paramL _ (@ctr_sing _ _) (OSctxt _ _ _ _ _ c0)
    (rsub_trans (rsubI _ _ (@ctr_maellI _ _)) rs)).
- destruct f. unfold fmlsext in e. destruct Φ1 ; simpl in e.
+ destruct q. inversion e.
+ exact (princ_paramL _ (@query_sing _) (OSctxt _ _ _ _ _ q)
    (rsub_trans (rsubI _ _ (@query_maellI _)) rs)).
- destruct f. unfold fmlsext in e3. destruct b.
  destruct cl ; simpl in e0 ; subst ; inversion e.
Qed.

Definition gs_one_maell V A rules psa psb ca cb rs ae ma mb :=
  gs2_osscam_dual' 
    (@gs_maell_one V (dual A) rules psb psa cb ca rs ae mb ma).

Check gs_maell_one.  Check gs_one_maell.
 
Lemma gs_maell_one_q' V (A : LLfml V) rules psa psb ca cb
  (rs : rsub maell_rules rules) 
  (adm_exch : forall seq seq' : list (LLfml V),
             swapped seq' seq -> adm rules [seq'] seq)
  (ma : maell_rules psa ca) (mb : Onerule psb cb) :
  (forall A' : LLfml V, A <> Bang A') ->
  gen_step2 (osscamq dual rules) A isubfml (derrec rules emptyT)
    (derrec rules emptyT) psa ca psb cb.
Proof. intro nb. apply gs_osscamq_lem. intros * cae cbe.
inversion mb. subst.  destruct cbe.
inversion e.  apply (f_equal dual) in H0. simpl in H0.
rewrite -> dual_dual in H0. subst. clear e.
simpl in cae.  destruct cae. 2: inversion e.
2: specialize (nb A' e) ; inversion nb.
simpl. simpl in nb. apply (gs_osscam_q_lem nb).
intros * nq. inversion nq.
apply (gs_maell_one rs adm_exch ma mb).
Qed.

Definition gs_one_maell_q' V A rules psa psb ca cb rs ae ma mb nb :=
  gs2_osscamq_dual' 
    (@gs_maell_one_q' V (dual A) rules psb psa cb ca rs ae mb ma nb).

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
* destruct H1. inversion H.
* exact (princ_paramR (@query_sing _) (OSctxt _ _ _ _ _ H1)
    (rsub_trans (rsubI _ _ (@query_maellI _)) rs)).
+ inversion X. subst. destruct cl ; destruct H ; inversion H3.
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
+ inversion X0. destruct H0. inversion H. 
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

Lemma gs_ctr_ng W (A : W) rules dual any drsa drsb psa psb ca cb :
  rsub (fmlsruleg (ctrrule A)) rules -> fmlsruleg (ctrrule A) psa ca ->
  gen_step2 (osscang dual rules) A any drsa drsb psa ca psb cb.
Proof. intros rsfw fwa saa fpl fpr da db.  split. intro n.
pose (fmlsrule_g_ex fwa) as fxy. cD. clear fwa.
pose (leT_or_gt n (length fxy)) as lg. destruct lg.
- (* parametric case *) (* next step unfolds gen_step2 *)
  eapply (princ_paramL_n any drsa drsb (@ctr_sing _ _) fxy1 l rsfw).
+ intros A' aaa dl dls dr drs.  specialize (saa A' aaa dl dls dr drs).
destruct saa.  exact (o n).
+ fpxtac'' fpl.  destruct (snd fpxa). exact (o n).
+ fpxtac'' fpr.  destruct (snd fpxa). exact (o n).
+ exact da.  + exact db.
- (* two parametric cases, excluded by n > length fxy, and principal case *)
clear fpr saa.
destruct fxy1. destruct c0. unfold fmlsext. simpl.
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
inversion fpl. clear fpl X0. destruct X.
inversion o.  specialize (X (S (S (Nat.add cae0 cae3)))).  inversion X.
simpl in X0. rewrite -> repeat_add in X0.
specialize (X0 ls rs ms).
require X0.  list_assoc_l.  apply (f_equal (fun a => a ++ ls)).
clear X X0 o da d H0 l.
induction cae0 ; simpl. reflexivity.
exact (f_equal (cons A) IHcae0).
exact (X0 eq_refl mrg). Qed.

Lemma gs_wk_ng W (A : W) rules dual any drsa drsb psa psb ca cb :
  rsub (fmlsruleg (wkrule A)) rules -> fmlsruleg (wkrule A) psa ca ->
  gen_step2 (osscang dual rules) A any drsa drsb psa ca psb cb.
Proof. intros rsfw fwa saa fpl fpr da db.  split. intro n.
pose (fmlsrule_g_ex fwa) as fxy. cD. clear fwa.
pose (leT_or_gt n (length fxy)) as lg. destruct lg.
- (* parametric case *) (* next step unfolds gen_step2 *)
  eapply (princ_paramL_n any drsa drsb (@wk_sing _ _) fxy1 l rsfw).
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
inversion fpl. clear fpl X0. destruct X.
inversion o.  specialize (X (Nat.add cae0 cae3)).  inversion X.
rewrite -> repeat_add in X0.
rewrite -> app_assoc in X0.
exact (X0 _ _ _ eq_refl eq_refl mrg). Qed.

Check gs_wk_ng.

Lemma ctr_neq_paramL V (A B : LLfml V) rules drsa drsb psa ca psb cb :
  rsub (fmlsruleg (ctrrule (Query B))) rules -> 
  fmlsruleg (ctrrule (Query B)) psa ca -> A <> Query B -> 
  gen_step2 (osscamQ dual rules) A empty_relT drsa drsb psa ca psb cb.
Proof. intros rscr ctra anb.
apply fmlsrule_g_ex in ctra. cD.
apply gs_ossca_mQ_lem.
- eapply gs2_eq.  intro.  apply req_sym.  apply osscam_nn_eq.
eapply princ_paramL_nn_ne.
+ apply ctr_sing.
+ exact ctra1.
+ intros * ctrpc.  destruct ctrpc.
eexists. reflexivity.  intro ba.  exact (anb (eq_sym ba)).
+ exact rscr.

- apply gs_osscaQ_lem. intros. subst.
apply gs_osscang_Q_lem.  apply gs_osscan_g_lem.
intro n.  apply gs2_osscann_n.
eapply princ_paramL_nn_ne.
+ apply ctr_sing.
+ exact ctra1.
+ intros * ctrpc.  destruct ctrpc.
eexists. reflexivity.  intro ba.  exact (anb (eq_sym ba)).
+ exact rscr.

- apply gs_osscaQ'_lem. intros. subst.
apply gs_osscang_Q'_lem.  apply gs_osscan_g_lem.
intro n.  apply gs2_osscann_n.
apply gs2_osscann_dual_e'.
eapply princ_paramL_nn_ne.
+ apply ctr_sing.
+ exact ctra1.
+ intros * ctrpc.  destruct ctrpc.
eexists. reflexivity. simpl. rewrite dual_dual.
intro ba.  exact (anb (eq_sym ba)).
+ exact rscr.
Qed.

Lemma wk_neq_paramL V (A B : LLfml V) rules drsa drsb psa ca psb cb :
  rsub (fmlsruleg (wkrule (Query B))) rules -> 
  fmlsruleg (wkrule (Query B)) psa ca -> A <> Query B -> 
  gen_step2 (osscamQ dual rules) A empty_relT drsa drsb psa ca psb cb.
Proof. intros rswr wka anb.
apply fmlsrule_g_ex in wka. cD.
apply gs_ossca_mQ_lem.
- eapply gs2_eq.  intro.  apply req_sym.  apply osscam_nn_eq.
eapply princ_paramL_nn_ne.
+ apply wk_sing.
+ exact wka1.
+ intros * wkpc.  destruct wkpc.
eexists. reflexivity.  intro ba.  exact (anb (eq_sym ba)).
+ exact rswr.

- apply gs_osscaQ_lem. intros. subst.
apply gs_osscang_Q_lem.  apply gs_osscan_g_lem.
intro n.  apply gs2_osscann_n.
eapply princ_paramL_nn_ne.
+ apply wk_sing.
+ exact wka1.
+ intros * wkpc.  destruct wkpc.
eexists. reflexivity.  intro ba.  exact (anb (eq_sym ba)).
+ exact rswr.

- apply gs_osscaQ'_lem. intros. subst.
apply gs_osscang_Q'_lem.  apply gs_osscan_g_lem.
intro n.  apply gs2_osscann_n.
apply gs2_osscann_dual_e'.
eapply princ_paramL_nn_ne.
+ apply wk_sing.
+ exact wka1.
+ intros * wkpc.  destruct wkpc.
eexists. reflexivity. simpl. rewrite dual_dual.
intro ba.  exact (anb (eq_sym ba)).
+ exact rswr.
Qed.

Check wk_neq_paramL.

Lemma Q_or_not {V} A : {A' : _ & A = @Query V A'} + forall A', A <> @Query V A'.
destruct A.
12 : left ; eexists ; reflexivity.
all: right ; intros A' H ; inversion H. Qed.

Axiom fml_eq_or_not : forall {V} (A : LLfml V), forall B, (A = B) + (A <> B).

Lemma gs2_wk_Q V (A : LLfml V) B rules any drsa drsb psa psb ca cb :
  rsub (fmlsruleg (wkrule (Query B))) rules ->
  fmlsruleg (wkrule (Query B)) psa ca ->
  gen_step2 (osscamQ dual rules) A any drsa drsb psa ca psb cb.
Proof. intros rswr fwa.
pose (fml_eq_or_not A (Query B)). sD.
+ subst.  apply gen_step2_empty.
apply gs2_ng_mQ. exact (gs_wk_ng _ _ _ rswr fwa).
(* where cut-formula is different from formula that is conclusion of rule,
must be a parametric case *)
+ apply (gen_step2_sub_mono (rsub_emptyT _)).
exact (wk_neq_paramL _ _ rswr fwa s).
Qed.

Lemma gs2_ctr_Q V (A : LLfml V) B rules any drsa drsb psa psb ca cb :
  rsub (fmlsruleg (ctrrule (Query B))) rules ->
  fmlsruleg (ctrrule (Query B)) psa ca ->
  gen_step2 (osscamQ dual rules) A any drsa drsb psa ca psb cb.
Proof. intros rswr fwa.
pose (fml_eq_or_not A (Query B)). sD.
+ subst.  apply gen_step2_empty.
apply gs2_ng_mQ. exact (gs_ctr_ng _ _ _ rswr fwa).
(* where cut-formula is different from formula that is conclusion of rule,
must be a parametric case *)
+ apply (gen_step2_sub_mono (rsub_emptyT _)).
exact (ctr_neq_paramL _ _ rswr fwa s).
Qed.

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
inversion X0. destruct H0.  simpl in H. inversion H.
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
unfold fmlsext. simpl. destruct H.
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
destruct m.
eapply merge_paramL_ngl_QT.  apply adm_exch_maell.
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
* inversion X2. destruct H.  unfold fmlsext. simpl. clear X2.
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

