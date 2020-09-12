
(* K4 modal logic, using lists of formulae *)
(* exchange *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.
Unset Universe Polymorphism.
Test Universe Polymorphism.
Unset Printing Universes.
Test Printing Universes.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen. 
Require Import genT.
Require Import ddT.
Require Import gstep.
Require Import gen_ext.
Require Import gen_seq.
Require Import rtcT.
Require Import List_lemmasT.
Require Import gen_tacs.
Require Import swappedT.
Require Import k4.

(* lemma re gen_ext and swapped *)
Lemma gen_ext_swap: forall T (l le : list T),
  gen_ext l le -> forall les, swapped le les -> 
  sigT (fun ls => prod (swapped l ls) (gen_ext ls les)).
Proof. intros until 0. intro ge. induction ge.
{ intros. exists []. split. apply swapped_same.
apply gen_ext_nil_any.  }
{ intros. inversion X. subst.
destruct A. simpl in *. destruct B.  simpl in *.
exists (x :: l). split. apply swapped_same.
rewrite <- H. apply gen_ext_cons. apply ge.
{ rewrite <- app_comm_cons in H. injection H. intros. subst. 
apply gen_ext_splitR in ge. cD. subst.
apply gen_ext_splitR in ge3. cD. subst.
exists ([] ++ ge3 ++ (t :: ge) ++ ge1). split.
eapply swapped_I. 2 : reflexivity. simpl. reflexivity.
simpl.  repeat (apply gen_ext_app || apply gen_ext_cons || assumption).
}
{ simpl in H. injection H. intros. subst.
apply gen_ext_splitR in ge. cD. subst.
apply gen_ext_splitR in ge3. cD. subst.
apply gen_ext_splitR in ge6. cD. subst.
exists ((t :: ge) ++ ge6 ++ ge3 ++ ge0). split.
rewrite app_comm_cons.  apply swapped_I'.
repeat (apply gen_ext_app || apply gen_ext_cons || assumption).
} }
{ intros. inversion X. subst.
destruct A. simpl in *. destruct B.  simpl in *.
exists l. split. apply swapped_same.
rewrite <- H. eapply gen_ext_trans. apply gen_ext_extra. apply ge.
apply gen_ext_refl.
{ rewrite <- app_comm_cons in H. injection H. intros. subst.
apply gen_ext_splitR in ge. cD. subst.
apply gen_ext_splitR in ge3. cD. subst.
exists ([] ++ ge3 ++ ge ++ ge1). split.
eapply swapped_I. 2 : reflexivity. simpl. reflexivity.
simpl.  repeat (apply gen_ext_app || apply gen_ext_extra || assumption).
}
{ rewrite <- app_comm_cons in H. injection H. intros. subst.
apply gen_ext_splitR in ge. cD. subst.
apply gen_ext_splitR in ge3. cD. subst.
apply gen_ext_splitR in ge6. cD. subst.
eexists. split. apply swapped_I'.
repeat (apply gen_ext_app || apply gen_ext_extra || assumption).
} } Qed.

Check gen_ext_swap.

Check (fun T => @swapped T : relationT (list T)).

Definition inv_image A B (f : A -> B) (R : relationT B) x y := R (f x) (f y).

(*
Ltac swl_tac mid := eexists ; split ; 
  [> assoc_mid mid ; apply Sctxt_e ; eassumption |
    apply ForallTI_forall ; intros x inms ; apply InT_mapE in inms ; 
    destruct inms as [x0 p] ; destruct p as [sex int] ;
    destruct x0 ;  unfold seqext in sex ; destruct sex ;
    eexists ; split ;
      [> eapply InT_map ; eassumption |
      unfold seqext ; apply fst_relI ; swap_tac ]].

Ltac swr_tac mid := eexists ; split ; 
  [> assoc_mid mid ; rewrite - app_assoc ;
    (* because assoc_mid messes with antecedent *)
    apply Sctxt_e ; eassumption |
    apply ForallTI_forall ; intros x inms ; apply InT_mapE in inms ; 
    destruct inms as [x0 p] ; destruct p as [sex int] ;
    destruct x0 ;  unfold seqext in sex ; destruct sex ;
    eexists ; split ;
      [> eapply InT_map ; eassumption |
      unfold seqext ; apply snd_relI ; swap_tac ]].

Ltac concl_in_app X0 r sea :=
  pose X0 as r ; apply sea in r ; 
  destruct r ; subst ; rewrite ?app_nil_r ; rewrite ?app_nil_l ;
  simpl in X0 ; rewrite ?app_nil_r in X0.
*)

Lemma exchL_std_rule': forall W (rules : rlsT (Seql W)),
  (forall ps U S, rules ps (U, S) -> sing_empty U) ->
  forall ps c, seqrule rules ps c ->
    can_trf_rules (fst_rel (swapped (T:=W))) (seqrule rules) ps c.
Proof. intros * se * fsr.
apply fst_snd_ext in fsr.
pose (@exchL_std_rule _ _ (snd_ext_rls rules)) .
require c0. { intros * sr. inversion sr. subst.
inversion X. destruct c1. inversion H1. subst.  exact (se _ _ _ X0). }
specialize (c0 _ _ fsr).  revert c0.
apply can_trf_rules_mono'.  apply fst_snd_ext. Qed.

Check exchL_std_rule'.

Lemma exchR_std_rule': forall W (rules : rlsT (Seql W)),
  (forall ps U S, rules ps (U, S) -> sing_empty S) ->
  forall ps c, seqrule rules ps c ->
    can_trf_rules (snd_rel (swapped (T:=W))) (seqrule rules) ps c.
Proof. intros * se * fsr.
apply snd_fst_ext in fsr.
pose (@exchR_std_rule _ _ (fst_ext_rls rules)) .
require c0. { intros * sr. inversion sr. subst.
inversion X. destruct c1. inversion H1. subst.  exact (se _ _ _ X0). }
specialize (c0 _ _ fsr).  revert c0.
apply can_trf_rules_mono'.  apply snd_fst_ext. Qed.

Check exchR_std_rule'.

(*
Lemma exchL_std_rule: forall W (rules : rlsT (Seql W)),
  (forall ps U S, rules ps (U, S) -> sing_empty U) ->
  forall ps c, seqrule rules ps c ->
    can_trf_rules (fst_rel (swapped (T:=W))) (seqrule rules) ps c.
Proof. unfold can_trf_rules.
intros W rules se ps c sqr c' fr.  
pose (fun ps xs ys S rps => 
  sing_empty_app xs ys (se ps (xs ++ ys) S rps)) as sea.
inversion fr. subst. clear fr.
inversion sqr. clear sqr. subst.
destruct c as [pl pr]. (* left and right of principal rules *)
unfold seqext in H1. 
inversion H1.  clear H1. subst.
inversion X. subst.
acacD'T2 ; subst.
- concl_in_app X0 r sea.  + swl_tac H3.  + swl_tac H1.
- concl_in_app X0 r sea.  concl_in_app X0 r sea.
+ swl_tac H5.  + swl_tac C.
+ list_eq_nc. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
simpl in X0. rewrite ?app_nil_r in X0.
swl_tac H1.
- swl_tac pl.
- concl_in_app X0 r sea.  + swl_tac H5.  + swl_tac H3.
- swl_tac pl.
- swl_tac pl.
- concl_in_app X0 r sea.  + swl_tac H1.  + swl_tac H.
- concl_in_app X0 r sea.  concl_in_app X0 r sea.
+ swl_tac H3.  + swl_tac B.
+ list_eq_ncT. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X0 ; rewrite ?app_nil_r in X0.
swl_tac H.
- concl_in_app X0 r sea.  concl_in_app X0 r sea. concl_in_app X0 r sea.
+ swl_tac H5.  + swl_tac C.
+ list_eq_ncT. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X0 ; rewrite ?app_nil_r in X0.
swl_tac B.
+ list_eq_nc. destruct e.  list_eq_nc. destruct H1. subst.
rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X0 ; rewrite ?app_nil_r in X0.
swl_tac H.
- swl_tac pl.
Qed.

Check exchL_std_rule.

Lemma exchR_std_rule: forall W (rules : rlsT (Seql W)),
  (forall ps U S, rules ps (U, S) -> sing_empty S) ->
  forall ps c, seqrule rules ps c ->
    can_trf_rules (snd_rel (swapped (T:=W))) (seqrule rules) ps c.
Proof. unfold can_trf_rules.
intros W rules se ps c sqr c' fr.  
pose (fun ps xs ys U rps => 
  sing_empty_app xs ys (se ps U (xs ++ ys) rps)) as sea.
inversion fr. subst. clear fr.
inversion sqr. clear sqr. subst.
destruct c as [pl pr]. (* left and right of principal rules *)
unfold seqext in H1. 
inversion H1.  clear H1. subst.
inversion X. subst.
acacD'T2 ; subst.
- concl_in_app X0 r sea.  + swr_tac H3.  + swr_tac H1.
- concl_in_app X0 r sea.  concl_in_app X0 r sea.
+ swr_tac H5.  + swr_tac C.
+ list_eq_ncT. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
simpl in X0. rewrite ?app_nil_r in X0.
swr_tac H1.
- swr_tac pr.
- concl_in_app X0 r sea.  + swr_tac H5.  + swr_tac H3.
- swr_tac pr.
- swr_tac pr.
- concl_in_app X0 r sea.  + swr_tac H1.  + swr_tac H.
- concl_in_app X0 r sea.  concl_in_app X0 r sea.
+ swr_tac H3.  + swr_tac B.
+ list_eq_ncT. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X0 ; rewrite ?app_nil_r in X0.
swr_tac H.
- concl_in_app X0 r sea.  concl_in_app X0 r sea. concl_in_app X0 r sea.
+ swr_tac H5.  + swr_tac C.
+ list_eq_ncT. destruct e. subst. rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X0 ; rewrite ?app_nil_r in X0.
swr_tac B.
+ list_eq_ncT. destruct e.  list_eq_ncT. destruct e0. subst.
rewrite ?app_nil_r. rewrite ?app_nil_l.
  simpl in X0 ; rewrite ?app_nil_r in X0.
swr_tac H.
- swr_tac pr.
Qed.

Check exchR_std_rule.
*)

Lemma princrule_seL: forall V ps (U S : list (PropF V)),
  princrule ps (U, S) -> sing_empty U.
Proof. intros *. intros pp.
  inversion pp ; subst ; rename_last q ; inversion q ; subst ;
  apply se_empty || apply se_single. Qed.

Lemma princrule_seR: forall V ps (U S : list (PropF V)),
  princrule ps (U, S) -> sing_empty S.
Proof. intros *. intros pp.
  inversion pp ; subst ; rename_last q ; inversion q ; subst ;
  apply se_empty || apply se_single. Qed.

(* exchange just for classical system *)
Lemma exchL_cpl: forall V concl, 
  derrec (seqrule (@princrule V)) (@emptyT _) concl ->
     forall concl', fst_rel (@swapped _) concl concl' ->
     derrec (seqrule (@princrule V)) (@emptyT _) concl'.
Proof. intro. apply der_trf. apply exchL_std_rule'. apply princrule_seL. Qed.

Lemma exchR_cpl: forall V concl, 
  derrec (seqrule (@princrule V)) (@emptyT _) concl ->
     forall concl', snd_rel (@swapped _) concl concl' ->
     derrec (seqrule (@princrule V)) (@emptyT _) concl'.
Proof. intro. apply der_trf. apply exchR_std_rule'. apply princrule_seR. Qed.

Lemma map_WBox_inj V xs : forall ys, 
  map (@WBox V) xs = map (@WBox V) ys -> xs = ys.
Proof. induction xs ; simpl ; intros.
apply eq_sym in H. apply map_eq_nil in H. subst. reflexivity.
destruct ys. simpl in H.  discriminate H.
simpl in H. injection H as . apply IHxs in H0. subst. reflexivity. Qed.

(* now for the box rule of K4, first without implicit weakening *)
Lemma trf_exchL_K4_sw V ps c: @K4prrule V ps c ->
    can_trf_rules_rtc (fst_rel (@swapped _)) (@K4prrule V) ps c.
Proof. intro k4.  destruct k4.
unfold can_trf_rules_rtc. intros c' sw.      
inversion sw. subst. clear sw.
apply swapped_map_ex in H2. cD. subst.
eexists. split. apply K4prrule_I.
apply ForallTI_forall. intros x inxm.
inversion inxm. subst. clear inxm. 2: inversion H1.
eexists. split. apply InT_eq.
eapply rtn1T_trans.  eapply fst_relI. 
apply swapped_L. apply H0.

eapply rtn1T_trans.  2: apply rtn1T_refl.  eapply fst_relI.
apply swapped_R.  apply swapped_map.  assumption. Qed.

(* now for the box rule of K4 *)
Lemma trf_exchL_K4 V ps c: cgerule (@K4prrule V) ps c ->
    can_trf_rules_rtc (fst_rel (@swapped _)) (cgerule (@K4prrule V)) ps c.
Proof. intro cgk4. inversion cgk4 as [ps0 ca cs cea ces k4 gea ges]. subst. 
inversion k4. subst. clear cgk4 k4.
unfold can_trf_rules_rtc. intros c' sw.      
inversion sw. subst. clear sw.
eapply gen_ext_swap in gea. 2: eassumption. cD.
assert (sigT (fun gg => gea = map (@WBox _) gg)).
{ inversion gea0. subst. clear gea0.
repeat (match goal with | [ H : _ |- _ ] => eapply map_app_ex in H ; cD end).
subst.  eexists. rewrite - !map_app. reflexivity. }
cD. subst.  
eexists. split. eapply CGctxt.  2: eassumption.  2: eassumption.  
eapply K4prrule_I. 
apply ForallTI_forall. intros x inxm.
inversion inxm. subst. clear inxm. 2: inversion H1.
eexists. split. apply InT_eq.
inversion gea0. clear gea0.
repeat (match goal with | [ H : _ |- _ ] => eapply map_app_ex in H ; cD end).
subst.
repeat (match goal with | [ H : _ |- _ ] => eapply map_WBox_inj in H end).
subst.  rewrite !map_app.
eapply rtn1T_trans.  eapply fst_relI.  rewrite app_assoc.
eapply swapped_I.  reflexivity.  reflexivity.
eapply rtn1T_trans.  2: apply rtn1T_refl.  eapply fst_relI.  swap_tac. Qed.

Check trf_exchL_K4.

(* now for the weakening rule *)
Lemma trf_exchL_wk W ps c: cgerule (@trivrule _) ps c ->
    can_trf_rules (fst_rel (@swapped W)) (cgerule (@trivrule _)) ps c.
Proof. intro cgwk. inversion cgwk as [ps0 ca cs cea ces triv gea ges]. subst. 
inversion triv. subst. clear cgwk triv.
unfold can_trf_rules. intros c' sw.      
inversion sw. subst. clear sw.
eapply gen_ext_swap in gea. 2: eassumption. cD.
eexists. split. 
- eapply CGctxt.  2: eassumption.  2: eassumption.  apply trivrule_I.
- apply ForallTI_forall. intros x inxm. 
inversion inxm. subst. clear inxm. 2: inversion H0. 
eexists. split. apply InT_eq.
apply fst_relI. assumption. inversion X0. Qed.

Lemma trf_exchR_wk W ps c: cgerule (@trivrule _) ps c ->
    can_trf_rules (snd_rel (@swapped W)) (cgerule (@trivrule _)) ps c.
Proof. intro cgwk. inversion cgwk as [ps0 ca cs cea ces triv gea ges]. subst. 
inversion triv. subst. clear cgwk triv.
unfold can_trf_rules. intros c' sw.      
inversion sw. subst. clear sw.
eapply gen_ext_swap in ges. 2: eassumption. cD.
eexists. split. 
- eapply CGctxt.  2: eassumption.  2: eassumption.  apply trivrule_I.
- apply ForallTI_forall. intros x inxm. 
inversion inxm. subst. clear inxm. 2: inversion H0. 
eexists. split. apply InT_eq.
apply snd_relI. assumption. inversion X0. Qed.

Check trf_exchL_wk.  Check trf_exchR_wk.

Theorem exchL_rtc V concl: derrec (@K4rules V) (@emptyT _) concl ->
  forall concl', clos_refl_transT_n1 (fst_rel (@swapped _)) concl concl' ->
    derrec (@K4rules V) (@emptyT _) concl'.
Proof. apply der_trf_rtc. intros.
destruct X.  eapply can_trf_rules_rtc_mono'.
unfold rsub. apply K4_I.  apply trf_exchL_K4. assumption.
apply can_trf_rules_imp_rtc.  eapply can_trf_rules_mono.
unfold rsub. apply cpl_I.  apply exchL_std_rule'. 2: assumption.
apply princrule_seL. Qed.

Theorem exchL_K4 V concl: derrec (@K4rules V) (@emptyT _) concl ->
  forall concl', fst_rel (@swapped _) concl concl' ->
    derrec (@K4rules V) (@emptyT _) concl'.
Proof. intros. eapply exchL_rtc. eassumption.
eapply rtn1T_trans.  eassumption. apply rtn1T_refl. Qed.

Check exchL_K4.  Check exchL_rtc.

Theorem exchL_K4_swrtc V concl: derrec (@K4rules_sw V) (@emptyT _) concl ->
  forall concl', clos_refl_transT_n1 (fst_rel (@swapped _)) concl concl' ->
    derrec (@K4rules_sw V) (@emptyT _) concl'.
Proof. apply der_trf_rtc. intros.  destruct X.
- eapply can_trf_rules_rtc_mono'.
unfold rsub. apply K4_sw_I.  apply trf_exchL_K4_sw. assumption.
- apply can_trf_rules_imp_rtc.  eapply can_trf_rules_mono.
unfold rsub. apply cplsw_I.  apply exchL_std_rule'. 2: assumption.
apply princrule_seL.
- eapply can_trf_rules_rtc_mono'.
unfold rsub. apply K4_wk_I.
apply can_trf_rules_imp_rtc.  apply trf_exchL_wk. assumption.
Qed.

Theorem exchL_K4_sw V concl: derrec (@K4rules_sw V) (@emptyT _) concl ->
  forall concl', fst_rel (@swapped _) concl concl' ->
    derrec (@K4rules_sw V) (@emptyT _) concl'.
Proof. intros. eapply exchL_K4_swrtc. eassumption.
eapply rtn1T_trans.  eassumption. apply rtn1T_refl. Qed.

Check exchL_K4_sw.  Check exchL_K4_swrtc.

(* box rule without weakening, exchange on the right is trivial *)
Lemma trf_exchR_K4_sw V ps c: @K4prrule V ps c ->
    can_trf_rules (snd_rel (@swapped _)) (@K4prrule V) ps c.
Proof. intro k4.  destruct k4. 
unfold can_trf_rules. intros c' sw.
inversion sw. subst. clear sw.
eapply swapped_singleLE in H2. subst.
eexists. split. apply K4prrule_I.
apply ForallT_singleI. eexists.  split. apply InT_eq.
apply snd_relI. apply swapped_same. Qed.

Lemma trf_exchR_K4 V ps c: cgerule (@K4prrule V) ps c ->
    can_trf_rules (snd_rel (@swapped _)) (cgerule (@K4prrule V)) ps c.
Proof. intro cgk4. inversion cgk4 as [ps0 ca cs cea ces k4 gea ges]. subst. 
inversion k4. subst. clear cgk4 k4.
unfold can_trf_rules. intros c' sw.      
inversion sw. subst. clear sw.
eapply gen_ext_swap in ges. 2: eassumption. cD.

eexists. split. eapply CGctxt. 2: eassumption.  2: eassumption.  
inversion ges0. clear ges0. subst.
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
repeat (list_eq_ncT ; cD) ; subst ; simpl ; eapply K4prrule_I.
apply ForallTI_forall. intros.
eexists. split. apply InT_eq. 
inversion H. subst.  apply snd_relI. swap_tac.
inversion H1. Qed.

Check trf_exchR_K4.

Theorem exchR_K4 V concl: derrec (@K4rules V) (@emptyT _) concl ->
  forall concl', snd_rel (@swapped _) concl concl' ->
    derrec (@K4rules V) (@emptyT _) concl'.
Proof. apply der_trf. intros.
destruct X.  eapply can_trf_rules_mono.
unfold rsub. apply K4_I.  apply trf_exchR_K4. assumption.
eapply can_trf_rules_mono.
unfold rsub. apply cpl_I.  apply exchR_std_rule'. 2: assumption.
apply princrule_seR. Qed.

Theorem exchR_K4_sw V concl: derrec (@K4rules_sw V) (@emptyT _) concl ->
  forall concl', snd_rel (@swapped _) concl concl' ->
    derrec (@K4rules_sw V) (@emptyT _) concl'.
Proof. apply der_trf. intros.  destruct X.
- eapply can_trf_rules_mono.
unfold rsub. apply K4_sw_I.  apply trf_exchR_K4_sw. assumption.
- eapply can_trf_rules_mono.
unfold rsub. apply cplsw_I.  apply exchR_std_rule'. 2: assumption.
apply princrule_seR.
- eapply can_trf_rules_mono.
unfold rsub. apply K4_wk_I.  apply trf_exchR_wk. assumption.
Qed.

Check exchR_K4. Check exchR_K4_sw.

