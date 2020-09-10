
Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../ll".
Add LoadPath "../tense-lns".
Require Import gen genT ddT.
Require Import lntT swappedT lntacsT.
Require Import gstep.
Require Import fmlsext.
Require Import lldefs.

Ltac concl_in_app r s rsr := 
  pose (rsubD rsr _ _ r) as s ; inversion s ; clear s ; 
  repeat (list_eq_ncT ; sD ; subst) ;
  rewrite ?app_nil_r ; rewrite ?app_nil_l ;
  rewrite ?app_nil_r in r ; rewrite ?app_nil_l in r ; subst.

Ltac sw_tac a r := assoc_mid [a] ;
  eexists ; apply (pair (OSgctxt _ _ _ _ _ r)) ;
  apply ForallTI_forall ; intros x inms ; apply InT_mapE in inms ;
  destruct inms as [x0 p] ; destruct p as [fex int] ;
  unfold fmlsext in fex ; 
  eexists ; apply (pair (InT_map _ int)) ;
  unfold fmlsext ; subst ; swap_tac.

Ltac mea_tac := match goal with 
  | [ K : map _ _ = (_ ++ _) |- _ ] => apply map_app_ex in K ; cD ; subst end.
  
Lemma exch_princ_rule: forall W (rules : rlsT (list W)),
  rsub rules (fun _ => sing) ->
  forall ps c, fmlsruleg rules ps c ->
    can_trf_rules (swapped (T:=W)) (fmlsruleg rules) ps c.
Proof.  intros * rsr * frg c' sw.  
destruct frg.  inversion sw. clear sw. subst.
unfold fmlsext in H. 
acacD'T2 ; subst ; (* 10 subgoals *)
concl_in_app r s rsr ; sw_tac a r. 
Qed.

Check exch_princ_rule.

(*
(* specialized version for fmlsextg for Bang rule *)
Inductive fmlsrulegq W U (f : U -> W) pr : rlsT (list W) :=
  | fmlsrulegq_I : forall (cl cr : list U) (mcl mcr mc : list W) ps c,
    pr ps c -> mcl = map f cl -> mcr = map f cr -> mc = fmlsext mcl mcr c ->
    @fmlsrulegq _ _ f pr (map (fmlsext mcl mcr) ps) mc.
*)

Ltac swq_tac f a r := assoc_mid [a] ; eexists ; split ;
  [ eapply (fmlsrulegq_I f _ _ _ _ _ r) ; rewrite - ?map_app ; reflexivity
  | apply ForallTI_forall ; intros x inms ; apply InT_mapE in inms ;
  destruct inms as [x0 p] ; destruct p as [fex int] ;
  unfold fmlsext in fex ; 
  eexists ; apply (pair (InT_map _ int)) ;
  unfold fmlsext ; subst ; rewrite ?map_app ; swap_tac ].

Lemma exch_princq_rule: forall W U (f : U -> W) (rules : rlsT (list W)),
  rsub rules (fun _ => sing) ->
  forall ps c, fmlsrulegq f rules ps c ->
    can_trf_rules (swapped (T:=W)) (fmlsrulegq f rules) ps c.
Proof.  intros * rsr * frg c' sw.  
destruct frg.  inversion sw. clear sw. subst.
unfold fmlsext in H. 
acacD'T2 ; subst ; (* 10 subgoals *)
repeat mea_tac ; concl_in_app r s rsr ; swq_tac f a r. 
Qed.

Check exch_princq_rule.

Definition rpair {B A} b a := @pair A B a b.

Ltac split_mrgM := match goal with 
  | [ K : merge _ _ (_ ++ _) |- _ ] => apply merge_splitM in K ; cD ; subst end.

Ltac inv_InT' := match goal with
  | [ K : InT _ (_ :: _) |- _ ] => inversion K ; clear K ; subst
  | [ K : InT _ [] |- _ ] => inversion K ; clear K end.

Ltac fix_mrg r := eapply merge_ctxtgI ; eapply (merge_ctxtI _ _ _ _ r) ;
  repeat (eassumption || apply merge_app) ;
  repeat (eassumption || apply merge_app).

Ltac fa_sw2 := apply ForallTI_forall ; intros ; repeat inv_InT' ; (* 2 sgs *)
  [ eexists ; apply (pair (InT_eq _ _)) ; swap_tac |
  eexists ; apply (pair (InT_cons _ (InT_eq _ _))) ; swap_tac ].

Ltac do_ex_mrg r s rsr a := 
repeat split_mrgM ; concl_in_app r s rsr ;
  assoc_mid [a] ; eexists ; (split ; [ fix_mrg r | fa_sw2 ]).

Lemma exch_merge_rule: forall W (rules : rlsT (list W)),
  rsub rules (fun _ => sing) ->
  forall ps c, merge_ctxtg rules ps c ->
    can_trf_rules (swapped (T:=W)) (merge_ctxtg rules) ps c.
Proof. intros * rsr * mrg c' sw.
destruct mrg. destruct m.  inversion sw. clear sw. subst.
acacD'T2 ; subst ; (* 10 subgoals *)
do_ex_mrg r s rsr a. Qed.

Check exch_merge_rule.

(* id rules *)
Lemma id_trf {V : Set} rules (v : V) :
  rsub (Idrule (Var v)) rules -> rsub (Idrule (DVar v)) rules ->  
  forall ps c, Idrule (Var v) ps c -> can_trf_rules (@swapped _) rules ps c.
Proof.  intros rsid rsidd * idr c' sw.
destruct sw. destruct idr. subst. exists [].
pose (rsubD rsid _ _ (Idrule_I (Var v))) as idr.
pose (rsubD rsidd _ _ (Idrule_I (DVar v))) as iddr.
simpl in idr.  simpl in iddr.
acacD'T2 ; subst ; repeat (list_eq_ncT ; cD) ; subst ;
  simpl ; rewrite ?app_nil_r ; 
  apply (rpair (ForallT_nil _)) ; assumption.
Qed.

Lemma idd_trf {V : Set} rules (v : V) :
  rsub (Idrule (Var v)) rules -> rsub (Idrule (DVar v)) rules ->  
  forall ps c, Idrule (DVar v) ps c -> can_trf_rules (@swapped _) rules ps c.
Proof.  intros rsid rsidd * idr c' sw.
destruct sw. destruct idr. subst. exists [].
pose (rsubD rsid _ _ (Idrule_I (Var v))) as idr.
pose (rsubD rsidd _ _ (Idrule_I (DVar v))) as iddr.
simpl in idr.  simpl in iddr.
acacD'T2 ; subst ; repeat (list_eq_ncT ; cD) ; subst ;
  simpl ; rewrite ?app_nil_r ; 
  apply (rpair (ForallT_nil _)) ; assumption.
Qed.

Check id_trf.  Check idd_trf.  

Lemma one_trf {V} rules : rsub Onerule rules -> 
  forall ps c, @Onerule V ps c -> can_trf_rules (@swapped _) rules ps c.
Proof. intros rsor * or c' sw. destruct or. 
apply swapped_singleLE in sw. subst.
exists []. exact (pair (rsubD rsor _ _ Onerule_I) (ForallT_nil _)). Qed.

Check one_trf.

Lemma mall_tfr {V} ps c: 
  @mall_rules V ps c -> can_trf_rules (@swapped _) mall_rules ps c.
Proof. intros mr. destruct mr. 
- pose (exch_princ_rule llprinc_sing f).
exact (can_trf_rules_mono' (rsubI _ _ princ_mallI) c0).
- pose (exch_merge_rule tens_sing m).
exact (can_trf_rules_mono' (rsubI _ _ tens_mallI) c0).
- exact (one_trf (rsubI _ _ one_mallI) o).
- exact (id_trf (rsubI _ _ (@id_mallI V v)) (rsubI _ _ (@idd_mallI V v)) i).
- exact (idd_trf (rsubI _ _ (@id_mallI V v)) (rsubI _ _ (@idd_mallI V v)) i).
Qed.

Definition exch_mall V := der_trf (@mall_tfr V).
(* also have height-reserving exchange *)
Definition exch_mall_ht V := der_trf_ht (@mall_tfr V).

Theorem adm_exch_mall V concl concl' : 
  swapped concl' concl -> adm (@mall_rules V) [concl'] concl.
Proof. intro sw. apply admI. intro drs. inversion drs.
  exact (exch_mall X sw). Qed.

Check adm_exch_mall.

Lemma maell_tfr {V} ps c: 
  @maell_rules V ps c -> can_trf_rules (@swapped _) maell_rules ps c.
Proof. intros mr. destruct mr. 
- exact (can_trf_rules_mono' (rsubI _ _ mall_maellI) (mall_tfr m)).
- pose (exch_princ_rule (@wk_sing _ _) f).
exact (can_trf_rules_mono' (rsubI _ _ (@wk_maellI _ _)) c0).
- pose (exch_princ_rule (@ctr_sing _ _) f).
exact (can_trf_rules_mono' (rsubI _ _ (@ctr_maellI _ _)) c0).
- pose (exch_princ_rule query_sing f).
exact (can_trf_rules_mono' (rsubI _ _ query_maellI) c0).
- pose (@exch_princq_rule _ _ (@Query V) _ (@bang_sing _) _ _ f).
exact (can_trf_rules_mono' (rsubI _ _ bang_maellI) c0).
Qed.

Definition exch_maell V := der_trf (@maell_tfr V).
(* also have height-reserving exchange *)
Definition exch_maell_ht V := der_trf_ht (@maell_tfr V).

Theorem adm_exch_maell {V} concl concl' : 
  swapped concl' concl -> adm (@maell_rules V) [concl'] concl.
Proof. intro sw. apply admI. intro drs. inversion drs.
  exact (exch_maell X sw). Qed.

Check adm_exch_maell.

