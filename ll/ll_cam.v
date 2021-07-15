
Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT ddT dd_fc.
Require Import gen_tacs swappedT.
Require Import fmlsext.
Require Import lldefs ll_lems.
Require Import gstep gentree.

(* dual and subformula relation are arbitrary *)
Lemma princ_paramL_nn W (A : W) rules dual nl nr any prs xs ys
  drsa drsb psa psb ca cb : rsub prs (fun _ => sing) ->
  fmlsrule xs ys prs psa ca -> leT nl (length xs) ->
  rsub (fmlsruleg prs) rules ->
  gen_step2 (osscann dual rules nl nr) A any drsa drsb psa ca psb cb.
Proof. intros ps fpa lxs rsr. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpr.
apply osscannI. intros * cae cbe m. subst.
inversion fpa. subst. clear fpa.
pose (rsubD ps ps0 c X). simpl in s. destruct s.
unfold fmlsext in H1.
pose (get_prefix _ lxs). cD. subst xs.
rewrite <- app_assoc in H1.
apply strip_prefixes in H1.  cD.
2: rewrite s0 ; rewrite repeat_length ; reflexivity.
subst ls.  eapply merge_ctns_singleL in m. cD. subst. clear s0.
eapply derI.
+ apply (rsubD rsr).  eapply OSgctxt_eq. apply X.
reflexivity. reflexivity.
+ apply dersrecI_forall. intros c inmf.
apply InT_mapE in inmf. cD.
eapply ForallTD_forall in fpl.
2: apply (InT_map _ inmf1).
destruct fpl. destruct o. subst.
unfold fmlsext.  unfold fmlsext in d0. simpl in d0.
rewrite <- app_assoc in d0.
apply (d0 _ _ _ eq_refl eq_refl).
replace m0 with ([] ++ m0) by reflexivity.
exact (merge_app m3 (merge_app (merge_Rnil inmf) m6)). Qed.

(* dual and subformula relation are not arbitrary *)
Definition princ_paramR_nn V A rules nl nr prs xs ys
    drsa drsb psa psb ca cb rps fpb leys rsr :=
  gs2_osscann_dual' (@princ_paramL_nn _ (dual A : LLfml V) rules dual nr nl
    isubfml prs ys xs drsb drsa psb psa cb ca rps fpb leys rsr).

Check princ_paramL_nn.  Check princ_paramR_nn.

(* princ_paramL - dual and isubfml are generic *)
(* this is a special case of princ_paramL_nn *)
Lemma princ_paramL' W (A : W) rules dual any prs x xs ys
  drsa drsb psa psb ca cb : rsub prs (fun _ => sing) ->
  fmlsrule (x :: xs) ys prs psa ca -> rsub (fmlsruleg prs) rules -> 
  gen_step2 (osscam dual rules) A any drsa drsb psa ca psb cb.
Proof. intros rss rsfr rpr. eapply gs2_eq.
intro. apply req_sym.  apply osscam_nn_eq.
eapply (fun x => princ_paramL_nn _ _ _ rss rsfr x rpr).
simpl. apply leT_n_S. apply leT_0_n. Qed.

Definition princ_paramL W A rules dual any prs x xs ys :=
  @princ_paramL' W A rules dual any prs x xs ys 
    (derrec rules emptyT) (derrec rules emptyT).
  
(* princ_paramR - specific to dual, isubfml *)
Definition princ_paramR V A rules prs x xs ys psa psb ca cb rps fpb rsr := 
  gs2_osscam_dual' (@princ_paramL _ (dual A : LLfml V)
    rules dual isubfml prs x xs ys psb psa cb ca rps fpb rsr).
Check princ_paramL.  Check princ_paramR.

(* if the cut formula is different from the conclusion of rule(s) prs,
  then it must be parametric, not principal *)
Lemma princ_paramL_nn_ne' W (A : W) rules dual nl nr any prs 
  drsa drsb psa psb ca cb : rsub prs (fun _ => sing) ->
  fmlsruleg prs psa ca -> 
  (forall ps c, prs ps c -> {c' : W & c = [c'] & c' <> A}) -> 
  rsub (fmlsruleg prs) rules ->
  gen_step2 (osscann dual rules nl nr) A any drsa drsb psa ca psb cb.
Proof.
intros ps fgp.
apply fmlsrule_g_ex in fgp. cD.
pose (leT_or_gt nl (length fgp)). destruct s.
(* assuming leT nl (length fgp) *)
intros cd.  eapply princ_paramL_nn ; eassumption. 
(* assuming leT (S (length fgp)) nl *)
intros cd rsr saa fpl fpr dl dr. 
apply osscannI. intros * cae cbe mrg. clear saa fpl fpr dl dr ps rsr.
destruct fgp1.  specialize (cd _ _ p). destruct cd.
unfold fmlsext in cae. subst.
acacD'T2 ; subst.
+ rewrite app_length in l. rewrite repeat_length in l.
destruct (leT_S_F (leT_trans l (leT_plus_l _ _))).
+ rewrite app_nil_r in cae0. subst. rewrite repeat_length in l.
destruct (leT_S_F l).
+ apply repeat_eq_app in cae0. cD.
destruct cae4 ; simpl in cae6 ; inversion cae6.  destruct (n H0).
+ apply repeat_eq_app in cae0. cD.
destruct cae3 ; simpl in cae4 ; inversion cae4.  destruct (n H0).
Qed.

(* like princ_paramL_nn_ne' but with fmlsrule xs ys *)
Definition princ_paramL_nn_ne W (A : W) rules dual nl nr any prs xs ys
  drsa drsb psa psb ca cb rpr fr := 
  @princ_paramL_nn_ne' W (A : W) rules dual nl nr any prs 
  drsa drsb psa psb ca cb rpr (@fmlsrule_g _ xs ys _ _ _ fr).

Check princ_paramL_nn_ne.  Check princ_paramL_nn_ne'. 

Print Implicit gs2_eq.

Definition princ_paramL_n W (A : W) rules dual n any prs xs ys
  drsa drsb psa psb ca cb rps fa lnx rfr :=
  gs2_osscann_n (@princ_paramL_nn W (A : W) rules dual n 1 any prs xs ys
  drsa drsb psa psb ca cb rps fa lnx rfr).

(* note princ_paramL is the case n=1 of this *)
(* isubfml is generic, not dual due to osscan'_eq *)
Lemma princ_paramL_n' V (A : LLfml V) rules n any prs x xs ys
  drsa drsb psa psb ca cb : rsub prs (fun _ => sing) ->
  fmlsrule (x :: xs) ys prs psa ca -> rsub (fmlsruleg prs) rules -> 
  gen_step2 (osscan' dual rules n) A any drsa drsb psa ca psb cb.
Proof. intros ps fpa rsr.  apply gs2_osscann_n'.
eapply princ_paramL_nn.
exact ps. exact fpa. simpl. apply leT_n_S. apply leT_0_n.
exact rsr. Qed.

(* note princ_paramR is the case n=1 of this *)
Definition princ_paramR_n V A rules n prs x xs ys
  drsa drsb psa psb ca cb rps fp rsr :=
  gs2_osscann_n (gs2_osscann_dual' (gs2_osscan'_nn (@princ_paramL_n'
  V (dual A) rules n isubfml prs x xs ys drsb drsa psb psa cb ca rps fp rsr))).

(* use empty_relT rather than isubfml to get dual result *)
Definition princ_paramR_n_e V A rules n prs x xs ys
  drsa drsb psa psb ca cb rps fp rsr :=
  gs2_osscann_n (gs2_osscann_dual_e' (gs2_osscan'_nn 
    (@princ_paramL_n' V (dual A)
    rules n empty_relT prs x xs ys drsb drsa psb psa cb ca rps fp rsr))).

Lemma merge_paramL_n V (A : LLfml V) rules n any prs x xs ys
  drsb psa psb ca cb : rsub prs (fun _ => sing) ->
  merge_ctxt (x :: xs) ys prs psa ca -> rsub (merge_ctxtg prs) rules -> 
  gen_step2 (osscan' dual rules n) A any 
    (derrec rules emptyT) drsb psa ca psb cb.
Proof. intros ps mcp rsmr. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpr.
clear dl dr. 
apply osscanI. intros. subst. apply merge_sym in H1.
inversion mcp. clear mcp. subst.
pose (rsubD ps _ c X). simpl in s. destruct s.
eapply merge_ctns_singleL in H1. cD. subst.
rewrite -> dual_dual in H3.  inversion H3 ; subst ; clear H3. 

(* left premise has cut-formula A *)
- apply ForallT_2D in fpl. cD. clear fpl fpl1.
destruct fpl2. simpl in d. rewrite -> dual_dual in d.
pose (merge_assoc H6 (merge_sym H10)) as mal. cD.
pose (merge_assoc H9 (merge_sym H4)) as mar. cD.
clear H6 H10 H4 H9.
pose (merge_app mal1 (merge_app (merge_Rnil pl) mar1)).
simpl in m.  apply merge_sym in m.
specialize (d _ _ _ eq_refl eq_refl m). clear m mal1 mar1.
eapply derI. apply (rsubD rsmr).  eapply merge_ctxtgI. 
apply (merge_ctxtI _ _ _ _ X (merge_sym mal0) (merge_sym mar0)).
repeat (assumption || apply dlCons || apply dlNil).

(* right premise has cut-formula A *)
- apply ForallT_2D in fpl. cD. clear fpl2 fpl0.
destruct fpl1. simpl in d. rewrite -> dual_dual in d.
pose (merge_assoc H6 H10) as mal. cD.
pose (merge_assoc H9 H4) as mar. cD.
clear H6 H10 H4 H9.
pose (merge_app mal1 (merge_app (merge_Rnil pr) mar1)).
simpl in m. apply merge_sym in m.
specialize (d _ _ _ eq_refl eq_refl m). clear m mar1 mal1.
eapply derI. apply (rsubD rsmr). eapply merge_ctxtgI. 
apply (merge_ctxtI _ _ _ _ X mal0 mar0).
repeat (assumption || apply dlCons || apply dlNil).
Qed.

Check merge_paramL_n.
Print Implicit gs2_osscan'_m.

(* note - could prove this directly, with dual generic, see commit
  4c29c6c2e2bf82cb755fef961e9c998715b8124b *)

Definition merge_paramL'  V A rules any prs x xs ys drsb psa psb ca cb
  rps mc rmr := gs2_osscan'_m 
  (@merge_paramL_n V A rules 1 any prs x xs ys drsb psa psb ca cb rps mc rmr).

Check merge_paramL'.
Check (fun x => gs2_osscann_n (gs2_osscann_dual' (gs2_osscan'_nn x))).

Definition merge_paramL V A rules (* dual *) any prs x xs ys :=
  @merge_paramL' V A rules (* dual *) any prs x xs ys (derrec rules emptyT).

(* merge_paramR - specific to dual, isubfml *)
Definition merge_paramR V A rules prs x xs ys psa psb ca cb rps mcp rsmr :=
  gs2_osscam_dual' (@merge_paramL _ (dual A : LLfml V)
  rules (* dual *) isubfml prs x xs ys psb psa cb ca rps mcp rsmr).

Check merge_paramL.  Check merge_paramR.

Definition merge_paramR_n V A rules prs n x xs ys 
    drsa psa psb ca cb rps mcp rsmr :=
  gs2_osscann_n (gs2_osscann_dual' (gs2_osscan'_nn 
    (@merge_paramL_n _ (dual A : LLfml V)
  rules n isubfml prs x xs ys drsa psb psa cb ca rps mcp rsmr))).

Definition merge_paramR_n_e V A rules prs n x xs ys 
    drsa psa psb ca cb rps mcp rsmr :=
  gs2_osscann_n (gs2_osscann_dual_e' (gs2_osscan'_nn 
    (@merge_paramL_n _ (dual A : LLfml V)
  rules n empty_relT prs x xs ys drsa psb psa cb ca rps mcp rsmr))).

Check merge_paramL_n.  Check merge_paramR_n.  Check merge_paramR_n_e.

Lemma plusL_wth V (A : LLfml V) rules ys zs drsa drsb psa psb ca cb :
  fmlsrule [] ys PlusLrule psa ca -> 
  fmlsrule [] zs Wthrule psb cb -> 
  gen_step2 (osscam dual rules) A isubfml drsa drsb psa ca psb cb.
Proof. intros psca pscb. unfold gen_step2.
intros sub fpl fpr dl dr. clear dl dr.
apply osscamI. intros. subst.
inversion psca. subst. clear psca. 
inversion pscb. subst. clear pscb. 
destruct X. destruct X0.
unfold fmlsext in H2. unfold fmlsext in H3.
simpl in H2. simpl in H3.
injection H2 as. injection H3 as.
subst. simpl in H2. injection H2 as. subst.
sfs_in fpl. sfs_in fpr.
inversion fpl. inversion fpr. clear fpl fpr. subst.
specialize (sub A0 (isub_plusL _ _) _ (fst X) _ (fst X1)).
destruct sub.  exact (d _ _ _ eq_refl eq_refl H1).  Qed.

Lemma plusR_wth V (A : LLfml V) rules ys zs drsa drsb psa psb ca cb :
  fmlsrule [] ys PlusRrule psa ca -> 
  fmlsrule [] zs Wthrule psb cb -> 
  gen_step2 (osscam dual rules) A isubfml drsa drsb psa ca psb cb.
Proof. intros psca pscb. unfold gen_step2.
intros sub fpl fpr dl dr. clear dl dr.
apply osscamI. intros. subst.
inversion psca. subst. clear psca. 
inversion pscb. subst. clear pscb. 
destruct X. destruct X0.
unfold fmlsext in H2. unfold fmlsext in H3.
simpl in H2. simpl in H3.
injection H2 as. injection H3 as.
subst. simpl in H2. injection H2 as. subst.
sfs_in fpl. sfs_in fpr.
inversion fpl. inversion fpr. inversion X2. clear fpl fpr X2. subst.
specialize (sub B (isub_plusR _ _) _ (fst X) _ (fst X3)).
destruct sub.  exact (d _ _ _ eq_refl eq_refl H1).  Qed.

Check plusL_wth.  Check plusR_wth.

Definition wth_plusL V A rules ys zs drsa drsb psa psb ca cb rla rlb :=
  gs2_osscam_dual' 
    (@plusL_wth V (dual A) rules ys zs drsb drsa psb psa cb ca rlb rla).
Definition wth_plusR V A rules ys zs drsa drsb psa psb ca cb rla rlb :=
  gs2_osscam_dual' 
    (@plusR_wth V (dual A) rules ys zs drsb drsa psb psa cb ca rlb rla).

Check wth_plusL.  Check wth_plusR.

Lemma tens_par V (A : LLfml V) rules ys zs drsa psa psb ca cb :
  merge_ctxt [] ys Tensrule psa ca -> 
  fmlsrule [] zs Parrule psb cb -> 
  gen_step2 (osscam dual rules) A isubfml drsa (derrec rules emptyT)
         psa ca psb cb.
Proof. intros psca pscb. unfold gen_step2.
intros sub fpl fpr dl dr. clear dl dr.
apply osscamI. intros. subst.
inversion psca. subst. clear psca. 
inversion pscb. subst. clear pscb. 
inversion X. subst. 
inversion H0. inversion H. clear X H0 H. subst.
simpl in fpl. sfs_in fpr.  unfold fmlsext in H5.
destruct X0.  simpl in H5. inversion H5. clear H5. subst.
pose (merge_assoc H1 (merge_sym H3)). cD. clear H1 H3.
inversion fpl. inversion fpr. subst. cD. clear fpl fpr X2 X3 X4.
pose (sub A0 (isub_tensL _ _) _ X _ X1). 
destruct o. specialize (d _ _ _ eq_refl eq_refl (mergeRI _ s1)).
clear X X1. inversion X0. cD. clear X0 X1 X2. subst.
specialize (sub B (isub_tensR _ _) _ X _ d).  
destruct sub.  exact (d0 _ _ _ eq_refl eq_refl s0). Qed.

Definition par_tens V A rules ys zs drsb psa psb ca cb rla rlb :=
  gs2_osscam_dual' 
    (@tens_par V (dual A) rules ys zs drsb psb psa cb ca rlb rla).

Check tens_par. Check par_tens.

Lemma bot_one V (A : LLfml V) rules any ys drsb psa psb ca cb :
  fmlsrule [] ys Botrule psa ca -> Onerule psb cb -> 
  gen_step2 (osscam dual rules) A any (derrec rules emptyT) drsb psa ca psb cb.
Proof. intros psca pscb. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpr dl dr.
apply osscamI. intros. subst.
inversion psca. subst. clear psca. 
inversion pscb. subst. clear pscb. 
apply merge_RnilE in H1.  destruct X. 
unfold fmlsext in H2.  simpl in H2.  injection H2 as . subst. clear H3.
sfs_in fpl.  inversion fpl. subst. cD. assumption. Qed.

Definition one_bot V A rules ys drsa psa psb ca cb rla rlb :=
  gs2_osscam_dual' (@bot_one V (dual A) rules _ ys drsa psb psa cb ca rlb rla).

(* now this one isn't so straightforward because the dual A in the id rule
  can be merged anywhere into the context rs of the |- dual A :: rs
  so we do need admissibility of exchange *)
Lemma gs_idL V (A B : LLfml V) rules any drsa psa psb ca cb 
  (adm_exch : forall (seq seq' : list (LLfml V)),
    swapped seq' seq -> adm rules [seq'] seq) :
  Idrule B psa ca -> 
  gen_step2 (osscam dual rules) A any drsa
         (derrec rules emptyT) psa ca psb cb.
Proof. intro id. unfold gen_step2.
intros sub fpl fpr dl dr. clear sub fpl fpr dl.
apply osscamI. intros. subst.
inversion id. subst. clear id.
apply merge_singleL in H1. cD. subst.
erequire adm_exch.  erequire adm_exch.  require adm_exch.
all: cycle 1. destruct adm_exch. apply d.
exact (dersrec_singleI dr). swap_tac_Rc. Qed.

Definition gs_idR V A B rules drsb psa psb ca cb ae rlb :=
  gs2_osscam_dual' (@gs_idL V (dual A) B rules _ drsb psb psa cb ca ae rlb).

Check gs_idL.  Check gs_idR. 

(* rule on left is Tensrule *)
Lemma gs_tens_mall' V (A : LLfml V) rules psa psb ca cb
  (rs : rsub mall_rules rules) 
  (adm_exch : forall seq seq' : list (LLfml V),
             swapped seq' seq -> adm rules [seq'] seq)
  (m : merge_ctxtg Tensrule psa ca) (mb : mall_rules psb cb) :
  gen_step2 (osscam dual rules) A isubfml (derrec rules emptyT)
    (derrec rules emptyT) psa ca psb cb.
Proof. destruct m. destruct m. destruct cl.
(* with left context [], all possibilities for rule on right *)
destruct mb. destruct f. destruct Φ1.
+ apply gs_osscam_lem.  intros * cae cbe.
unfold fmlsext in cbe.  simpl in cae.  simpl in cbe. 
inversion t. subst. inversion cae. subst. 
destruct l as [ psb cb rb|psb cb rb|psb cb rb|psb cb rb|psb cb rb|psb cb rb] ; 
(* following gets all cases of cut where formulae not duals *)
(destruct rb ; subst ; simpl in cbe ; inversion cbe).
subst. clear cbe.
eapply tens_par.
exact (merge_ctxtI _ _ _ _ t m m0).
apply OSctxt. apply Parrule_I.
+ eapply (princ_paramR llprinc_sing).
apply OSctxt. apply l.  exact (rsub_trans (rsubI _ _ princ_mallI) rs).
+ destruct m1. destruct m1. destruct cl.
* destruct t.  destruct t0. 
apply gs_osscam_lem.
intros. simpl in H. simpl in H0. 
inversion H. inversion H0. subst. simpl in H4. discriminate H4.
* eapply (merge_paramR tens_sing).
exact (merge_ctxtI _ _ _ _ t0 m1 m2).
exact (rsub_trans (rsubI _ _ tens_mallI) rs).
+ (* rule on right is Onerule *)
apply gs_osscam_lem.
destruct t. destruct o. simpl.
intros * cae cbe. inversion cae. inversion cbe.
subst. simpl in H2. inversion H2.
+ exact (gs_idR _ adm_exch i).
+ exact (gs_idR _ adm_exch i).
+ eapply (merge_paramL _ tens_sing).
exact (merge_ctxtI _ _ _ _ t m m0).
exact (rsub_trans (rsubI _ _ tens_mallI) rs).
Qed.

Definition gs_tens_mall V A psa psb ca cb :=
  @gs_tens_mall' V A _ psa psb ca cb (rsub_id mall_rules).

(* rule on right is Tensrule *)
Definition gs_mall_tens' V A rules psa psb ca cb rs ae ma m :=
  gs2_osscam_dual' (@gs_tens_mall' V (dual A) rules psb psa cb ca rs ae m ma).
Definition gs_mall_tens V A psa psb ca cb ae ma m :=
  gs2_osscam_dual' (@gs_tens_mall V (dual A) psb psa cb ca ae m ma).

(* rule on right is Onerule *)
Lemma gs_mall_one' V (A : LLfml V) rules psa psb ca cb
  (rs : rsub mall_rules rules) 
  (adm_exch : forall seq seq' : list (LLfml V),
             swapped seq' seq -> adm rules [seq'] seq)
  (ma : mall_rules psa ca) (mb : Onerule psb cb) :
  gen_step2 (osscam dual rules) A isubfml (derrec rules emptyT)
    (derrec rules emptyT) psa ca psb cb.
Proof. destruct ma. destruct f. destruct Φ1.
- apply gs_osscam_lem.  intros * cae cbe. 
inversion mb as [pso fe]. subst cb.  unfold fmlsext in cae.
destruct l as [ psa ca ra|psa ca ra|psa ca ra|psa ca ra|psa ca ra|psa ca ra] ; 
inversion ra ; subst ca ; simpl in cae ; inversion cae ; 
subst A ; simpl in fe ; inversion fe.
sfs.  eapply bot_one.
eapply OSctxt_eq ; split.  apply Onerule_I.
- eapply (princ_paramL _ llprinc_sing). 
apply OSctxt. apply l.  exact (rsub_trans (rsubI _ _ princ_mallI) rs).
- apply (gs_tens_mall' rs adm_exch m (one_mallI mb)).
- apply gs_osscam_lem.  intros * cae cbe. destruct o. destruct mb.
  inversion cae. inversion cbe. subst. simpl in H2. inversion H2.
- exact (gs_idL _ _ adm_exch i).
- exact (gs_idL _ _ adm_exch i).
Qed.

Definition gs_mall_one V A psa psb ca cb :=
  @gs_mall_one' V A _ psa psb ca cb (rsub_id mall_rules).

(* rule on left is Onerule *)
Definition gs_one_mall' V A rules psa psb ca cb rs ae ma mb :=
  gs2_osscam_dual' (@gs_mall_one' V (dual A) rules psb psa cb ca rs ae mb ma).
Definition gs_one_mall V A psa psb ca cb ae ma mb :=
  gs2_osscam_dual' (@gs_mall_one V (dual A) psb psa cb ca ae mb ma).

Lemma gs_mall' V (A : LLfml V) rules psa psb ca cb 
  (rs : rsub mall_rules rules)
  (adm_exch : forall (seq seq' : list (LLfml V)),
    swapped seq' seq -> adm rules [seq'] seq) :
  mall_rules psa ca -> mall_rules psb cb -> 
  gen_step2 (osscam dual rules) A isubfml (derrec rules emptyT)
         (derrec rules emptyT) psa ca psb cb.
Proof. intros ma mb. inversion ma ; subst. destruct X. destruct Φ1.
destruct mb. destruct f. destruct Φ1.
- apply gs_osscam_lem.  intros * cae cbe.
sfs_in cae.  sfs_in cbe. 
destruct l as [ psa ca ra|psa ca ra|psa ca ra|psa ca ra|psa ca ra|psa ca ra] ; 
destruct l0 as [ psb cb rb|psb cb rb|psb cb rb|psb cb rb|psb cb rb|psb cb rb] ; 
(* following gets all cases of cut where formulae not duals *)
try (destruct ra ; destruct rb ;
  simpl in cae ;  simpl in cbe ; 
  inversion cae ; inversion cbe as [fe] ; subst ;
  simpl in fe ; discriminate fe).
eapply wth_plusL ; apply OSctxt ; assumption.
eapply wth_plusR ; apply OSctxt ; assumption.
eapply plusL_wth ; apply OSctxt ; assumption.
eapply plusR_wth ; apply OSctxt ; assumption.
- eapply (princ_paramR llprinc_sing).
apply OSctxt. apply l0.  exact (rsub_trans (rsubI _ _ princ_mallI) rs).
(* rule on right is Tensrule *)
- exact (gs_mall_tens' rs adm_exch ma m).
(* rule on right is Onerule *)
- exact (gs_mall_one' rs adm_exch ma o).
- exact (gs_idR _ adm_exch i).
- exact (gs_idR _ adm_exch i).
- eapply (princ_paramL _ llprinc_sing). 
apply OSctxt. apply l.  exact (rsub_trans (rsubI _ _ princ_mallI) rs).
(* rule on left is Tensrule *)
- exact (gs_tens_mall' rs adm_exch X mb). 
- (* rule on left is Onerule *)
exact (gs_one_mall' rs adm_exch X mb).
- exact (gs_idL _ _ adm_exch X).
- exact (gs_idL _ _ adm_exch X).
Qed.

Check gs_mall'.

Definition gs_mall V (A : LLfml V) psa psb ca cb :=
  @gs_mall' V (A : LLfml V) _ psa psb ca cb (rsub_id _).

(* cut-admissibility for mall, explicitly depending on exchange admissibility *)
Theorem cut_adm_mall' {V} (A : LLfml V)  
  (adm_exch : forall (seq seq' : list (LLfml V)),
    swapped seq' seq -> adm mall_rules [seq'] seq) :
  forall cl, derrec mall_rules emptyT cl ->
  forall cr, derrec mall_rules emptyT cr ->
  osscam dual mall_rules A cl cr.
Proof. apply (gen_step2_lemT (AccT_isubfml A)).
intros *. exact (gs_mall adm_exch). Qed.

(* proof first using induction on heights of sub-derivations *)
Theorem cut_adm_mall_alt {V} (A : LLfml V)  
  (adm_exch : forall (seq seq' : list (LLfml V)),
    swapped seq' seq -> adm mall_rules [seq'] seq) :
  forall cl, derrec mall_rules emptyT cl ->
  forall cr, derrec mall_rules emptyT cr ->
  osscam dual mall_rules A cl cr.
Proof. intros cl dl cr dr.
assert (dt2fun (osscam dual mall_rules) A (fcI dl) (fcI dr)).
all: cycle 1.
unfold dt2fun in X. simpl in X.  rewrite !der_concl_eq in X. exact X.
apply (height_step2_tr_lem _ _ (AccT_isubfml A)).
intros.  apply gs2_tr_height.
destruct dta.  destruct dtb.
apply gs2c_gs2tr. apply gs2_gs2c. 
apply (gs_mall adm_exch) ; apply bot_is_rule. Qed.

(*
Print Implicit gs2c_gs2tr. Print Implicit gs2_gs2c.
Print Implicit height_step2_tr_lem.
*)
