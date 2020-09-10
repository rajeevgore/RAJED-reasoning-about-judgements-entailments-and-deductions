
(* K4 modal logic, using lists of formulae *)
(* invertibility of classical rules *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.

Test Universe Polymorphism. (* NB Set this causes errors *)
Test Printing Universes.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../tense-lns".
Require Import gen. 
Require Import genT.
Require Import ddT.
Require Import List_lemmasT.
Require Import lntT.
Require Import swappedT.
Require Import lntacsT.
Require Import gen_seq gstep.
Require Import gen_ext.
Require Import rtcT.
Require Import k4.
Require Import k4_exch.

Definition rs_cpl_k4 {V} := rsubI _ _ (@cpl_I V).
Definition rs_cpl_k4sw {V} := rsubI _ _ (@cplsw_I V).
Definition drs_cpl_k4 {V} := derl_mono (@rs_cpl_k4 V).
Definition drs_cpl_k4' {V} := derl_mono' (@rs_cpl_k4 V).
Definition drs_cpl_k4sw {V} := derl_mono (@rs_cpl_k4sw V).
Definition drs_cpl_k4sw' {V} := derl_mono' (@rs_cpl_k4sw V).
Definition spak4 {V} := rsub_trans (@rs_cpl_k4 V) (@rsub_adm _ _).
Definition spak4sw {V} := rsub_trans (@rs_cpl_k4sw V) (@rsub_adm _ _).
Definition dspak4 {V} := rsub_trans (@drs_cpl_k4 V) (@rsub_derl_adm _ _).
Definition dspak4sw {V} := rsub_trans (@drs_cpl_k4sw V) (@rsub_derl_adm _ _).
Definition ck4ak4 {V} := rsub_trans (@rsK4 V) (@rsub_adm _ _).
Definition ctrak4 {V} := rsub_trans (@rsK4_wk V) (@rsub_adm _ _).
Definition k4ak4 {V} := rsub_trans (@rsK4_sw V) (@rsub_adm _ _).
Definition rs_ImpR_k4 {V} := rsub_trans (@rsseqImpR V) (@rs_cpl_k4 V).
Definition rs_ImpL_k4 {V} := rsub_trans (@rsseqImpL V) (@rs_cpl_k4 V).
Definition rs_BotL_k4 {V} := rsub_trans (@rsseqBotL V) (@rs_cpl_k4 V).
Definition rs_ImpR_k4sw {V} := rsub_trans (@rsseqImpR V) (@rs_cpl_k4sw V).
Definition rs_ImpL_k4sw {V} := rsub_trans (@rsseqImpL V) (@rs_cpl_k4sw V).
Definition rs_BotL_k4sw {V} := rsub_trans (@rsseqBotL V) (@rs_cpl_k4sw V).

Lemma ImpLthm1 P (A B : PropF P) rules U V W X Y: 
  rsub (@Idrule _) rules -> rsub (@ImpLrule P) rules -> 
  derl (seqrule rules) [] (U ++ A :: V ++ Imp A B :: W, X ++ B :: Y).
Proof. intros rsid rsimpl.
eapply dtderI. eapply (Sctxt_eq _ _ _ [] (U ++ A :: V) W X (B :: Y)).
unfold rsub in rsimpl. apply rsimpl. apply ImpLrule_I.
list_assoc_r'. simpl. reflexivity.  simpl. reflexivity.  simpl. reflexivity.

apply seqrule_mono in rsid.  eapply dersl_mono'. apply rsid.
eapply dtCons_eq.  apply in_derl.  eapply (@sr_Id_alt _ B) ; solve_InT. 
eapply dtCons_eq.  apply in_derl.  eapply (@sr_Id_alt _ A) ; solve_InT.

apply dtNil.  simpl. reflexivity.  simpl. reflexivity. Qed.  

Lemma ImpLthm2 P (A B : PropF P) rules U V W X Y: 
  rsub (@Idrule _) rules -> rsub (@ImpLrule P) rules -> 
  derl (seqrule rules) [] (U ++ Imp A B :: V ++ A :: W, X ++ B :: Y).
Proof. intros rsid rsimpl.
eapply dtderI. eapply (Sctxt_eq _ _ _ [] U (V ++ A :: W) X (B :: Y)).
unfold rsub in rsimpl. apply rsimpl. apply ImpLrule_I.
list_assoc_r'. simpl. reflexivity.  simpl. reflexivity.  simpl. reflexivity.

apply seqrule_mono in rsid.  eapply dersl_mono'. apply rsid.
eapply dtCons_eq.  apply in_derl.  eapply (@sr_Id_alt _ B) ; solve_InT. 
eapply dtCons_eq.  apply in_derl.  eapply (@sr_Id_alt _ A) ; solve_InT.

apply dtNil.  simpl. reflexivity.  simpl. reflexivity. Qed.  

Definition ImpLthm1sr P (A B : PropF P) U V W X Y :=
  @ImpLthm1 P A B _ U V W X Y (@rsId _) (@rsImpL _).
Definition ImpLthm2sr P (A B : PropF P) U V W X Y :=
  @ImpLthm2 P A B _ U V W X Y (@rsId _) (@rsImpL _).

Definition derl_eq X rs ps c := @eq_rect X c (@derl X rs ps).

Definition ImpLthm1sreq P (A B : PropF P) U V W X Y :=
  derl_eq (@ImpLthm1sr P A B U V W X Y).
Definition ImpLthm2sreq P (A B : PropF P) U V W X Y :=
  derl_eq (@ImpLthm2sr P A B U V W X Y).

Definition dsidp X := rsubD (derl_mono (seqrule_mono (@rsId X))).
Definition sidp X := rsubD (seqrule_mono (@rsId X)).
Definition sbotp X := rsubD (seqrule_mono (@rsBotL X)).

Definition sr_pr_alt X A ant suc ina ins := 
  sidp (@sr_Id_alt (PropF X) A ant suc ina ins).

Definition dsr_pr_alt X A ant suc ina ins := 
  in_derl _ _ _ (@sr_pr_alt X A ant suc ina ins).

Lemma idrsgoal V rules A ant suc f: rsub (seqrule (@Idrule _)) rules ->
  InT A ant -> InT A suc -> {ps : list (Seql (PropF V)) &
  rules ps (ant, suc) * ForallT f ps}.
Proof. intros rs ina ins. eexists. split.  
unfold rsub in rs. apply rs.
apply (@sr_Id_alt _ A) ; assumption.  
apply ForallT_nil. Qed.

Definition rsidspr (V : Set) := seqrule_mono (@rsId V).
Definition rsiddspr (V : Set) := rsub_trans (@rsidspr V) (@rsub_derl _ _).

Definition rsidK4 (V : Set) := rsub_trans (@rsidspr V) (@rscpl V).
Definition rsidaK4 (V : Set) := rsub_trans (@rsidK4 V) (@rsub_adm _ _).

Definition ididrgoal V A ant suc f := @idrsgoal V _ A ant suc f (rsub_id _).
Definition iddsprgoal V A ant suc f := @idrsgoal V _ A ant suc f (@rsiddspr V).
Definition idsprgoal V A ant suc f := @idrsgoal V _ A ant suc f (@rsidspr V).
Definition idk4goal V A ant suc f := @idrsgoal V _ A ant suc f (@rsidK4 V).
Definition idak4goal V A ant suc f := @idrsgoal V _ A ant suc f (@rsidaK4 V).

Definition rsbotK4 (V : Set) := 
  rsub_trans (seqrule_mono (@rsBotL V)) (@rscpl V).
Definition rsbotaK4 (V : Set) := rsub_trans (@rsbotK4 V) (@rsub_adm _ _).

Lemma botrsgoal V rules ant suc f: rsub (seqrule (@Botrule V)) rules ->
  InT (@Bot _) ant -> {ps : list (Seql (PropF V)) &
  rules ps (ant, suc) * ForallT f ps}.
Proof. intros rs ia. eexists. split.  2: apply ForallT_nil.
unfold rsub in rs. apply rs.
apply InT_split in ia. cD. subst. 
eapply (Sctxt_eq _ _ [@Bot V] []).
apply Botrule_I. simpl. reflexivity. 
simpl. symmetry. apply app_nil_l.  simpl. reflexivity. Qed.

Definition botspgoal V ant suc f := 
  @botrsgoal V _ ant suc f (seqrule_mono (@rsBotL V)).
Definition botk4goal V ant suc f := @botrsgoal V _ ant suc f (@rsbotK4 V).
Definition botak4goal V ant suc f := @botrsgoal V _ ant suc f (@rsbotaK4 V).

Lemma psnilagoal W rules seq f : derl rules [] seq ->
  {ps : list W & adm rules ps seq * ForallT f ps}.
Proof. intro drs. exists []. split. 2 : apply ForallT_nil. 
apply derl_sub_adm. exact drs. Qed.

Lemma sig_in_cons W fr any (seq1 seq2 : W) seqs: fr [seq1 : W] seq2 ->
  {ps : list W & fr ps seq2 *
  ForallT (fun p' => {p : W & InT p (seq1 :: seqs) * clos_reflT any p p'}) ps}.
Proof. intro. eexists. split. eassumption.  
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl. Qed.

Lemma sig_in_cons2 W fr any (seq0 seq1 seq2 : W) seqs: fr [seq1 : W] seq2 ->
  {ps : list W & fr ps seq2 *
  ForallT (fun p' => {p : W & InT p (seq0 :: seq1 :: seqs) * 
    clos_reflT any p p'}) ps}.
Proof. intro. eexists. split. eassumption.  
apply ForallT_singleI. eexists. split.
apply InT_cons. apply InT_eq. apply rT_refl. Qed.

Lemma admK4exchR V ant suc suc': swapped suc' suc ->
  adm (@K4rules V) [(ant, suc')] (ant, suc).
Proof. intros sw. apply admI. intro drs. apply dersrec_singleD in drs.
eapply exchR_K4. apply drs. apply snd_relI. apply sw. Qed.

Lemma admK4exchL V ant ant' suc: swapped ant' ant ->
  adm (@K4rules V) [(ant', suc)] (ant, suc).
Proof. intros sw. apply admI. intro drs. apply dersrec_singleD in drs.
eapply exchL_K4. apply drs. apply fst_relI. apply sw. Qed.

Lemma admK4swexchR V ant suc suc': swapped suc' suc ->
  adm (@K4rules_sw V) [(ant, suc')] (ant, suc).
Proof. intros sw. apply admI. intro drs. apply dersrec_singleD in drs.
eapply exchR_K4_sw. apply drs. apply snd_relI. apply sw. Qed.

Lemma admK4swexchL V ant ant' suc: swapped ant' ant ->
  adm (@K4rules_sw V) [(ant', suc)] (ant, suc).
Proof. intros sw. apply admI. intro drs. apply dersrec_singleD in drs.
eapply exchL_K4_sw. apply drs. apply fst_relI. apply sw. Qed.

Lemma can_trf_ImpRinv_k4 V ps c: @K4prrule _ ps c ->
  can_trf_rules_rc (seqrel (@ImpRinv V)) (@K4prrule _) ps c.
Proof. intros k4.  inversion k4. clear k4. subst.
unfold can_trf_rules_rc.
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
inversion iri. clear iri. subst.
unfold seqext in *. 
inversion seo. clear seo. subst.
list_eq_ncT. sD. injection H2 as . discriminate H. list_eq_ncT.
Qed.

(* TODO generalise these next three 
but note following doesn't work because U could be introduced by the
weakening and S not, or vv 
Lemma can_trf_geninv_wk W invrel ps c: 
  (forall p (U S : list W), invrel (U, S) p -> sing_empty U * sing_empty S) -> 
  cgerule (@trivrule _) ps c ->
  can_trf_rules_rc (seqrel invrel) (cgerule (@trivrule _)) ps c.
*)

Lemma from_one_ImpLinv1 V: rsub (@ImpLinv1 V) (@from_one_fml _).
Proof.  unfold rsub. intros. destruct H. apply fofI. apply singL. Qed.
Lemma from_one_ImpLinv2 V: rsub (@ImpLinv2 V) (@from_one_fml _).
Proof.  unfold rsub. intros. destruct H. apply fofI. apply singL. Qed.
Lemma from_one_ImpRinv V: rsub (@ImpRinv V) (@from_one_fml _).
Proof.  unfold rsub. intros. destruct H. apply fofI. apply singR. Qed.

Lemma can_trf_geninv_wk W invrel ps (c : Seql W): 
  rsub invrel (@from_one_fml _) -> cgerule (@trivrule _) ps c ->
  can_trf_rules_rc (seqrel invrel) (cgerule (@trivrule _)) ps c.
Proof. intros rsi cgt. inversion_clear cgt as [? ? ? ? ? t ga gs].
inversion t. clear t. subst.
unfold can_trf_rules_rc.
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri.
destruct c0. destruct c'0.  unfold seqext in seo. injection seo as . subst.
pose iri as iri'. eapply (rsubD rsi) in iri'.  
inversion iri'. subst.  clear iri'.
inversion X ; subst ; clear X ; simpl in ga ; simpl in gs ;
apply gen_ext_splitR in gs ; cD ; subst ;
apply gen_ext_splitR in ga ; cD ; subst.
- inversion ga3 ; subst ; clear ga3 ; eexists ; split.
all: cycle 1.
eapply ForallT_singleI ; eexists ; split ; [ apply InT_eq | apply rT_step ].
eapply Sctxt_relI_eq. apply iri.  simpl. reflexivity.  reflexivity.
all: cycle -1.
eapply CGctxt. apply trivrule_I.
repeat (assumption || apply gen_ext_refl || apply gen_ext_app).
repeat (assumption || apply gen_ext_refl || apply gen_ext_app).
all: cycle 1.
eapply ForallT_singleI ; eexists ; split ; [ apply InT_eq | apply rT_refl ].
eapply CGctxt. apply trivrule_I.
apply gen_ext_app.  apply gen_ext_appL.  assumption.  assumption.
apply gen_ext_app.  apply gen_ext_appL.  assumption.  assumption.
- inversion gs3 ; subst ; clear gs3 ; eexists ; split.
all: cycle 1.
eapply ForallT_singleI ; eexists ; split ; [ apply InT_eq | apply rT_step ].
eapply Sctxt_relI_eq. apply iri.  simpl. reflexivity.  reflexivity.
all: cycle -1.
eapply CGctxt. apply trivrule_I.
repeat (assumption || apply gen_ext_refl || apply gen_ext_app).
repeat (assumption || apply gen_ext_refl || apply gen_ext_app).
all: cycle 1.
eapply ForallT_singleI ; eexists ; split ; [ apply InT_eq | apply rT_refl ].
eapply CGctxt. apply trivrule_I.
apply gen_ext_app.  apply gen_ext_appL.  assumption.  assumption.
apply gen_ext_app.  apply gen_ext_appL.  assumption.  assumption.
Qed.

Definition can_trf_ImpLinv1_wk V ps c :=
  @can_trf_geninv_wk _ _ ps c (@from_one_ImpLinv1 V).
Definition can_trf_ImpLinv2_wk V ps c :=
  @can_trf_geninv_wk _ _ ps c (@from_one_ImpLinv2 V).
Definition can_trf_ImpRinv_wk V ps c :=
  @can_trf_geninv_wk _ _ ps c (@from_one_ImpRinv V).

Definition can_trf_ImpRinv_wk_ak4 V ps c (cgtr : cgerule (@trivrule _) ps c) :=
  can_trf_rules_rc_mono' (@ctrak4 V) (can_trf_ImpRinv_wk cgtr).
Definition can_trf_ImpLinv1_wk_ak4 V ps c (cgtr : cgerule (@trivrule _) ps c) :=
  can_trf_rules_rc_mono' (@ctrak4 V) (can_trf_ImpLinv1_wk cgtr).
Definition can_trf_ImpLinv2_wk_ak4 V ps c (cgtr : cgerule (@trivrule _) ps c) :=
  can_trf_rules_rc_mono' (@ctrak4 V) (can_trf_ImpLinv2_wk cgtr).

Lemma can_trf_ImpRinv_ck4 V ps c: cgerule (@K4prrule _) ps c ->
  can_trf_rules_rc (seqrel (@ImpRinv V)) (cgerule (@K4prrule _)) ps c.
Proof. intros cgk4.  inversion_clear cgk4 as [? ? ? ? ? k4 ga gs].
inversion k4. clear k4. subst.
unfold can_trf_rules_rc.
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
inversion iri. clear iri. subst.
unfold seqext in *. 
inversion seo. clear seo. subst.
eexists. split.
2: eapply ForallT_singleI.
2: eexists. 2: split. 2: apply InT_eq. 2: apply rT_refl.
eapply CGctxt. apply K4prrule_I.
eapply gen_ext_trans. 2: eassumption.
apply gen_ext_app. simpl. apply gen_ext_extra. 
apply gen_ext_refl.  apply gen_ext_refl.
apply gen_ext_splitR in gs. cD.
list_eq_ncT. sD. subst.
inversion gs3. subst.
rewrite app_assoc. apply gen_ext_appL. assumption.
subst. apply gen_ext_appR. assumption.
Qed.

Definition can_trf_ImpRinv_ck4_ak4 V ps c (cgk4 : cgerule (@K4prrule V) ps c) :=
  can_trf_rules_rc_mono' (@ck4ak4 V) (can_trf_ImpRinv_ck4 cgk4).

Definition can_trf_ImpRinv_k4_ak4 V ps c (cgk4 : K4prrule ps c) :=
  can_trf_rules_rc_mono' (@k4ak4 V) (can_trf_ImpRinv_k4 cgk4).

(* last rule is Id rule *)
Lemma can_trf_ImpRinv_Id_dspr V Φ1 Φ2 Ψ1 Ψ2 ps c: Idrule ps c ->
  can_trf_rules_rc (seqrel (@ImpRinv V)) (derl (seqrule (@princrule V))) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. intros id.  destruct id. simpl. 
unfold can_trf_rules_rc. 
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
inversion iri. subst. clear iri. 
simpl in seo. injection seo as .
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 12 subgoals *)
(* some goals have identity formula on right inverted,
  so are A0, A0 -> B |- B
  some simply have A on both sides *)
- (* identity formula on right inverted *)
eexists. split.
eapply (ImpLthm1sreq _ _ _ [] _ _ _).
simpl.  reflexivity. apply ForallT_nil.

- (* identity formula on right inverted *)
eexists. split.
eapply (ImpLthm2sreq _ _ _ _ _ _ _).  list_assoc_r'.  reflexivity. 
apply ForallT_nil.

- apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)
- apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

- (* identity formula on right inverted *)
eexists. split.
eapply (ImpLthm1sreq _ _ _ _ _ _ _).  reflexivity.
apply ForallT_nil.

- apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

- (* identity formula on right inverted *)
eexists. split.
eapply (ImpLthm1sreq _ _ _ [] _ _ _).  simpl.  reflexivity.
apply ForallT_nil.  

- (* identity formula on right inverted *)
eexists. split.
eapply (ImpLthm2sreq _ _ _ _ _ _ _).  list_assoc_r'.  reflexivity.
apply ForallT_nil.

- apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)
- apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

- (* identity formula on right inverted *)
eexists. split.
eapply (ImpLthm1sreq _ _ _ _ _ _ _).  reflexivity.
apply ForallT_nil.

- apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)
Qed.

Definition can_trf_ImpRinv_Id_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' dspak4
  (@can_trf_ImpRinv_Id_dspr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).
Check can_trf_ImpRinv_Id_ak4.

Definition can_trf_ImpRinv_Id_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' dspak4sw
  (@can_trf_ImpRinv_Id_dspr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).
Check can_trf_ImpRinv_Id_ak4sw.

(* sqr_simp, eg from seqrel (del_relR (Bot V))
    (Φ0 ++ A :: H ++ Φ2, Ψ0 ++ B :: H2 ++ Bot V :: Ψ2)
    (Φ0 ++ A :: H ++ Φ2, Ψ0 ++ B :: H2 ++ Ψ2)
    to seqrel (del_relR (Bot V)) ([], [Bot V]) ([], []) *)
Ltac sqr_simp := 
list_assoc_r ; repeat (apply sqr_appL1 || apply sqr_appL2 || 
  apply sqr_cons1 || apply sqr_cons2) ;
list_assoc_l ; repeat (apply sqr_appR1 || apply sqr_appR2) ;
repeat (apply sqr_cons_app1 || apply sqr_cons_app2 ||
  apply sqr_app_cons1 || apply sqr_app_cons2) ;
repeat (apply sqr_cons_na1 || apply sqr_cons_na2 ||
  apply sqr_na_cons1 || apply sqr_na_cons2) ;
repeat (apply sqr_nn1 || apply sqr_nn2 || apply sqr_cc1 || apply sqr_cc2) ;
repeat (apply sqr_asL1 || apply sqr_asL2 || apply sqr_asR1 || apply sqr_asR2 ||
  apply sqr_saL1 || apply sqr_saL2 || apply sqr_saR1 || apply sqr_saR2).

Ltac apply2 th1 th2 := apply th1 || apply th2.

Ltac sqr_simpf applyf  := 
list_assoc_r ; repeat (applyf sqr_appL1 || applyf sqr_appL2 || 
  applyf sqr_cons1 || applyf sqr_cons2) ;
list_assoc_l ; repeat (applyf sqr_appR1 || applyf sqr_appR2) ;
repeat (applyf sqr_cons_app1 || applyf sqr_cons_app2 ||
  applyf sqr_app_cons1 || applyf sqr_app_cons2) ;
repeat (applyf sqr_cons_na1 || applyf sqr_cons_na2 ||
  applyf sqr_na_cons1 || applyf sqr_na_cons2) ;
repeat (applyf sqr_nn1 || applyf sqr_nn2 || applyf sqr_cc1 || applyf sqr_cc2).

(* Ltac sqr_simps th1 := sqr_simpf (ltac:(apply2) th1).  *)
Ltac sqr_simps th1 := sqr_simpf (ltac:(fun th2 => apply2 th1 th2)).

Ltac sqr_simpt th1  := 
list_assoc_r ; repeat (apply2 th1 sqr_appL1 || apply2 th1 sqr_appL2 || 
  apply2 th1 sqr_cons1 || apply2 th1 sqr_cons2) ;
list_assoc_l ; repeat (apply2 th1 sqr_appR1 || apply2 th1 sqr_appR2) ;
repeat (apply2 th1 sqr_cons_app1 || apply2 th1 sqr_cons_app2 ||
  apply2 th1 sqr_app_cons1 || apply2 th1 sqr_app_cons2) ;
repeat (apply2 th1 sqr_cons_na1 || apply2 th1 sqr_cons_na2 ||
  apply2 th1 sqr_na_cons1 || apply2 th1 sqr_na_cons2) ;
repeat (apply2 th1 sqr_nn1 || apply2 th1 sqr_nn2 || 
  apply2 th1 sqr_cc1 || apply2 th1 sqr_cc2).

(* problem here, can't do exactly as can_trf_R_L
  because adm _ not monotonic, so can't get 
  can_trf_rules_rc ... (adm (seqrule (singleton_rel psr ([], [Ui])))) ... 
  gives can_trf_rules_rc ... (adm (@K4rules V)) ...
  and require admissibility because exchange is required when the 
  rule inverted is the last rule, but with the context arranged differently *)

(* last rule is ImpRrule, two cases as to whether same or different
  implication is inverted *)
(* problem here, requires admissibility of exchange, 
  so cannot use monotonocity of can_trf_rules_rc and a more general result *)

Lemma can_trf_ImpRinv_ImpR V rules Φ1 Φ2 Ψ1 Ψ2 ps c 
  (adm_exchL : forall (ant ant' suc : list (PropF V)),
    swapped ant' ant -> adm rules [(ant', suc)] (ant, suc)):
  rsub (seqrule (@ImpRrule V)) rules -> ImpRrule ps c ->
  can_trf_rules_rc (seqrel ImpRinv) (adm rules) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. intros rs impr.  destruct impr. simpl. 
unfold can_trf_rules_rc. 
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
destruct iri.
unfold seqext.  simpl in seo. simpl. 
injection seo as . subst.
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r.
* (* simply a case of exchange *)
apply sig_in_cons.  apply adm_exchL.  swap_tac_Rc.
* eexists. split. apply in_adm. apply (rsubD rs).
eapply (Sctxt_eq _ _ [] [Imp A B] Φ1 (H ++ C :: Φ3) Ψ1 (H2 ++ D :: Ψ3)).
try apply ImpR. apply ImpRrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_singleI. eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpRinv_I.
* (* simply a case of exchange *)
apply sig_in_cons.  apply adm_exchL.  swap_tac_Rc.
* eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [] [Imp A B] (Φ0 ++ C :: H) Φ2 Ψ1 (H2 ++ D :: Ψ3)).
try apply ImpR. apply ImpRrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_singleI. eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpRinv_I.
* (* simply a case of exchange *)
apply sig_in_cons.  apply adm_exchL.  swap_tac_Rc.
* eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [] [Imp A B] Φ1 (H ++ C :: Φ3) (Ψ0 ++ D :: H2) Ψ2).
try apply ImpR. apply ImpRrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_singleI. eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpRinv_I.
* (* simply a case of exchange *)
apply sig_in_cons.  apply adm_exchL.  swap_tac_Rc.
* eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [] [Imp A B] (Φ0 ++ C :: H) Φ2 (Ψ0 ++ D :: H2) Ψ2).
try apply ImpR. apply ImpRrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_singleI. eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpRinv_I.
Qed.

Check can_trf_ImpRinv_ImpR.

Definition can_trf_ImpRinv_ImpR_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c :=
  @can_trf_ImpRinv_ImpR V _ Φ1 Φ2 Ψ1 Ψ2 ps c (@admK4exchL _) (@rs_ImpR_k4 _).
Definition can_trf_ImpRinv_ImpR_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c :=
  @can_trf_ImpRinv_ImpR V _ Φ1 Φ2 Ψ1 Ψ2 ps c 
    (@admK4swexchL _) (@rs_ImpR_k4sw _).
Check can_trf_ImpRinv_ImpR_ak4.  Check can_trf_ImpRinv_ImpR_ak4sw.

(* last rule is Botrule *)
Lemma can_trf_ImpRinv_BotL_spr V Φ1 Φ2 Ψ1 Ψ2 ps c: Botrule ps c ->
  can_trf_rules_rc (seqrel ImpRinv) (seqrule (@princrule V)) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. intros bot.  destruct bot. simpl. 
unfold can_trf_rules_rc.  intros c' sri.
inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
destruct iri.
unfold seqext. simpl in seo. simpl. 
injection seo as . subst.
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 9 subgoals *)
apply botspgoal ; solve_InT. Qed.

Definition can_trf_ImpRinv_BotL_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' spak4
  (@can_trf_ImpRinv_BotL_spr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).

Definition can_trf_ImpRinv_BotL_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' spak4sw
  (@can_trf_ImpRinv_BotL_spr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).

Check can_trf_ImpRinv_BotL_ak4.  Check can_trf_ImpRinv_BotL_ak4sw.

Definition sceqsr W ps ca cs U V Φ1 Φ2 Ψ1 Ψ2 cae cse := 
  @Sctxt_eq W _ ps _ ca cs U V Φ1 Φ2 Ψ1 Ψ2 (srI _ _) cae cse eq_refl.

Definition screqsr W X Y U V Φ1 Φ2 Ψ1 Ψ2 seq1 seq2 :=
  @Sctxt_relI_eq W _ X Y U V Φ1 Φ2 Ψ1 Ψ2 seq1 seq2 (srI _ _).
  
(* to replace the various apply screqsr ... steps *)
Ltac screqsr_auto := apply seq_ssD ; 
list_assoc_r ; repeat (apply ss_appL || apply ss_cons) ;
try (apply ss_appLe1 || apply ss_appLe2) ;
list_assoc_l ; repeat (apply ss_appR || apply ss_cons) ;
try (apply ss_appRe1 || apply ss_appRe2) ;
try (apply ss_app_cons1 || apply ss_app_cons2) ;
try apply ss_id ; apply srI.

Inductive is_nil A : list A -> Type := is_nilI: is_nil [].

Lemma is_nil_app A (U V : list A): is_nil (U ++ V) -> is_nil U * is_nil V.
Proof. intro isn. inversion isn as [nea]. apply nil_eq_app in nea.
  destruct nea. subst. split ; apply is_nilI. Qed.

Lemma is_nil_eqI A (U : list A): U = [] -> is_nil U.
Proof. intro. subst. apply is_nilI. Qed.
Lemma is_nil_eqI' A (U : list A): [] = U -> is_nil U.
Proof. intro. subst. apply is_nilI. Qed.

Ltac mk_is_nil := 
  match goal with
    | [ H : _ = [] |- _ ] => apply is_nil_eqI in H
    | [ H : [] = _ |- _ ] => apply is_nil_eqI' in H
    end.

Ltac is_nilE :=
  match goal with
    | [ H : is_nil (_ :: _) |- _ ] => inversion H
    | [ H : is_nil (_ ++ _) |- _ ] => apply is_nil_app in H ; destruct H
    | [ H : is_nil [] |- _ ] => clear H
    end.

Ltac is_nilD :=
  match goal with
    | [ H : is_nil _ |- _ ] => destruct H
    end.

Ltac ssL1ex H0 := 
  tryif (apply (ssrule_testL1 H0)) then idtac else (apply ssrule_appL1).
Ltac ssR1ex H0 := 
  tryif (apply (ssrule_testR1 H0)) then idtac else (apply ssrule_appR1).
Ltac ssL2ex H0 := 
  tryif (apply (ssrule_testL2 H0)) then idtac else (apply ssrule_appL2).
Ltac ssR2ex H0 := 
  tryif (apply (ssrule_testR2 H0)) then idtac else (apply ssrule_appR2).

Ltac sceqsr2_auto H0 :=
  list_assoc_r ; repeat ssL2ex H0 ; repeat (apply ssrule_appL1) ;
  list_assoc_l ; repeat ssR2ex H0 ; repeat (apply ssrule_appR1) ;
  try apply ssrule_appR1c ;  try apply ssrule_appR2c ;
  apply seqrule_id ; apply srI.

Ltac sceqsr1_auto H :=
  list_assoc_r ; repeat ssL1ex H ; repeat (apply ssrule_appL2) ;
  list_assoc_l ; repeat ssR1ex H ; repeat (apply ssrule_appR2) ;
  try apply ssrule_appR1c ;  try apply ssrule_appR2c ;
  apply seqrule_id ; apply srI.

Ltac betw_ss int := 
  rewrite ?map_seqext_seqext ; simpl ; rewrite ?app_nil_r ;
  apply ForallTI_forall ; intros x inxms ; apply InT_mapE in inxms ; cD ;
  rename_last int ; eexists ; split ; 
  [ eapply InT_map in int ; apply int |
  destruct inxms as [ya ys] ;  subst ; simpl ].

(* try to generalise can_trf_ImpRinv_ImpL 
  this generalisation involves simple cases where the inference rule 
  and the inversion rule are simply all extensions of particular sequents *)
(* try doing it like this to make it easier to work out arguments for
  sceqsr in eapply (sceqsr ...) - doesn't always work easily because N can
  be substituted for [] or H0 ++ []; if the latter
  could simply use the argument of is_nil,
  so at present this looks good except for 3 goals where it seems N is shown
  to be empty *)

Lemma can_trf_R_L' V Φ1 Φ2 Ψ1 Ψ2 psr Sr pi Ui N: is_nil N -> 
  can_trf_rules (seqrel (singleton_rel ([], [Sr : V]) pi)) 
    (seqrule (singleton_rel psr ([Ui : V], N)))
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) psr) (seqext Φ1 Φ2 Ψ1 Ψ2 ([Ui], N)).
Proof. intro isn. unfold can_trf_rules. intros c' sss. 
inversion sss. clear sss. destruct H0. subst.
destruct pi as [pia pis]. unfold seqext.
unfold seqext in H. injection H as .
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
rewrite ?app_nil_r in isn ; simpl in isn ; repeat is_nilE. 

* eexists. split.  sceqsr2_auto H0.  betw_ss int.  screqsr_auto.
* eexists. split.  sceqsr2_auto H0.  betw_ss int.  screqsr_auto.
* eexists. split.  sceqsr2_auto H0.  betw_ss int.  screqsr_auto.
* eexists. split.  sceqsr2_auto N.  betw_ss int.  screqsr_auto.
* eexists. split.  sceqsr2_auto N.  betw_ss int.  screqsr_auto.
* eexists. split.  sceqsr2_auto N.  betw_ss int.  screqsr_auto.

* eexists. split.  
eapply (sceqsr _ [Ui] [] (Φ1 ++ pia) Φ2 Ψ0 (pis ++ Ψ3)) ;
  simpl ; list_assoc_r ; reflexivity.
betw_ss int.  screqsr_auto.

* eexists. split.  
eapply (sceqsr _ [Ui] [] Φ1 (H4 ++ pia ++ Φ3) Ψ0 (pis ++ Ψ3)) ;
  simpl ; list_assoc_r ; reflexivity.
betw_ss int.  screqsr_auto.

* eexists. split.  sceqsr2_auto N.  betw_ss int.  screqsr_auto.
* eexists. split.  sceqsr2_auto N.  betw_ss int.  screqsr_auto.

* eexists. split.
eapply (sceqsr _ [Ui] [] (Φ0 ++ pia ++ H) Φ2 Ψ0 (pis ++ Ψ3)) ;
  simpl ; list_assoc_r ; reflexivity.
betw_ss int.  screqsr_auto.

* eexists. split.  sceqsr2_auto N.  betw_ss int.  screqsr_auto.
Qed.

Definition can_trf_R_L V Φ1 Φ2 Ψ1 Ψ2 psr Sr pi Ui :=
  @can_trf_R_L' V Φ1 Φ2 Ψ1 Ψ2 psr Sr pi Ui [] (is_nilI _).

(* former proof, just the sceqsr and screqsr steps shown, 
  which correspond to sceqsr_auto and screqsr_auto in newer proof 
eapply (sceqsr _ [Ui] [] (Φ1 ++ pia) Φ2 Ψ1 (H0 ++ pis ++ Ψ3)) ;
apply (screqsr [] [Sr] pia pis Φ1 (ya ++ Φ2) (Ψ1 ++ ys ++ H0) Ψ3) ;
eapply (sceqsr _ [Ui] [] Φ1 (H4 ++ pia ++ Φ3) Ψ1 (H0 ++ pis ++ Ψ3)) ;
apply (screqsr [] [Sr] pia pis (Φ1 ++ ya ++ H4) Φ3 (Ψ1 ++ ys ++ H0) Ψ3) ;
eapply (sceqsr _ [Ui] [] (Φ0 ++ pia ++ H) Φ2 Ψ1 (H0 ++ pis ++ Ψ3)) ;
apply (screqsr [] [Sr] pia pis Φ0 (H ++ ya ++ Φ2) (Ψ1 ++ ys ++ H0) Ψ3) ;
eapply (sceqsr _ [Ui] [] (Φ1 ++ pia) Φ2 Ψ0 (pis ++ Ψ3)) ;
apply (screqsr [] [Sr] pia pis Φ1 (ya ++ Φ2) (Ψ0 ++ ys) Ψ3) ; 
eapply (sceqsr _ [Ui] [] Φ1 (H4 ++ pia ++ Φ3) Ψ0 (pis ++ Ψ3)) ;
apply (screqsr [] [Sr] pia pis (Φ1 ++ ya ++ H4) Φ3 (Ψ0 ++ ys) Ψ3) ;
eapply (sceqsr _ [Ui] [] (Φ1 ++ pia) Φ2 (Ψ0 ++ pis ++ H2) Ψ2) ;
apply (screqsr [] [Sr] pia pis Φ1 (ya ++ Φ2) Ψ0 (H2 ++ ys ++ Ψ2)) ; 
eapply (sceqsr _ [Ui] [] Φ1 (H4 ++ pia ++ Φ3) (Ψ0 ++ pis ++ H2) Ψ2) ;
apply (screqsr [] [Sr] pia pis (Φ1 ++ ya ++ H4) Φ3 Ψ0 (H2 ++ ys ++ Ψ2)) ;
eapply (sceqsr _ [Ui] [] (Φ0 ++ pia ++ H) Φ2 Ψ0 (pis ++ Ψ3)) ;
apply (screqsr [] [Sr] pia pis Φ0 (H ++ ya ++ Φ2) (Ψ0 ++ ys) Ψ3) ;
eapply (sceqsr _ [Ui] [] (Φ0 ++ pia ++ H) Φ2 (Ψ0 ++ pis ++ H2) Ψ2) ;
apply (screqsr [] [Sr] pia pis Φ0 (H ++ ya ++ Φ2) Ψ0 (H2 ++ ys ++ Ψ2)) ;
Qed.
*)

Check can_trf_R_L.

Lemma can_trf_L_R' V Φ1 Φ2 Ψ1 Ψ2 psr Sr pi Ui N: is_nil N ->
  can_trf_rules (seqrel (singleton_rel ([Sr : V], []) pi)) 
    (seqrule (singleton_rel psr (N, [Ui : V])))
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) psr) (seqext Φ1 Φ2 Ψ1 Ψ2 (N, [Ui])).
Proof. intro isn. unfold can_trf_rules. intros c' sss. 
inversion sss. clear sss. destruct H0. subst.
destruct pi as [pia pis]. unfold seqext.
unfold seqext in H. injection H as .
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
rewrite ?app_nil_r in isn ; simpl in isn ; repeat is_nilE. 

- eexists. split.  sceqsr1_auto H.  betw_ss int.  screqsr_auto.
- eexists. split.  sceqsr1_auto H.  betw_ss int.  screqsr_auto.
- eexists. split.  sceqsr1_auto N.  betw_ss int.  screqsr_auto.
- eexists. split.  sceqsr1_auto N.  betw_ss int.  screqsr_auto.

- eexists. split. 
eapply (sceqsr _ [] [Ui] Φ0 (pia ++ Φ3) (Ψ1 ++ pis) Ψ2) ;
  simpl ; list_assoc_r ; reflexivity.
betw_ss int.  screqsr_auto.

- eexists. split.  sceqsr1_auto N.  betw_ss int.  screqsr_auto.

- eexists. split. 
eapply (sceqsr _ [] [Ui] Φ0 (pia ++ Φ3) Ψ1 (H2 ++ pis ++ Ψ3)) ;
  simpl ; list_assoc_r ; reflexivity.
betw_ss int.  screqsr_auto.

- eexists. split.  sceqsr1_auto N.  betw_ss int.  screqsr_auto.
- eexists. split.  sceqsr1_auto H.  betw_ss int.  screqsr_auto.
- eexists. split.  sceqsr1_auto N.  betw_ss int.  screqsr_auto.

- eexists. split. 
eapply (sceqsr _ [] [Ui] Φ0 (pia ++ Φ3) (Ψ0 ++ pis ++ H0) Ψ2) ;
  simpl ; list_assoc_r ; reflexivity.
betw_ss int.  screqsr_auto.

- eexists. split.  sceqsr1_auto N.  betw_ss int.  screqsr_auto.
Qed.

Definition can_trf_L_R V Φ1 Φ2 Ψ1 Ψ2 psr Sr pi Ui :=
  @can_trf_L_R' V Φ1 Φ2 Ψ1 Ψ2 psr Sr pi Ui [] (is_nilI _).

(* old proof of can_trf_L_R - instead of using sceqsr1_auto and screqsr_auto.
  used the following
eapply (sceqsr _ [] [Ui] Φ1 (H ++ pia ++ Φ3) (Ψ1 ++ pis) Ψ2) ;
apply (screqsr [Sr] [] pia pis (Φ1 ++ ya ++ H) Φ3 Ψ1 (ys ++ Ψ2)) ;
eapply (sceqsr _ [] [Ui] Φ1 (H ++ pia ++ Φ3) Ψ1 (H2 ++ pis ++ Ψ3)) ;
apply (screqsr [Sr] [] pia pis (Φ1 ++ ya ++ H) Φ3 (Ψ1 ++ ys ++ H2) Ψ3) ;
eapply (sceqsr _ [] [Ui] Φ0 (pia ++ Φ3) (Ψ1 ++ pis) Ψ2) ;
apply (screqsr [Sr] [] pia pis (Φ0 ++ ya) Φ3 Ψ1 (ys ++ Ψ2)) ;
eapply (sceqsr _ [] [Ui] (Φ0 ++ pia ++ H4) Φ2 (Ψ1 ++ pis) Ψ2) ;
apply (screqsr [Sr] [] pia pis Φ0 (H4 ++ ya ++ Φ2) Ψ1 (ys ++ Ψ2)) ;
eapply (sceqsr _ [] [Ui] Φ0 (pia ++ Φ3) Ψ1 (H2 ++ pis ++ Ψ3)) ;
apply (screqsr [Sr] [] pia pis (Φ0 ++ ya) Φ3 (Ψ1 ++ ys ++ H2) Ψ3) ;
eapply (sceqsr _ [] [Ui] (Φ0 ++ pia ++ H4) Φ2 Ψ1 (H2 ++ pis ++ Ψ3)) ;
apply (screqsr [Sr] [] pia pis Φ0 (H4 ++ ya ++ Φ2) (Ψ1 ++ ys ++ H2) Ψ3) ;
eapply (sceqsr _ [] [Ui] Φ1 (H ++ pia ++ Φ3) (Ψ0 ++ pis ++ H0) Ψ2) ;
apply (screqsr [Sr] [] pia pis (Φ1 ++ ya ++ H) Φ3 Ψ0 (H0 ++ ys ++ Ψ2)) ;
eapply (sceqsr _ [] [Ui] Φ0 (pia ++ Φ3) (Ψ0 ++ pis ++ H0) Ψ2) ;
apply (screqsr [Sr] [] pia pis (Φ0 ++ ya) Φ3 Ψ0 (H0 ++ ys ++ Ψ2)) ;
eapply (sceqsr _ [] [Ui] (Φ0 ++ pia ++ H4) Φ2 (Ψ0 ++ pis ++ H0) Ψ2) ;
apply (screqsr [Sr] [] pia pis Φ0 (H4 ++ ya ++ Φ2) Ψ0 (H0 ++ ys ++ Ψ2)) ;
*)

Check can_trf_L_R.

Definition can_trf_rules_req_sr W rulesi (rules : rlsT (Seql W)) :=
  @can_trf_rules_req _ _ _ rules (req_sym (rsr_rusr rulesi)).

(* last rule is ImpLrule *)
Lemma can_trf_ImpRinv_ImpL_an V Φ1 Φ2 Ψ1 Ψ2 ps c (ipc : ImpLrule ps c) : 
  can_trf_rules (seqrel ImpRinv) (seqrule (@princrule V)) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. apply can_trf_rules_req_sr. apply can_trf_rules_Un.
intros r isr.  inversion_clear isr. destruct X. destruct i. destruct ipc.
eapply can_trf_rules_mono'.  2: apply can_trf_R_L.
apply rsubI. intros. inversion X.  inversion H. 
apply Sctxt.  apply ImpL. apply ImpLrule_I. Qed.

Check can_trf_ImpRinv_ImpL_an.

Definition can_trf_ImpRinv_ImpL_a V Φ1 Φ2 Ψ1 Ψ2 ps c i :=
  can_trf_rules_imp_rc (@can_trf_ImpRinv_ImpL_an V Φ1 Φ2 Ψ1 Ψ2 ps c i).

(* could do this for derl *)
Definition can_trf_ImpRinv_ImpL_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c i :=
  can_trf_rules_rc_mono' spak4
  (@can_trf_ImpRinv_ImpL_a V Φ1 Φ2 Ψ1 Ψ2 ps c i).

Definition can_trf_ImpRinv_ImpL_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c i :=
  can_trf_rules_rc_mono' spak4sw
  (@can_trf_ImpRinv_ImpL_a V Φ1 Φ2 Ψ1 Ψ2 ps c i).

Check can_trf_ImpRinv_ImpL_ak4.  Check can_trf_ImpRinv_ImpL_ak4sw.
(*
problem with using can_trf_rules_rc for this because in the case
where the last rule is also ImpR, on the same implicational formula A -> B,
the use of the rule may be different because it may put the A into
a different spot in the antecedent of the premise;
so we want admissibility, not derivability, 
and use admissibility of exchange *)

Lemma can_trf_ImpRinv_ak4 V ps c: @K4rules V ps c ->
  can_trf_rules_rc (seqrel ImpRinv) (adm (@K4rules V)) ps c.
Proof. intro k4. destruct k4. 
apply can_trf_ImpRinv_ck4_ak4. assumption. 
destruct s. destruct p. (* 4 cases for 4 rules *)
+ apply can_trf_ImpRinv_Id_ak4. assumption. 
+ apply can_trf_ImpRinv_ImpR_ak4. assumption. 
+ apply can_trf_ImpRinv_ImpL_ak4. assumption. 
+ apply can_trf_ImpRinv_BotL_ak4. assumption. Qed.

Lemma can_trf_ImpRinv_ak4sw V ps c: @K4rules_sw V ps c ->
  can_trf_rules_rc (seqrel ImpRinv) (adm (@K4rules_sw V)) ps c.
Proof. intro k4. destruct k4. 
- apply can_trf_ImpRinv_k4_ak4. assumption. 
- destruct s. destruct p. (* 4 cases for 4 rules *)
+ apply can_trf_ImpRinv_Id_ak4sw. assumption. 
+ apply can_trf_ImpRinv_ImpR_ak4sw. assumption. 
+ apply can_trf_ImpRinv_ImpL_ak4sw. assumption. 
+ apply can_trf_ImpRinv_BotL_ak4sw. assumption. 
- apply can_trf_ImpRinv_wk_ak4. assumption. 
Qed.

Check can_trf_ImpRinv_ak4.  Check can_trf_ImpRinv_ak4sw.

(* using this to show invertibility of ImpR rule *)
Definition K4_ImpRinv V := der_trf_rc_adm (@can_trf_ImpRinv_ak4 V).  
Definition K4sw_ImpRinv V := der_trf_rc_adm (@can_trf_ImpRinv_ak4sw V).  
Check K4_ImpRinv.  Check K4sw_ImpRinv.

(* express invertibility in terms of rel_adm *)
Lemma ra_K4_ImpRinv V: rel_adm (@K4rules V) (seqrel ImpRinv).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4_ImpRinv ; eassumption. Qed.

Lemma ra_K4sw_ImpRinv V: rel_adm (@K4rules_sw V) (seqrel ImpRinv).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_ImpRinv ; eassumption. Qed.

(** now invertibility of ImpL **)
Lemma can_trf_ImpLinv1_k4 V ps c: @K4prrule _ ps c ->
  can_trf_rules_rc (seqrel (@ImpLinv1 V)) (@K4prrule _) ps c.
Proof. intros k4.  inversion k4. clear k4. subst.
unfold can_trf_rules_rc.
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
inversion iri. clear iri. subst.
unfold seqext in *. 
inversion seo. clear seo. subst.
apply eq_sym in H0. apply map_app_ex in H0. cD.
apply map_cons_ex in H4. cD. discriminate H6. Qed.

Lemma can_trf_ImpLinv1_ck4 V ps c: cgerule (@K4prrule _) ps c ->
  can_trf_rules_rc (seqrel (@ImpLinv1 V)) (cgerule (@K4prrule _)) ps c.
Proof. intros cgk4.  inversion_clear cgk4 as [? ? ? ? ? k4 ga gs].
inversion k4. clear k4. subst.
unfold can_trf_rules_rc.
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
inversion iri. clear iri. subst.
unfold seqext in *. 
inversion seo. clear seo. subst.
eexists. split.
2: eapply ForallT_singleI.
2: eexists. 2: split. 2: apply InT_eq. 2: apply rT_refl.
eapply CGctxt. apply K4prrule_I.
apply gen_ext_splitR in ga. cD.
apply map_app_ex in ga1. cD. subst.
inversion ga3. destruct ga5 ; simpl in H0. discriminate H0. 
injection H0 as . subst. discriminate H. 
subst. rewrite map_app. apply gen_ext_app. 
apply gen_ext_extra. assumption.  assumption. 
simpl. assumption. Qed.

Definition can_trf_ImpLinv1_k4_ak4 V ps c (k4 : @K4prrule V ps c) :=
  can_trf_rules_rc_mono' k4ak4  (can_trf_ImpLinv1_k4 k4).

Definition can_trf_ImpLinv1_ck4_ak4 V ps c 
    (cgk4 : cgerule (@K4prrule V) ps c) :=
  can_trf_rules_rc_mono' ck4ak4  (can_trf_ImpLinv1_ck4 cgk4).

Lemma can_trf_ImpLinv2_k4 V ps c: @K4prrule _ ps c ->
  can_trf_rules_rc (seqrel (@ImpLinv2 V)) (@K4prrule _) ps c.
Proof. intros k4.  inversion k4. clear k4. subst.
unfold can_trf_rules_rc.
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
inversion iri. clear iri. subst.
unfold seqext in *. 
inversion seo. clear seo. subst.
apply eq_sym in H0. apply map_app_ex in H0. cD.
apply map_cons_ex in H4. cD. discriminate H6. Qed.

Lemma can_trf_ImpLinv2_ck4 V ps c: cgerule (@K4prrule _) ps c ->
  can_trf_rules_rc (seqrel (@ImpLinv2 V)) (cgerule (@K4prrule _)) ps c.
Proof. intros cgk4.  inversion_clear cgk4 as [? ? ? ? ? k4 ga gs].
inversion k4. clear k4. subst.
unfold can_trf_rules_rc.
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
inversion iri. clear iri. subst.
unfold seqext in *. 
inversion seo. clear seo. subst.
eexists. split.
2: eapply ForallT_singleI.
2: eexists. 2: split. 2: apply InT_eq. 2: apply rT_refl.
eapply CGctxt. apply K4prrule_I.
clear gs. simpl.
apply gen_ext_splitR in ga. cD.
apply map_app_ex in ga1. cD. subst.
rewrite map_app. apply gen_ext_app. 2: assumption.
inversion ga3. destruct ga5 ; simpl in H0. discriminate H0. 
injection H0 as . subst. discriminate H.  assumption.
simpl. apply gen_ext_splitR in gs. cD.
rewrite gs1. apply gen_ext_app. apply gen_ext_extra.  assumption. 
assumption. Qed.

Definition can_trf_ImpLinv2_k4_ak4 V ps c (k4 : @K4prrule V ps c) :=
  can_trf_rules_rc_mono' k4ak4  (can_trf_ImpLinv2_k4 k4).

Definition can_trf_ImpLinv2_ck4_ak4 V ps c 
    (cgk4 : cgerule (@K4prrule V) ps c) :=
  can_trf_rules_rc_mono' ck4ak4  (can_trf_ImpLinv2_ck4 cgk4).

Check can_trf_ImpLinv1_ck4_ak4.  Check can_trf_ImpLinv2_ck4_ak4.

Lemma ImpRthm1 P (A B : PropF P) rules U V X Y: 
  rsub (@Idrule _) rules -> rsub (@ImpRrule P) rules -> 
  derl (seqrule rules) [] (U ++ B :: V, X ++ Imp A B :: Y).
Proof. intros rsid rsimpr.
eapply dtderI. eapply (Sctxt_eq _ _ [] _ U (B :: V) X Y).
- unfold rsub in rsimpr. apply rsimpr. apply ImpRrule_I.
- simpl. reflexivity.  - simpl. reflexivity. - simpl. reflexivity.
- apply seqrule_mono in rsid.  eapply dersl_mono'. apply rsid.
eapply dtCons_eq.  apply in_derl. 
+ eapply (@sr_Id_alt _ B) ; solve_InT. 
+ apply dtNil.  
+ simpl. reflexivity. Qed.

Lemma ImpRthm2a P (A B : PropF P) rules U V W X: 
  rsub (@Idrule _) rules -> rsub (@ImpRrule P) rules -> 
  derl (seqrule rules) [] (X, U ++ A :: V ++ Imp A B :: W).
Proof. intros rsid rsimpr.
eapply dtderI. eapply (Sctxt_eq _ _ [] _ [] X (U ++ A :: V) W).
- unfold rsub in rsimpr. apply rsimpr. apply ImpRrule_I.
- simpl. reflexivity.  - simpl. list_assoc_r. reflexivity.
- simpl. reflexivity.
- apply seqrule_mono in rsid.  eapply dersl_mono'. apply rsid.
eapply dtCons_eq.  apply in_derl. 
+ eapply (@sr_Id_alt _ A) ; solve_InT. 
+ apply dtNil.  
+ simpl. reflexivity. Qed.

Lemma ImpRthm2b P (A B : PropF P) rules U V W X: 
  rsub (@Idrule _) rules -> rsub (@ImpRrule P) rules -> 
  derl (seqrule rules) [] (X, U ++ Imp A B :: V ++ A :: W).
Proof. intros rsid rsimpr.
eapply dtderI. eapply (Sctxt_eq _ _ [] _ [] X U (V ++ A :: W)).
- unfold rsub in rsimpr. apply rsimpr. apply ImpRrule_I.
- simpl. reflexivity.  - simpl. reflexivity.  - simpl. reflexivity.
- apply seqrule_mono in rsid.  eapply dersl_mono'. apply rsid.
eapply dtCons_eq.  apply in_derl. 
+ eapply (@sr_Id_alt _ A) ; solve_InT. 
+ apply dtNil.  
+ simpl. reflexivity. Qed.

Definition ImpRthm1sr P (A B : PropF P) U V X Y :=
  @ImpRthm1 P A B _ U V X Y (@rsId _) (@rsImpR _).
Definition ImpRthm2asr P (A B : PropF P) U V W X :=
  @ImpRthm2a P A B _ U V W X (@rsId _) (@rsImpR _).
Definition ImpRthm2bsr P (A B : PropF P) U V W X :=
  @ImpRthm2b P A B _ U V W X (@rsId _) (@rsImpR _).

Definition ImpRthm1sreq P (A B : PropF P) U V X Y :=
  derl_eq (@ImpRthm1sr P A B U V X Y).
Definition ImpRthm2asreq P (A B : PropF P) U V W X :=
  derl_eq (@ImpRthm2asr P A B U V W X).
Definition ImpRthm2bsreq P (A B : PropF P) U V W X :=
  derl_eq (@ImpRthm2bsr P A B U V W X).

(* last rule is Id rule *)
Lemma can_trf_ImpLinv2_Id_dspr V Φ1 Φ2 Ψ1 Ψ2 ps c: Idrule ps c ->
  can_trf_rules_rc (seqrel ImpLinv2) (derl (seqrule (@princrule V))) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. intros id.  destruct id. simpl. 
unfold can_trf_rules_rc. 
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
inversion iri. subst. clear iri. 
simpl in seo. injection seo as .
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 12 subgoals *)
(* some goals have identity formula on right inverted,
  so are A0, A0 -> B |- B
  some simply have A on both sides *)
+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm2asreq _ _ _ [] _).
simpl. reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm2bsreq _ _ _ _ _).
list_assoc_r'. reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm2asreq _ _ _ [] _).
simpl. reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm2bsreq _ _ _ _ _).
list_assoc_r'. reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm2asreq _ _ _ _ _).
reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm2asreq _ _ _ _ _).
reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)
Qed.

Check can_trf_ImpLinv2_Id_dspr.  

Definition can_trf_ImpLinv2_Id_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' dspak4
  (@can_trf_ImpLinv2_Id_dspr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).
Check can_trf_ImpLinv2_Id_ak4.

Definition can_trf_ImpLinv2_Id_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' dspak4sw
  (@can_trf_ImpLinv2_Id_dspr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).
Check can_trf_ImpLinv2_Id_ak4sw.

Lemma can_trf_ImpLinv1_Id_dspr V Φ1 Φ2 Ψ1 Ψ2 ps c: Idrule ps c ->
  can_trf_rules_rc (seqrel ImpLinv1) (derl (seqrule (@princrule V))) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. intros id.  destruct id. simpl. 
unfold can_trf_rules_rc. 
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
inversion iri. subst. clear iri. 
simpl in seo. injection seo as .
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 12 subgoals *)
(* some goals have identity formula on right inverted,
  so are A0, A0 -> B |- B
  some simply have A on both sides *)
+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm1sreq _ _ _ _ _ _).
reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm1sreq _ _ _ _ _ _).
list_assoc_r'. reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm1sreq _ _ _ _ _ _).
reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm1sreq _ _ _ _ _ _).
list_assoc_r'. reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm1sreq _ _ _ _ _ _).
list_assoc_l'. reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)

+ (* identity formula on right inverted *)
eexists. split. 
eapply (ImpRthm1sreq _ _ _ _ _ _).
list_assoc_l'. reflexivity.
apply ForallT_nil.

+ apply (@iddsprgoal _ A) ; solve_InT.  (* A on both sides *)
Qed.

Check can_trf_ImpLinv1_Id_dspr.

Definition can_trf_ImpLinv1_Id_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' dspak4
  (@can_trf_ImpLinv1_Id_dspr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).
Check can_trf_ImpLinv1_Id_ak4.

Definition can_trf_ImpLinv1_Id_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' dspak4sw
  (@can_trf_ImpLinv1_Id_dspr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).
Check can_trf_ImpLinv1_Id_ak4sw.

(* last rule is ImpRrule *)
Lemma can_trf_ImpLinv1_ImpR_an V Φ1 Φ2 Ψ1 Ψ2 ps c (ipc : ImpRrule ps c) : 
  can_trf_rules (seqrel ImpLinv1) (seqrule (@princrule V)) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. apply can_trf_rules_req_sr. apply can_trf_rules_Un.
intros r isr.  inversion_clear isr. destruct X. destruct i. destruct ipc.
eapply can_trf_rules_mono'.  2: apply can_trf_L_R.
apply rsubI. intros. inversion X.  inversion H. 
apply Sctxt.  apply ImpR. apply ImpRrule_I. Qed.

Check can_trf_ImpLinv1_ImpR_an.

Definition can_trf_ImpLinv1_ImpR_a V Φ1 Φ2 Ψ1 Ψ2 ps c i :=
  can_trf_rules_imp_rc (@can_trf_ImpLinv1_ImpR_an V Φ1 Φ2 Ψ1 Ψ2 ps c i).

(* could do this for derl *)
Definition can_trf_ImpLinv1_ImpR_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c i :=
  can_trf_rules_rc_mono' spak4
  (@can_trf_ImpLinv1_ImpR_a V Φ1 Φ2 Ψ1 Ψ2 ps c i).

Definition can_trf_ImpLinv1_ImpR_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c i :=
  can_trf_rules_rc_mono' spak4sw
  (@can_trf_ImpLinv1_ImpR_a V Φ1 Φ2 Ψ1 Ψ2 ps c i).

Check can_trf_ImpLinv1_ImpR_ak4.  Check can_trf_ImpLinv1_ImpR_ak4sw.

Lemma can_trf_ImpLinv2_ImpR_an V Φ1 Φ2 Ψ1 Ψ2 ps c (ipc : ImpRrule ps c) : 
  can_trf_rules (seqrel ImpLinv2) (seqrule (@princrule V)) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. apply can_trf_rules_req_sr. apply can_trf_rules_Un.
intros r isr.  inversion_clear isr. destruct X. destruct i. destruct ipc.
eapply can_trf_rules_mono'.  2: apply can_trf_L_R.
apply rsubI. intros. inversion X.  inversion H. 
apply Sctxt.  apply ImpR. apply ImpRrule_I. Qed.

Check can_trf_ImpLinv2_ImpR_an.

Definition can_trf_ImpLinv2_ImpR_a V Φ1 Φ2 Ψ1 Ψ2 ps c i :=
  can_trf_rules_imp_rc (@can_trf_ImpLinv2_ImpR_an V Φ1 Φ2 Ψ1 Ψ2 ps c i).

(* could do this for derl *)
Definition can_trf_ImpLinv2_ImpR_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c i :=
  can_trf_rules_rc_mono' spak4
  (@can_trf_ImpLinv2_ImpR_a V Φ1 Φ2 Ψ1 Ψ2 ps c i).

Definition can_trf_ImpLinv2_ImpR_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c i :=
  can_trf_rules_rc_mono' spak4sw
  (@can_trf_ImpLinv2_ImpR_a V Φ1 Φ2 Ψ1 Ψ2 ps c i).

Check can_trf_ImpLinv2_ImpR_ak4.  Check can_trf_ImpLinv2_ImpR_ak4sw.

Ltac disc_bot_imp :=
  match goal with
    | [ H : Bot _ = Imp _ _ |- _ ] => discriminate H
    | [ H : Imp _ _ = Bot _ |- _ ] => discriminate H
    end.

(* last rule is Botrule *)
Lemma can_trf_ImpLinv1_BotL_spr V Φ1 Φ2 Ψ1 Ψ2 ps c: Botrule ps c ->
  can_trf_rules_rc (seqrel ImpLinv1) (seqrule (@princrule V)) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. intros bot.  destruct bot. simpl. 
unfold can_trf_rules_rc.  intros c' sri.
inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
destruct iri.
unfold seqext. simpl in seo. simpl. 
injection seo as . subst.
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 8 subgoals *)
  try disc_bot_imp ; apply botspgoal ; solve_InT. Qed.

Check can_trf_ImpLinv1_BotL_spr.

Lemma can_trf_ImpLinv2_BotL_spr V Φ1 Φ2 Ψ1 Ψ2 ps c: Botrule ps c ->
  can_trf_rules_rc (seqrel ImpLinv2) (seqrule (@princrule V)) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. intros bot.  destruct bot. simpl. 
unfold can_trf_rules_rc.  intros c' sri.
inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
destruct iri.
unfold seqext. simpl in seo. simpl. 
injection seo as . subst.
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 8 subgoals *)
  try disc_bot_imp ; apply botspgoal ; solve_InT. Qed.

Check can_trf_ImpLinv2_BotL_spr.

Definition can_trf_ImpLinv1_BotL_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' spak4
  (@can_trf_ImpLinv1_BotL_spr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).
Check can_trf_ImpLinv1_BotL_ak4.

Definition can_trf_ImpLinv1_BotL_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' spak4sw
  (@can_trf_ImpLinv1_BotL_spr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).
Check can_trf_ImpLinv1_BotL_ak4sw.

Definition can_trf_ImpLinv2_BotL_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' spak4
  (@can_trf_ImpLinv2_BotL_spr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).
Check can_trf_ImpLinv2_BotL_ak4.

Definition can_trf_ImpLinv2_BotL_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c idr :=
  can_trf_rules_rc_mono' spak4sw
  (@can_trf_ImpLinv2_BotL_spr V Φ1 Φ2 Ψ1 Ψ2 ps c idr).
Check can_trf_ImpLinv2_BotL_ak4sw.

(* last rule is ImpLrule, two cases as to whether same or different
  implication is inverted *)
Lemma can_trf_ImpLinv1_ImpL V rules Φ1 Φ2 Ψ1 Ψ2 ps c 
  (adm_exchR : forall (ant suc suc' : list (PropF V)),
    swapped suc' suc -> adm rules [(ant, suc')] (ant, suc)):
  rsub (seqrule (@ImpLrule V)) rules -> ImpLrule ps c ->
  can_trf_rules_rc (seqrel ImpLinv1) (adm rules) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. intros rs impl.  destruct impl. simpl. 
unfold can_trf_rules_rc. 
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
destruct iri.
unfold seqext.  simpl in seo. simpl. 
injection seo as . subst.
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r.

+ (* simply a case of exchange *)
apply sig_in_cons.  apply adm_exchR.  swap_tac_Rc.

+ eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [Imp A B] [] Φ1 (H4 ++ D :: Φ3) Ψ1 (H0 ++ Ψ3)).
apply ImpLrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_2I. 
* eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv1_I.
* eexists. split. apply InT_2nd. apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv1_I.

+ (* simply a case of exchange *)
apply sig_in_cons.  apply adm_exchR.  swap_tac_Rc.

+ eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [Imp A B] [] (Φ0 ++ D :: H4) Φ2 Ψ1 (H0 ++ Ψ3)).
apply ImpLrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_2I.
* eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv1_I.
* eexists. split. apply InT_2nd. apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv1_I.

+ (* simply a case of exchange *)
apply sig_in_cons.  apply adm_exchR.  swap_tac_Rc.

+ eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [Imp A B] [] Φ1 (H4 ++ D :: Φ3) (Ψ0 ++ H0) Ψ2).
apply ImpLrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_2I.
* eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv1_I.
* eexists. split. apply InT_2nd. apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv1_I.

+ (* simply a case of exchange *)
apply sig_in_cons.  apply adm_exchR.  swap_tac_Rc.

+ eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [Imp A B] [] (Φ0 ++ D :: H4) Φ2 (Ψ0 ++ H0) Ψ2).
apply ImpLrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_2I.
* eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv1_I.
* eexists. split. apply InT_2nd. apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv1_I.
Qed.

Definition can_trf_ImpLinv1_ImpL_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c :=
  @can_trf_ImpLinv1_ImpL V _ Φ1 Φ2 Ψ1 Ψ2 ps c (@admK4exchR _) (@rs_ImpL_k4 _).
Definition can_trf_ImpLinv1_ImpL_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c :=
  @can_trf_ImpLinv1_ImpL V _ Φ1 Φ2 Ψ1 Ψ2 ps c 
  (@admK4swexchR _) (@rs_ImpL_k4sw _).

Check can_trf_ImpLinv1_ImpL_ak4.

Lemma can_trf_ImpLinv2_ImpL V rules Φ1 Φ2 Ψ1 Ψ2 ps c 
  (adm_exchR : forall (ant suc suc' : list (PropF V)),
    swapped suc' suc -> adm rules [(ant, suc')] (ant, suc)):
  rsub (seqrule (@ImpLrule V)) rules -> ImpLrule ps c ->
  can_trf_rules_rc (seqrel ImpLinv2) (adm rules) 
  (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof. intros rs impl.  destruct impl. simpl. 
unfold can_trf_rules_rc. 
intros c' sri. inversion sri as [? ? ? ? ? ? iri seo set]. clear sri. 
destruct iri.
unfold seqext.  simpl in seo. simpl. 
injection seo as . subst.
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r.

+ (* simply a case of exchange *)
apply sig_in_cons2.  apply adm_exchR.  swap_tac_Rc.

+ eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [Imp A B] [] Φ1 (H4 ++ Φ3) Ψ1 (H0 ++ C :: Ψ3)).
apply ImpLrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_2I. 
* eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv2_I.
* eexists. split. apply InT_2nd. apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv2_I.

+ (* simply a case of exchange *)
apply sig_in_cons2.  apply adm_exchR.  swap_tac_Rc.

+ eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [Imp A B] [] (Φ0 ++ H4) Φ2 Ψ1 (H0 ++ C :: Ψ3)).
apply ImpLrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_2I.
* eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv2_I.
* eexists. split. apply InT_2nd. apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv2_I.

+ (* simply a case of exchange *)
apply sig_in_cons2.  apply adm_exchR.  swap_tac_Rc.

+ eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [Imp A B] [] Φ1 (H4 ++ Φ3) (Ψ0 ++ C :: H0) Ψ2).
apply ImpLrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_2I.
* eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv2_I.
* eexists. split. apply InT_2nd. apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv2_I.

+ (* simply a case of exchange *)
apply sig_in_cons2.  apply adm_exchR.  swap_tac_Rc.

+ eexists. split. apply in_adm. apply (rsubD rs). 
eapply (Sctxt_eq _ _ [Imp A B] [] (Φ0 ++ H4) Φ2 (Ψ0 ++ C :: H0) Ψ2).
apply ImpLrule_I.
simpl. list_assoc_r. reflexivity.
simpl. list_assoc_r. reflexivity.  reflexivity.
simpl. apply ForallT_2I.
* eexists. split. apply InT_eq.  apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv2_I.
* eexists. split. apply InT_2nd. apply rT_step.
sqr_simp. apply seqrel_id'.  apply ImpLinv2_I.
Qed.

Check can_trf_ImpLinv2_ImpL.

Lemma can_trf_ImpLinv1_ak4 V ps c: @K4rules V ps c ->
  can_trf_rules_rc (seqrel ImpLinv1) (adm (@K4rules V)) ps c.
Proof. intro k4. destruct k4. 
apply can_trf_ImpLinv1_ck4_ak4. assumption. 
destruct s. destruct p. (* 4 cases for 4 rules *)
+ apply can_trf_ImpLinv1_Id_ak4. assumption. 
+ apply can_trf_ImpLinv1_ImpR_ak4. assumption. 
+ apply can_trf_ImpLinv1_ImpL_ak4. assumption. 
+ apply can_trf_ImpLinv1_BotL_ak4. assumption. Qed.

Lemma can_trf_ImpLinv1_ak4sw V ps c: @K4rules_sw V ps c ->
  can_trf_rules_rc (seqrel ImpLinv1) (adm (@K4rules_sw V)) ps c.
Proof. intro k4. destruct k4. 
- apply can_trf_ImpLinv1_k4_ak4. assumption. 
- destruct s. destruct p. (* 4 cases for 4 rules *)
+ apply can_trf_ImpLinv1_Id_ak4sw. assumption. 
+ apply can_trf_ImpLinv1_ImpR_ak4sw. assumption. 
+ apply can_trf_ImpLinv1_ImpL_ak4sw. assumption. 
+ apply can_trf_ImpLinv1_BotL_ak4sw. assumption.
- apply can_trf_ImpLinv1_wk_ak4. assumption.
Qed.

Check can_trf_ImpLinv1_ak4.  Check can_trf_ImpLinv1_ak4sw.

(* using this to show invertibility of ImpL rule *)
Definition K4_ImpLinv1 V := der_trf_rc_adm (@can_trf_ImpLinv1_ak4 V).  
Definition K4sw_ImpLinv1 V := der_trf_rc_adm (@can_trf_ImpLinv1_ak4sw V).  
Check K4_ImpLinv1.  Check K4sw_ImpLinv1.

(* express invertibility in terms of rel_adm *)
Lemma ra_K4_ImpLinv1 V: rel_adm (@K4rules V) (seqrel ImpLinv1).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4_ImpLinv1 ; eassumption. Qed.

Lemma ra_K4sw_ImpLinv1 V: rel_adm (@K4rules_sw V) (seqrel ImpLinv1).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_ImpLinv1 ; eassumption. Qed.

Definition can_trf_ImpLinv2_ImpL_ak4 V Φ1 Φ2 Ψ1 Ψ2 ps c :=
  @can_trf_ImpLinv2_ImpL V _ Φ1 Φ2 Ψ1 Ψ2 ps c (@admK4exchR _) (@rs_ImpL_k4 _).
Definition can_trf_ImpLinv2_ImpL_ak4sw V Φ1 Φ2 Ψ1 Ψ2 ps c :=
  @can_trf_ImpLinv2_ImpL V _ Φ1 Φ2 Ψ1 Ψ2 ps c 
  (@admK4swexchR _) (@rs_ImpL_k4sw _).

Lemma can_trf_ImpLinv2_ak4 V ps c: @K4rules V ps c ->
  can_trf_rules_rc (seqrel ImpLinv2) (adm (@K4rules V)) ps c.
Proof. intro k4. destruct k4. 
apply can_trf_ImpLinv2_ck4_ak4. assumption. 
destruct s. destruct p. (* 4 cases for 4 rules *)
+ apply can_trf_ImpLinv2_Id_ak4. assumption. 
+ apply can_trf_ImpLinv2_ImpR_ak4. assumption. 
+ apply can_trf_ImpLinv2_ImpL_ak4. assumption. 
+ apply can_trf_ImpLinv2_BotL_ak4. assumption. Qed.

Lemma can_trf_ImpLinv2_ak4sw V ps c: @K4rules_sw V ps c ->
  can_trf_rules_rc (seqrel ImpLinv2) (adm (@K4rules_sw V)) ps c.
Proof. intro k4. destruct k4. 
- apply can_trf_ImpLinv2_k4_ak4. assumption. 
- destruct s. destruct p. (* 4 cases for 4 rules *)
+ apply can_trf_ImpLinv2_Id_ak4sw. assumption. 
+ apply can_trf_ImpLinv2_ImpR_ak4sw. assumption. 
+ apply can_trf_ImpLinv2_ImpL_ak4sw. assumption. 
+ apply can_trf_ImpLinv2_BotL_ak4sw. assumption.
- apply can_trf_ImpLinv2_wk_ak4. assumption.
Qed.

Check can_trf_ImpLinv2_ak4.  Check can_trf_ImpLinv2_ak4sw.

(* using this to show invertibility of ImpL rule *)
Definition K4_ImpLinv2 V := der_trf_rc_adm (@can_trf_ImpLinv2_ak4 V).  
Definition K4sw_ImpLinv2 V := der_trf_rc_adm (@can_trf_ImpLinv2_ak4sw V).  
Check K4_ImpLinv2.  Check K4sw_ImpLinv2.

(* express invertibility in terms of rel_adm *)
Lemma ra_K4_ImpLinv2 V: rel_adm (@K4rules V) (seqrel ImpLinv2).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4_ImpLinv2 ; eassumption. Qed.

Lemma ra_K4sw_ImpLinv2 V: rel_adm (@K4rules_sw V) (seqrel ImpLinv2).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_ImpLinv2 ; eassumption. Qed.

