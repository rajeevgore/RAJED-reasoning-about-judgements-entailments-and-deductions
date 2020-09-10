
Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../modal".
Add LoadPath "../tense-lns".
Require Import gen genT ddT dd_fc swappedT lntacsT.
Require Import gstep gentree.
Require Import fmlsext lldefs.
Require Import Coq.Program.Basics.

Ltac fpxtac'' fpx := apply ForallTI_forall ; intros x int ;
pose (ForallTD_forall fpx int) as fpxa ; apply (pair (fst fpxa)).

Ltac fpxtac' fpx th := apply ForallTI_forall ; intros x int ;
pose (ForallTD_forall fpx int) as fpxa ;
apply (pair (fst fpxa)) ; apply th ; apply (snd fpxa).

Ltac fpxtac fpx := fpxtac' fpx id.

Lemma d2f_osscang_mQ V A rules (dtl dtr : derrec_fc rules emptyT) :
  dt2fun (osscang dual rules) (@Query V A) dtl dtr -> 
  dt2fun (osscamQ dual rules) (@Query V A) dtl dtr. 
Proof. unfold dt2fun. apply osscang_mQ. Qed.

Lemma d2f_osscamQ_ng V A rules (dtl dtr : derrec_fc rules emptyT) :
  dt2fun (osscamQ dual rules) (@Query V A) dtl dtr -> 
  dt2fun (osscang dual rules) (@Query V A) dtl dtr.
Proof. unfold dt2fun. apply osscamQ_ng. Qed.

Lemma gs2_eq {seql seqr W} ossf ossg (A : W) sub dls drs psa ca psb cb :
  (forall A', req (ossf A') (ossg A')) ->
    @gen_step2 seql seqr W ossf A sub dls drs psa ca psb cb ->
    gen_step2 ossg A sub dls drs psa ca psb cb.
Proof. intro roo. unfold gen_step2.  intros gsf saa fpl fpr da db.
apply roo. apply gsf.
- intros. apply roo.  exact (saa A' X dl X0 dr X1).
- { apply ForallTI_forall. intros x inxp.
eapply ForallTD_forall in fpl. cD. split. 
exact fpl. apply roo. exact fpl0.  exact inxp. }
- { apply ForallTI_forall. intros x inxp.
eapply ForallTD_forall in fpr. cD. split. 
exact fpr. apply roo. exact fpr0.  exact inxp. }
- exact da.  - exact db. Qed.

(** dualities between left and right subproofs 
  for ossca ... and gen_step2 (ossca ...) **)

Definition gs2_osscan_nn W dual rules n (A : W) sub dls drs psa ca psb cb :=
  @gs2_eq _ _ W _ _ A sub dls drs psa ca psb cb (osscan_eq dual rules n).

Definition gs2_osscann_n W dual rules n (A : W) sub dls drs psa ca psb cb :=
  @gs2_eq _ _ W _ _ A sub dls drs psa ca psb cb 
     (fun A => req_sym (osscan_eq dual rules n A)).

Lemma gs2_osscann_n' V rules n (A : LLfml V) sub dls drs psa ca psb cb:
  gen_step2 (osscann dual rules 1 n) A sub dls drs psa ca psb cb ->
       gen_step2 (osscan' dual rules n) A sub dls drs psa ca psb cb.
Proof. intro. eapply gs2_eq.
intro.  apply req_sym. apply osscan'_eq.  exact X. Qed.

Lemma gs2_osscan'_nn V rules n (A : LLfml V) sub dls drs psa ca psb cb:
  gen_step2 (osscan' dual rules n) A sub dls drs psa ca psb cb ->
       gen_step2 (osscann dual rules 1 n) A sub dls drs psa ca psb cb.
Proof. intro. eapply gs2_eq.  intro.  apply osscan'_eq.  exact X. Qed.

Lemma osscann_dual {V} (A : LLfml V) rules nl nr cl cr :
  osscann dual rules nl nr A cl cr -> osscann dual rules nr nl (dual A) cr cl.
Proof. intros. apply osscannI.  intros * cre cle mrg.
destruct X.  rewrite -> dual_dual in cle.
exact (d rs ls ms cle cre (merge_sym mrg)). Qed.
  
Lemma osscann_dual' {V} (A : LLfml V) rules nl nr cl cr :
  osscann dual rules nl nr (dual A) cl cr -> osscann dual rules nr nl A cr cl.
Proof. intro.  apply osscann_dual in X.
rewrite -> dual_dual in X. exact X. Qed.

Lemma osscam_dual {V} (A : LLfml V) rules cl cr :
  osscam dual rules A cl cr -> osscam dual rules (dual A) cr cl.
Proof. intro. destruct X. apply osscamI.
intros * cre cle mrg. rewrite dual_dual in cle.
exact (d rs ls ms cle cre (merge_sym mrg)). Qed.

Lemma osscam_dual' {V} (A : LLfml V) rules cl cr :
  osscam dual rules (dual A) cl cr -> osscam dual rules A cr cl.
Proof. intro odd. pose (osscam_dual odd). 
rewrite -> dual_dual in o. exact o. Qed.

Lemma osscamq_dual {V} (A : LLfml V) rules cl cr :
  osscamq dual rules A cl cr -> osscamq dual rules (dual A) cr cl.
Proof. unfold osscamq. unfold osscaq'.  rewrite dual_dual.
intro.  cD.  apply (pair (osscam_dual X)).  tauto. Qed.

Lemma osscamq_dual' {V} (A : LLfml V) rules cl cr :
  osscamq dual rules (dual A) cl cr -> osscamq dual rules A cr cl.
Proof. intro odd. pose (osscamq_dual odd). 
rewrite -> dual_dual in o. exact o. Qed.

Lemma osscamQ_dual {V} (A : LLfml V) rules cl cr :
  osscamQ dual rules A cl cr -> osscamQ dual rules (dual A) cr cl.
Proof. unfold osscamQ. unfold osscaQ'.  rewrite dual_dual.
intro.  cD.  apply (pair (osscam_dual X)).  tauto. Qed.

Lemma osscamQ_dual' {V} (A : LLfml V) rules cl cr :
  osscamQ dual rules (dual A) cl cr -> osscamQ dual rules A cr cl.
Proof. intro odd. pose (osscamQ_dual odd). 
rewrite -> dual_dual in o. exact o. Qed.

Lemma d2f_osscamQ_dual {V} (A : LLfml V) rules 
  (dta dtb : derrec_fc rules emptyT) :
  dt2fun (osscamQ dual rules) A dta dtb -> 
  dt2fun (osscamQ dual rules) (dual A) dtb dta.
Proof. unfold dt2fun. apply osscamQ_dual. Qed.

Lemma d2f_osscamQ_dual' {V} (A : LLfml V) rules 
  (dta dtb : derrec_fc rules emptyT) :
  dt2fun (osscamQ dual rules) (dual A) dta dtb -> 
  dt2fun (osscamQ dual rules) A dtb dta.
Proof. unfold dt2fun. apply osscamQ_dual'. Qed.

Lemma gs2_osscam_dual {V} (A : LLfml V) rules drsa drsb psa ca psb cb :
  gen_step2 (osscam dual rules) A isubfml drsa drsb psa ca psb cb ->
  gen_step2 (osscam dual rules) (dual A) isubfml drsb drsa psb cb psa ca.
Proof. unfold gen_step2.  intros gs sd fpl fpr db da.
apply osscam_dual.  apply gs.
intros A' saa dl ddl dr ddr.
exact (osscam_dual' _ (sd (dual A') (dual_sub saa) dr ddr dl ddl)).
{ apply ForallTI_forall. intros x inxp.
eapply ForallTD_forall in fpr. cD. split. 
exact fpr. exact (osscam_dual' _ fpr0).  exact inxp. }
{ apply ForallTI_forall. intros x inxp.
eapply ForallTD_forall in fpl. cD. split. 
exact fpl. exact (osscam_dual' _ fpl0).  exact inxp. }
exact da.  exact db. Qed.

Lemma gs2_osscam_dual' {V} (A : LLfml V) rules drsa drsb psa ca psb cb :
  gen_step2 (osscam dual rules) (dual A) isubfml drsb drsa psb cb psa ca ->
  gen_step2 (osscam dual rules) A isubfml drsa drsb psa ca psb cb.
Proof. intro gs. pose (gs2_osscam_dual gs). 
rewrite -> dual_dual in g. exact g. Qed.

Lemma gs2_osscamq_dual {V} (A : LLfml V) rules drsa drsb psa ca psb cb :
  gen_step2 (osscamq dual rules) A isubfml drsa drsb psa ca psb cb ->
  gen_step2 (osscamq dual rules) (dual A) isubfml drsb drsa psb cb psa ca.
Proof. unfold gen_step2.  intros gs sd fpl fpr db da.
apply osscamq_dual.  apply gs.
intros A' saa dl ddl dr ddr.
exact (osscamq_dual' _ (sd (dual A') (dual_sub saa) dr ddr dl ddl)).
fpxtac'' fpr. exact (osscamq_dual' _ (snd fpxa)).
fpxtac'' fpl. exact (osscamq_dual' _ (snd fpxa)).
exact da.  exact db. Qed.

Lemma gs2_osscamq_dual' {V} (A : LLfml V) rules drsa drsb psa ca psb cb :
  gen_step2 (osscamq dual rules) (dual A) isubfml drsb drsa psb cb psa ca ->
  gen_step2 (osscamq dual rules) A isubfml drsa drsb psa ca psb cb.
Proof. intro gs. pose (gs2_osscamq_dual gs). 
rewrite -> dual_dual in g. exact g. Qed.

Lemma gs2_osscamQ_dual {V} (A : LLfml V) rules drsa drsb psa ca psb cb :
  gen_step2 (osscamQ dual rules) A isubfml drsa drsb psa ca psb cb ->
  gen_step2 (osscamQ dual rules) (dual A) isubfml drsb drsa psb cb psa ca.
Proof. unfold gen_step2.  intros gs sd fpl fpr db da.
apply osscamQ_dual.  apply gs.
intros A' saa dl ddl dr ddr.
exact (osscamQ_dual' _ (sd (dual A') (dual_sub saa) dr ddr dl ddl)).
fpxtac'' fpr. exact (osscamQ_dual' _ (snd fpxa)).
fpxtac'' fpl. exact (osscamQ_dual' _ (snd fpxa)).
exact da.  exact db. Qed.

Lemma gs2_osscamQ_dual' {V} (A : LLfml V) rules drsa drsb psa ca psb cb :
  gen_step2 (osscamQ dual rules) (dual A) isubfml drsb drsa psb cb psa ca ->
  gen_step2 (osscamQ dual rules) A isubfml drsa drsb psa ca psb cb.
Proof. intro gs. pose (gs2_osscamQ_dual gs). 
rewrite -> dual_dual in g. exact g. Qed.

Lemma gs2_osscamQ_dual_e {V} (A : LLfml V) rules drsa drsb psa ca psb cb :
  gen_step2 (osscamQ dual rules) A empty_relT drsa drsb psa ca psb cb ->
  gen_step2 (osscamQ dual rules) (dual A) empty_relT drsb drsa psb cb psa ca.
Proof. unfold gen_step2.  intros gs sd fpl fpr db da.
apply osscamQ_dual.  apply gs.
intros A' saa.  destruct saa.
fpxtac'' fpr. exact (osscamQ_dual' _ (snd fpxa)).
fpxtac'' fpl. exact (osscamQ_dual' _ (snd fpxa)).
exact da.  exact db. Qed.

Lemma gs2_osscamQ_dual_e' {V} (A : LLfml V) rules drsa drsb psa ca psb cb :
  gen_step2 (osscamQ dual rules) (dual A) empty_relT drsb drsa psb cb psa ca ->
  gen_step2 (osscamQ dual rules) A empty_relT drsa drsb psa ca psb cb.
Proof. intro gs. pose (gs2_osscamQ_dual_e gs). 
rewrite -> dual_dual in g. exact g. Qed.

Lemma hs2_osscamQ_dual {V} (A : LLfml V) rules 
  (dta dtb : derrec_fc rules emptyT) :
  height_step2_tr (dt2fun (osscamQ dual rules)) A isubfml dta dtb ->
  height_step2_tr (dt2fun (osscamQ dual rules)) (dual A) isubfml dtb dta.
Proof. unfold height_step2_tr. unfold gf_step2_tr.
intros hs sd fpl fpr.
apply d2f_osscamQ_dual. apply hs.
intros A' saa * aa ab.
exact (d2f_osscamQ_dual' _ (sd (dual A') (dual_sub saa) b a ab aa)).
intros dtp mpa.  exact (d2f_osscamQ_dual' _ (fpr dtp mpa)).
intros dtq mqb.  exact (d2f_osscamQ_dual' _ (fpl dtq mqb)). Qed.

Lemma hs2_osscamQ_dual' {V} (A : LLfml V) rules 
  (dta dtb : derrec_fc rules emptyT) :
  height_step2_tr (dt2fun (osscamQ dual rules)) (dual A) isubfml dta dtb ->
  height_step2_tr (dt2fun (osscamQ dual rules)) A isubfml dtb dta.
Proof. intro hs. pose (hs2_osscamQ_dual hs). 
rewrite -> dual_dual in h. exact h. Qed.

(* need different proof for empty_relT, not using dual_sub *)
Lemma gs2_osscann_dual_e V (A : LLfml V) rules nl nr drsa drsb psa ca psb cb :
  gen_step2 (osscann dual rules nl nr) A empty_relT drsa drsb psa ca psb cb ->
  gen_step2 (osscann dual rules nr nl) (dual A) empty_relT
    drsb drsa psb cb psa ca.
Proof. unfold gen_step2.  intros gs sd fpl fpr db da.
apply osscann_dual.  apply gs.
intros A' saa dl ddl dr ddr.  inversion saa.
{ apply ForallTI_forall. intros x inxp.
eapply ForallTD_forall in fpr. cD. split. 
exact fpr. exact (osscann_dual' _ fpr0).  exact inxp. }
{ apply ForallTI_forall. intros x inxp.
eapply ForallTD_forall in fpl. cD. split. 
exact fpl. exact (osscann_dual' _ fpl0).  exact inxp. }
exact da.  exact db. Qed.

Lemma gs2_osscann_dual V (A : LLfml V) rules nl nr drsa drsb psa ca psb cb :
  gen_step2 (osscann dual rules nl nr) A isubfml drsa drsb psa ca psb cb ->
  gen_step2 (osscann dual rules nr nl) (dual A) isubfml drsb drsa psb cb psa ca.
Proof. unfold gen_step2.  intros gs sd fpl fpr db da.
apply osscann_dual.  apply gs.
intros A' saa dl ddl dr ddr.
exact (osscann_dual' _ (sd (dual A') (dual_sub saa) dr ddr dl ddl)).
{ apply ForallTI_forall. intros x inxp.
eapply ForallTD_forall in fpr. cD. split. 
exact fpr. exact (osscann_dual' _ fpr0).  exact inxp. }
{ apply ForallTI_forall. intros x inxp.
eapply ForallTD_forall in fpl. cD. split. 
exact fpl. exact (osscann_dual' _ fpl0).  exact inxp. }
exact da.  exact db. Qed.

Lemma gs2_osscann_dual_e' V (A : LLfml V) rules nl nr drsa drsb psa ca psb cb :
  gen_step2 (osscann dual rules nl nr) (dual A)
    empty_relT drsa drsb psa ca psb cb ->
  gen_step2 (osscann dual rules nr nl) A empty_relT drsb drsa psb cb psa ca.
Proof. intro gs. pose (gs2_osscann_dual_e gs). 
rewrite -> dual_dual in g. exact g. Qed.

Lemma gs2_osscann_dual' V (A : LLfml V) rules nl nr drsa drsb psa ca psb cb :
  gen_step2 (osscann dual rules nl nr) (dual A)
    isubfml drsa drsb psa ca psb cb ->
  gen_step2 (osscann dual rules nr nl) A isubfml drsb drsa psb cb psa ca.
Proof. intro gs. pose (gs2_osscann_dual gs). 
rewrite -> dual_dual in g. exact g. Qed.

(** lemmas specifying what (eg) A may be for gen_step2 ... **)

Lemma gs2_osscann_lem W dual rules (A : W) nl nr sub dls drs psa psb ca cb :
  (forall ls rs, ca = repeat A nl ++ ls -> cb = repeat (dual A) nr ++ rs ->
  gen_step2 (osscann dual rules nl nr) A sub dls drs psa ca psb cb) ->
  gen_step2 (osscann dual rules nl nr) A sub dls drs psa ca psb cb.
Proof. unfold gen_step2.
intros cgs2 saa fpl fpr dl dr.
apply osscannI.  intros * cae cbe mrg.
specialize (cgs2 ls rs cae cbe saa fpl fpr dl dr).
destruct cgs2. exact (d ls rs ms cae cbe mrg). Qed.

(* could get gs2_osscan_lem and gs_osscam_lem from gs2_osscann_lem *)
Lemma gs2_osscan_lem W dual rules (A : W) n sub dls drs psa psb ca cb :
  (forall ls rs, ca = repeat A n ++ ls -> cb = dual A :: rs ->
  gen_step2 (osscan dual rules n) A sub dls drs psa ca psb cb) ->
  gen_step2 (osscan dual rules n) A sub dls drs psa ca psb cb.
Proof. unfold gen_step2.
intros cgs2 saa fpl fpr dl dr.
apply osscanI.  intros * cae cbe mrg.
specialize (cgs2 ls rs cae cbe saa fpl fpr dl dr).
destruct cgs2. exact (d ls rs ms cae cbe mrg). Qed.

Lemma gs_osscam_lem W (dual : W -> W) rules A sub dls drs psa psb ca cb :
  (forall ls rs, ca = A :: ls -> cb = dual A :: rs ->
  gen_step2 (osscam dual rules) A sub dls drs psa ca psb cb) ->
  gen_step2 (osscam dual rules) A sub dls drs psa ca psb cb.
Proof. unfold gen_step2.
intros cgs2 saa fpl fpr dl dr.
apply osscamI.  intros * cae cbe mrg.
specialize (cgs2 ls rs cae cbe saa fpl fpr dl dr).
destruct cgs2. exact (d ls rs ms cae cbe mrg). Qed.

Lemma gs_osscaQ_lem V rules (A : LLfml V) sub dls drs psa psb ca cb :
  (forall A', A = Query A' -> forall rs, cb = Bang (dual A') :: rs ->
  gen_step2 (osscaQ dual rules) A sub dls drs psa ca psb cb) ->
  gen_step2 (osscaQ dual rules) A sub dls drs psa ca psb cb.
Proof. intro cgs2.  unfold gen_step2.
intros saa fpl fpr dl dr. repeat split. 
intros * cae cbe mrg. subst. simpl in cgs2.
specialize (cgs2 _ eq_refl _ eq_refl saa fpl fpr dl dr).
clear saa fpl fpr dl dr.
destruct cgs2.  specialize (o _ eq_refl).  destruct o.
specialize (o n).  destruct o.  simpl in d.
exact (d _ _ _ eq_refl eq_refl mrg).  Qed.

Lemma gs_osscaQ'_lem V rules (A : LLfml V) sub dls drs psa psb ca cb :
  (forall A', A = Bang A' -> forall ls, ca = Bang A' :: ls -> 
  gen_step2 (osscaQ' dual rules) A sub dls drs psa ca psb cb) ->
  gen_step2 (osscaQ' dual rules) A sub dls drs psa ca psb cb.
Proof. intro cgs2.  unfold gen_step2.
intros saa fpl fpr dl dr. repeat split. 
apply (f_equal dual) in H.  rewrite -> dual_dual in H. simpl in H. 
rewrite dual_dual.
intros * cae cbe mrg. subst. simpl in *.
specialize (cgs2 _ eq_refl rs eq_refl saa fpl fpr dl dr).
clear saa fpl fpr dl dr.
destruct cgs2. simpl in o.  rewrite -> ?dual_dual in o.
specialize (o _ eq_refl).  destruct o. 
specialize (o n).  destruct o.  simpl in d.
exact (d _ _ _ eq_refl eq_refl mrg).  Qed.

Lemma gs_osscamq_lem {V} rules A sub drsa drsb psa psb ca cb :
  (forall ls rs A', (ca = A :: ls) + (A = Query A') ->
        (cb = @dual V A :: rs) + (A = Bang A') ->
  gen_step2 (osscamq dual rules) A sub drsa drsb psa ca psb cb) ->
  gen_step2 (osscamq dual rules) A sub drsa drsb psa ca psb cb.
Proof. unfold gen_step2.
intros cgs2 saa fpl fpr dl dr.  split. 
{ apply osscamI.  intros * cae cbe mrg.
specialize (cgs2 ls rs A (inl cae) (inl cbe) saa fpl fpr dl dr).
destruct cgs2. destruct o. exact (d ls rs ms cae cbe mrg). }
repeat split ; intros A' ae * cre cbe mrg.
+ subst. simpl in cgs2.
specialize (cgs2 ls rs A' (inr eq_refl) (inl eq_refl) saa fpl fpr dl dr).
clear fpl fpr saa.  destruct cgs2. destruct p. 
revert mrg. eapply o0 ; reflexivity. (* why does this work? *)
+ pose (f_equal dual ae). rewrite -> dual_dual in e.
subst. simpl in cgs2. simpl in saa.
specialize (cgs2 rs ls _ (inl eq_refl) (inr eq_refl) saa fpl fpr dl dr).
clear fpl fpr saa.  destruct cgs2. destruct p. 
revert mrg.  eapply o1 ; simpl ; rewrite ?dual_dual ; reflexivity.
Qed.

Lemma hs2_osscamQ_lem {V} rules A sub (dtl dtr : derrec_fc rules emptyT) 
  psl psr cl cr (brl : botRule_fc dtl psl cl) (brr : botRule_fc dtr psr cr) :
  (forall ls rs A', (cl = A :: ls) + (A = Query A') ->
        (cr = @dual V A :: rs) + (A = Bang A') ->
  height_step2_tr (dt2fun (osscamQ dual rules)) A sub dtl dtr) ->
  height_step2_tr (dt2fun (osscamQ dual rules)) A sub dtl dtr.
Proof. intro hsc. unfold height_step2_tr. unfold gf_step2_tr.
intros sd fpl fpr. unfold dt2fun. repeat split ; intros * cle cre mrg ;
rewrite ?(botRule_fc_concl brl) in cle ;
rewrite ?(botRule_fc_concl brr) in cre.
- specialize (hsc ls rs A (inl cle) (inl cre) sd fpl fpr).
unfold dt2fun in hsc.  destruct hsc. destruct o. subst. 
exact (d ls rs ms (botRule_fc_concl brl) (botRule_fc_concl brr) mrg).
- specialize (hsc ls rs A0 (inr H) (inl cre) sd fpl fpr).
unfold dt2fun in hsc.  destruct hsc. destruct p. destruct o0. 
specialize (o0 A0 H). destruct o0.  specialize (o0 n). destruct o0. subst.
exact (d ls rs ms (botRule_fc_concl brl) (botRule_fc_concl brr) mrg).
- rewrite (botRule_fc_concl brl) in cre ; rewrite (botRule_fc_concl brr) in cle.
rewrite dual_dual in cre. 
pose (f_equal dual H). rewrite -> dual_dual in e. simpl in e. subst.
specialize (hsc rs ls _ (inl eq_refl) (inr eq_refl) sd fpl fpr).
unfold dt2fun in hsc.  destruct hsc. destruct p. destruct o1. 
simpl in o1. rewrite -> dual_dual in o1.
simpl in brr. rewrite -> dual_dual in brr.
specialize (o1 A0 eq_refl). destruct o1.  specialize (o1 n). destruct o1.
exact (d ls rs ms (botRule_fc_concl brr) (botRule_fc_concl brl) mrg).
Qed.

Lemma gs2_osscamQ_lem {V} rules A sub drsa drsb psa psb ca cb :
  (forall ls rs A', (ca = A :: ls) + (A = Query A') ->
        (cb = @dual V A :: rs) + (A = Bang A') ->
  gen_step2 (osscamQ dual rules) A sub drsa drsb psa ca psb cb) ->
  gen_step2 (osscamQ dual rules) A sub drsa drsb psa ca psb cb.
Proof. unfold gen_step2.
intros cgs2 saa fpl fpr dl dr. repeat split ; intros * cae cbe mrg.
{ specialize (cgs2 ls rs A (inl cae) (inl cbe) saa fpl fpr dl dr).
destruct cgs2. destruct o. exact (d ls rs ms cae cbe mrg). }
{ subst.
specialize (cgs2 ls rs A0 (inr eq_refl) (inl eq_refl) saa fpl fpr dl dr).
destruct cgs2. destruct p. destruct o0.
specialize (o0 A0 eq_refl). destruct o0.  specialize (o0 n). destruct o0.
exact (d _ _ _ eq_refl eq_refl mrg). }
{ pose (f_equal dual H). rewrite -> dual_dual in e. simpl in e. 
rewrite -> dual_dual in cbe. subst.
specialize (cgs2 rs ls _ (inl eq_refl) (inr eq_refl) saa fpl fpr dl dr).
destruct cgs2. destruct p. destruct o1. 
simpl in o1. rewrite -> dual_dual in o1.
specialize (o1 A0 eq_refl). destruct o1.  specialize (o1 n). destruct o1.
exact (d _ _ _ eq_refl eq_refl mrg). }
Qed.

(** lemmas relating gen_step2 (...) for different ... *)

(* lemmas relating gen_step2 (ossca ... for one n) to 
  gen_step2 (ossca ... for all n) *)

Lemma gs_osscaq_n_lem {V} rules A sub dls drs psa psb ca cb:
  (forall n, gen_step2 (osscanq dual rules n) A sub dls drs psa ca psb cb) ->
  gen_step2 (@osscaq V dual rules) A sub dls drs psa ca psb cb.
Proof. unfold gen_step2. intros oqn saa fpl fpr dl dr.
apply osscaqI. intro n.  apply oqn ; clear oqn.
- intros. apply saa ; assumption.
- fpxtac fpl. - fpxtac fpr.  - exact dl. - exact dr. Qed.

Lemma gs_osscan_g_lem {W} rules A dual sub dls drs psa psb ca cb:
  (forall n, gen_step2 (osscan dual rules n) A sub dls drs psa ca psb cb) ->
  gen_step2 (@osscang W dual rules) A sub dls drs psa ca psb cb.
Proof. unfold gen_step2. intros oqn saa fpl fpr dl dr.
apply osscangI. intro n.  apply oqn ; clear oqn.
- intros. apply saa ; assumption.
- fpxtac fpl. - fpxtac fpr.  - exact dl. - exact dr. Qed.

Lemma gs_osscan_g_ht_lem W (rules : rlsT (list W)) A dual sub dta dtb:
  (forall n, @height_step2_tr _ _ _ rules rules
    (dt2fun (osscan dual rules n)) A sub dta dtb) ->
  height_step2_tr (dt2fun (@osscang W dual rules)) A sub dta dtb.
Proof. split. intro n. specialize (X n). destruct X. (* does a lot!! *)
+ intros A' aaa a b Aa Ab.  specialize (X0 A' aaa a b Aa Ab).
unfold dt2fun in X0.  unfold dt2fun.  destruct X0. exact (o n).
+ intros dtp m.  specialize (X1 dtp m).
unfold dt2fun in X1.  unfold dt2fun.  destruct X1. exact (o n).
+ intros dtq m.  specialize (X2 dtq m).
unfold dt2fun in X2.  unfold dt2fun.  destruct X2. exact (o n).
+ apply osscanI. exact d. Qed.

Lemma gs_osscan_g_ht_or_lem W (rules : rlsT (list W)) A dual sub dta dtb:
  (forall n, @height_step2_tr _ _ _ rules rules
    (dt2fun (osscan dual rules n)) A sub dta dtb +
  height_step2_tr (dt2fun (@osscang W dual rules)) A sub dta dtb) ->
  height_step2_tr (dt2fun (@osscang W dual rules)) A sub dta dtb.
Proof. split. intro n. specialize (X n). sD. 
- destruct X. (* does a lot!! *)
+ intros A' aaa a b Aa Ab.  specialize (X0 A' aaa a b Aa Ab).
unfold dt2fun in X0.  unfold dt2fun.  destruct X0. exact (o n).
+ intros dtp m.  specialize (X1 dtp m).
unfold dt2fun in X1.  unfold dt2fun.  destruct X1. exact (o n).
+ intros dtq m.  specialize (X2 dtq m).
unfold dt2fun in X2.  unfold dt2fun.  destruct X2. exact (o n).
+ apply osscanI. exact d.
- destruct (X X0 X1 X2). exact (o n).  Qed.

(* version with isubfml fails because the subformula isn't Query _ *)
Lemma gs_osscang_Q_lem {V} rules A dual dls drs psa psb ca cb:
  gen_step2 (osscang dual rules) (Query A) empty_relT dls drs psa ca psb cb ->
  gen_step2 (@osscaQ V dual rules) (Query A) empty_relT dls drs psa ca psb cb.
Proof. unfold gen_step2. intros oqn saa fpl fpr dl dr.
apply osscaQI.  intros A0 qe.  apply oqn ; clear oqn.
- intros A' er. inversion er.
- fpxtac'' fpl. pose (snd fpxa). destruct o. exact (o A eq_refl).
- fpxtac'' fpr. pose (snd fpxa). destruct o. exact (o A eq_refl).
- exact dl.  - exact dr. Qed.

Lemma gs_osscang_Qi_lem {V} rules A dual dls drs psa psb ca cb:
  gen_step2 (@osscaQ V dual rules) (Query A) empty_relT dls drs psa ca psb cb ->
  gen_step2 (osscang dual rules) (Query A) empty_relT dls drs psa ca psb cb.
Proof. unfold gen_step2. intros oqn saa fpl fpr dl dr.
require oqn.  intros A' er. inversion er.
require oqn.  fpxtac'' fpl.  apply osscaQI.  intros A0 qe.  exact (snd fpxa).
require oqn.  fpxtac'' fpr.  apply osscaQI.  intros A0 qe.  exact (snd fpxa).
specialize (oqn dl dr). destruct oqn. exact (o A eq_refl). Qed.

Lemma gs_osscang_Q'_lem {V} rules A dls drs psa psb ca cb:
  gen_step2 (osscang dual rules) (Query (dual A)) empty_relT
    drs dls psb cb psa ca ->
  gen_step2 (@osscaQ' V dual rules) (Bang A) empty_relT dls drs psa ca psb cb.
Proof. unfold gen_step2. intros oqn saa fpl fpr dl dr.
apply osscaQI. simpl.  intros A0 qe.  clear qe.
apply oqn ; clear oqn.
- intros A' er. inversion er.
- fpxtac'' fpr. pose (snd fpxa). destruct o.  simpl in o. exact (o _ eq_refl).
- fpxtac'' fpl. pose (snd fpxa). destruct o.  simpl in o. exact (o _ eq_refl).
- exact dr.  - exact dl. Qed.

Lemma gs_osscang_Q'i_lem {V} rules A dls drs psa psb ca cb:
  gen_step2 (@osscaQ' V dual rules) (Bang A) empty_relT dls drs psa ca psb cb ->
  gen_step2 (osscang dual rules) (Query (dual A)) empty_relT
    drs dls psb cb psa ca.
Proof. unfold gen_step2. intros oqn saa fpl fpr dl dr.
require oqn.  intros A' er. inversion er.
require oqn.  fpxtac'' fpr.  apply osscaQI.  intros A0 qe. 
  simpl.  exact (snd fpxa).
require oqn.  fpxtac'' fpl.  apply osscaQI.  intros A0 qe.
  simpl. exact (snd fpxa).
specialize (oqn dr dl). destruct oqn. exact (o _ eq_refl). Qed.

(* doesn't work because osscang has assumptions for all n 
Lemma gs2_ng_m {W} rules (A : W) dual any dls drs psa psb ca cb:
  gen_step2 (osscang dual rules) A any dls drs psa ca psb cb ->
  gen_step2 (osscam dual rules) A any dls drs psa ca psb cb.
*)

Lemma gs2_ng_mQ {V} rules (A : LLfml V) dls drs psa psb ca cb:
  gen_step2 (osscang dual rules) (Query A) empty_relT dls drs psa ca psb cb ->
  gen_step2 (osscamQ dual rules) (Query A) empty_relT dls drs psa ca psb cb.
Proof. unfold gen_step2. intros oqn saa fpl fpr dl dr.
require oqn. intros A' er. destruct er.
require oqn. fpxtac'' fpl. exact (osscamQ_ng (snd fpxa)).
require oqn. fpxtac'' fpr. exact (osscamQ_ng (snd fpxa)).
exact (osscang_mQ (oqn dl dr)). Qed.

(* following must be empty_relT because osscang doesn't distinguish properly
  between Query and other cut formulae *)
Lemma hs2_ng_mQ {V} rules (A : LLfml V) (dtl dtr : derrec_fc rules emptyT) :
  height_step2_tr (dt2fun (osscang dual rules)) (Query A) empty_relT dtl dtr ->
  height_step2_tr (dt2fun (osscamQ dual rules)) (Query A) empty_relT dtl dtr.
Proof. unfold height_step2_tr. unfold gf_step2_tr.
 intros hsng sd fpl fpr. 
require hsng. intros A' er. destruct er.
require hsng. intros dtp mpl.  exact (d2f_osscamQ_ng (fpl _ mpl)).
require hsng. intros dtq mqr.  exact (d2f_osscamQ_ng (fpr _ mqr)).
exact (d2f_osscang_mQ hsng). Qed.

Lemma gs_osscan_gl_lem {W} rules dual n A sub dls drs psa psb ca cb:
  (forall m, leT m n -> 
    gen_step2 (osscan dual rules m) A sub dls drs psa ca psb cb) ->
  gen_step2 (@osscangl W dual rules n) A sub dls drs psa ca psb cb.
Proof. unfold gen_step2. intros oqn saa fpl fpr dl dr.
apply osscanglI. intros m lmn.  apply (oqn m lmn) ; clear oqn.
- intros. apply osscan_gl_lem. apply (osscangl_le lmn). apply saa ; assumption.
- fpxtac'' fpl. pose (snd fpxa). destruct o. exact (o _ lmn).
- fpxtac'' fpr. pose (snd fpxa). destruct o. exact (o _ lmn).
- exact dl. - exact dr. Qed.

Lemma osscangl_mono {W} rules dual m n (A : W) ca cb:
  leT m n -> osscangl dual rules n A ca cb -> osscangl dual rules m A ca cb.
Proof. intros lmn ossn. apply osscanglI. intros k lkm.
destruct ossn.  exact (o k (leT_trans lkm lmn)). Qed.

Lemma gs_osscan_gl_lem2 {W} rules dual k n A sub dls drs psa psb ca cb:
  gen_step2 (@osscangl W dual rules k) A sub dls drs psa ca psb cb ->
  (forall m, leT (S m) n -> osscan dual rules (S m + k) A ca cb) ->
  gen_step2 (@osscangl W dual rules (n + k)) A sub dls drs psa ca psb cb.
Proof. intro glk.
induction n. simpl. intro. exact glk.
intro lems.  require IHn. intros m lemn.
exact (lems m (leT_S lemn)).

unfold gen_step2. intros saa fpl fpr dl dr.
apply osscanglI. intros m lmn.  simpl in lmn. inversion lmn.
- specialize (lems _ (leT_n _)). simpl in lems. exact lems.
- subst. clear lmn.  unfold gen_step2 in IHn.
require IHn. intros A' sa dl0 dls0 dr0 drs0.
specialize (saa A' sa dl0 dls0 dr0 drs0).  simpl in saa.
exact (osscangl_mono (leT_S (leT_n _)) saa).
require IHn. fpxtac'' fpl. 
exact (osscangl_mono (leT_S (leT_n _)) (snd fpxa)).
require IHn. fpxtac'' fpr. 
exact (osscangl_mono (leT_S (leT_n _)) (snd fpxa)).
specialize (IHn dl dr). destruct IHn. exact (o _ H0).
Qed.

Lemma gs_osscang_l_lem {W} rules dual A sub dls drs psa psb ca cb:
  (forall n, gen_step2 (osscangl dual rules n) A sub dls drs psa ca psb cb) ->
  gen_step2 (@osscang W dual rules) A sub dls drs psa ca psb cb.
Proof. unfold gen_step2. intros oqn saa fpl fpr dl dr.
apply osscangI. intro n. apply osscan_gl_lem. apply oqn ; clear oqn.
- intros. apply osscang_l_lem. apply saa ; assumption.
- fpxtac' fpl @osscang_l_lem. 
- fpxtac' fpr @osscang_l_lem.
- exact dl. - exact dr. Qed.

Lemma gs_osscam_q_lem V rules (A : LLfml V) sub drsa drsb psa psb ca cb :
  (forall A', A <> Bang A') -> (forall A', A <> Query A') ->
  gen_step2 (osscam dual rules) A sub drsa drsb psa ca psb cb ->
  gen_step2 (osscamq dual rules) A sub drsa drsb psa ca psb cb.
Proof. unfold gen_step2. unfold osscamq. unfold osscaq'.
intros nb nq gs2m saa fpl fpr dl dr. split.
- apply gs2m.
+ intros A' s ll dll lr dlr.  exact (fst (saa A' s ll dll lr dlr)).
+ apply ForallTI_forall. intros x int.
eapply ForallTD_forall in fpl. cD. split ; eassumption. exact int.
+ apply ForallTI_forall. intros x int.
eapply ForallTD_forall in fpr. cD. split ; eassumption. exact int.
+ exact dl.  + exact dr.
- clear gs2m saa fpl fpr. repeat split ; intros A' ae * cae cbe mrg.
subst.  specialize (nq A' eq_refl). destruct nq.
pose (f_equal dual ae). rewrite -> dual_dual in e. simpl in e. subst.
specialize (nb _ eq_refl). destruct nb. Qed.

Lemma gs_ossca_mq_lem {V} rules A sub dls drs psa psb ca cb:
  gen_step2 (osscam dual rules) A sub dls drs psa ca psb cb ->
  gen_step2 (osscaq dual rules) A sub dls drs psa ca psb cb ->
  gen_step2 (osscaq' dual rules) A sub dls drs psa ca psb cb ->
  gen_step2 (@osscamq V dual rules) A sub dls drs psa ca psb cb.
Proof. unfold gen_step2.  intros gsm gsq gsq' saa fpl fpr dl dr.
unfold osscamq. split.  2: split.
- clear gsq gsq'. apply gsm.
+ intros. apply saa ; assumption.
+ fpxtac fpl.  + fpxtac fpr.  + exact dl. + exact dr.
- clear gsm gsq'. apply gsq.
+ intros. apply saa ; assumption.
+ fpxtac fpl.  + fpxtac fpr.  + exact dl. + exact dr.
- clear gsm gsq. apply gsq'.
+ intros. apply saa ; assumption.
+ fpxtac fpl.  + fpxtac fpr.  + exact dl. + exact dr.
Qed.

Lemma gs_ossca_mQ_lem {V} rules dual A sub dls drs psa psb ca cb:
  gen_step2 (osscam dual rules) A sub dls drs psa ca psb cb ->
  gen_step2 (osscaQ dual rules) A sub dls drs psa ca psb cb ->
  gen_step2 (osscaQ' dual rules) A sub dls drs psa ca psb cb ->
  gen_step2 (@osscamQ V dual rules) A sub dls drs psa ca psb cb.
Proof. unfold gen_step2.  intros gsm gsq gsq' saa fpl fpr dl dr.
unfold osscamQ. split.  2: split.
- clear gsq gsq'. apply gsm.
+ intros. apply saa ; assumption.
+ fpxtac fpl.  + fpxtac fpr.  + exact dl. + exact dr.
- clear gsm gsq'. apply gsq.
+ intros. apply saa ; assumption.
+ fpxtac fpl.  + fpxtac fpr.  + exact dl. + exact dr.
- clear gsm gsq. apply gsq'.
+ intros. apply saa ; assumption.
+ fpxtac fpl.  + fpxtac fpr.  + exact dl. + exact dr.
Qed.

Lemma gs_osscam_Q_lem V rules (A : LLfml V) sub drsa drsb psa psb ca cb :
  (forall A', A <> Bang A') -> (forall A', A <> Query A') ->
  gen_step2 (osscam dual rules) A sub drsa drsb psa ca psb cb ->
  gen_step2 (osscamQ dual rules) A sub drsa drsb psa ca psb cb.
Proof. intros nb nq gs2m.
apply gs_ossca_mQ_lem. exact gs2m.
apply gs_osscaQ_lem. intros A' ae rs cbe.  specialize (nq _ ae). inversion nq.
apply gs_osscaQ'_lem. intros A' ae ls cae.  specialize (nb _ ae). inversion nb.
Qed.

Lemma gs2_Q_Q' V (A : LLfml V) rules drsa drsb psa psb ca cb :
  gen_step2 (osscaQ dual rules) (dual A) empty_relT drsb drsa psb cb psa ca ->
  gen_step2 (osscaQ' dual rules) A empty_relT drsa drsb psa ca psb cb.
Proof. intro.  apply gs_osscaQ'_lem.  intros. subst A.
exact (gs_osscang_Q'_lem (gs_osscang_Qi_lem X)). Qed.

(* this fails because gen_step2 (osscaQ ...) and gen_step2 (osscang ...)
  have inductive hypotheses allowing generalised cut for all n 
Lemma gs2_Q_m V (A : LLfml V) rules drsa drsb psa psb ca cb :
  gen_step2 (osscaQ dual rules) (Query A) empty_relT drsb drsa psb cb psa ca ->
  gen_step2 (osscam dual rules) (Query A) empty_relT drsa drsb psa ca psb cb.
*)

(* summary of useful results *)
(*
Check (fun x => gs2_osscann_n (gs2_osscann_dual' (gs2_osscan'_nn x))).
Check (fun x => gs2_osscann_n (gs2_osscann_dual (gs2_osscan'_nn x))).
Check gs_osscan_g_lem.
Check gs_osscang_Q_lem.  Check gs_osscang_Qi_lem.
Check gs_osscang_Q'_lem.  Check gs_osscang_Q'i_lem.
Check (fun x => gs_osscang_Q'_lem (gs_osscang_Qi_lem x)).
Check (fun x => gs_osscang_Q_lem (gs_osscang_Q'i_lem x)).
*)

Lemma merge_doubles_via_der W rules (xs qs ms : list W) (mrg : merge xs qs ms) 
  (cc : forall q, InT q qs -> rsub (ctrrule q) rules) :
  { mqs : list W & prod (merge xs (doubles qs) mqs) (merge ms qs mqs) &
    derl (fmlsruleg rules) [mqs] ms }.
Proof. induction mrg ; cD.
- specialize (IHmrg cc). cD.
exists (x :: IHmrg). split ; apply mergeLI ; assumption.
apply fmlsruleg_derl_fmlsruleg.
eapply (OSgctxt_eq _ _ _ [x] [] IHmrg1).
rewrite app_nil_r. reflexivity.
simpl. unfold fmlsext.  rewrite app_nil_r. reflexivity.
- require IHmrg. intros q iqy. exact (cc q (InT_cons y iqy)). cD.
exists (y :: y :: IHmrg). 
split ; repeat (apply mergeRI || apply mergeLI) ; assumption.
eapply dtderI.
eapply (OSgctxt_eq _ _ _ [] zs).
specialize (cc y (InT_eq _ _)).  apply (rsubD cc).  apply ctrrule_I.
reflexivity.  reflexivity.
simpl. unfold fmlsext. simpl.
apply derl_dersl_single.
apply fmlsruleg_derl_fmlsruleg.
eapply (OSgctxt_eq _ _ _ [y ; y] [] IHmrg1).
rewrite app_nil_r. reflexivity.
simpl. unfold fmlsext.  rewrite app_nil_r. reflexivity.
- simpl. exists []. split ; apply merge_nil. apply asmI. Qed.

Lemma merge_wk W rules (xs qs ms : list W) (mrg : merge xs qs ms) 
  (cc : forall q, InT q qs -> rsub (wkrule q) rules) : 
  derl (fmlsruleg rules) [xs] ms.
Proof. induction mrg.
- specialize (IHmrg cc).
apply fmlsruleg_derl_fmlsruleg.
eapply (OSgctxt_eq _ _ _ [x] [] IHmrg).
rewrite app_nil_r. reflexivity.
simpl. unfold fmlsext.  rewrite app_nil_r. reflexivity.
- require IHmrg. intros q iqy. exact (cc q (InT_cons y iqy)).
eapply dtderI.  eapply (OSgctxt_eq _ _ _ [] zs).
specialize (cc y (InT_eq _ _)).  apply (rsubD cc).  apply wkrule_I.
reflexivity.  reflexivity.
simpl. unfold fmlsext. simpl.
apply derl_dersl_single. exact IHmrg.
- apply asmI. Qed.

(* not sure whether this is true or not, seems to difficult to prove
Lemma merge_double_4 W rules (H2 mbl mrg1 : list W) :
  merge H2 mbl mrg1 -> forall H4 mal, merge H4 mal mrg1 ->
  forall mrg, merge H2 mrg mal -> merge H4 mrg mbl -> 
  (forall q, InT q mrg -> rsub (ctrrule q) rules) ->
  { md : list W & merge mal mbl md & derl (fmlsruleg rules) [md] mrg1 }.
Proof. intro mb1. induction mb1.
- intros * m4a. inversion m4a ; subst ; clear m4a.
specialize (IHmb1 _ _ X).

Lemma merge_double_4 W rules mrg : forall (H2 mbl mrg1 : list W),
  merge H2 mbl mrg1 -> forall H4 mal, merge H4 mal mrg1 ->
  merge H2 mrg mal -> merge H4 mrg mbl -> 
  (forall q, InT q mrg -> rsub (ctrrule q) rules) ->
  { md : list W & merge mal mbl md & derl (fmlsruleg rules) [md] mrg1 }.
Proof. induction mrg.
*)

Lemma merge_exch W rules us vs xs
  (adm_exch : forall (seq seq' : list W),
    swapped seq' seq -> adm rules [seq'] seq) :
  merge us vs xs -> forall ys, merge us vs ys -> 
  forall ws zs, adm rules [ ws ++ xs ++ zs ] (ws ++ ys ++ zs).
Proof. intro mxs. induction mxs.
- intros xxy mxxy.  apply merge_consL in mxxy. cD. subst.
pose (merge_app (merge_Lnil mxxy) mxxy2).
intros.  specialize (IHmxs _ m (ws ++ [x]) zs0).
rewrite - app_assoc in IHmxs. simpl in IHmxs.
apply (adm_single_trans IHmxs). 
apply adm_exch. swap_tac.
- intros xyy mxyy.  apply merge_consR' in mxyy. cD. subst.
pose (merge_app (merge_Rnil mxyy) (merge_sym mxyy2)).
intros.  specialize (IHmxs _ m (ws ++ [y]) zs0).
rewrite - app_assoc in IHmxs. simpl in IHmxs.
apply (adm_single_trans IHmxs). 
apply adm_exch. swap_tac.
- intros ys mn. inversion mn. split.
intro drs. inversion drs. exact X. Qed.

Lemma merge_map U W (f : U -> W) xs ys ms :
  merge xs ys ms -> merge (map f xs) (map f ys) (map f ms).
Proof. intro mrg. induction mrg ; simpl.
exact (mergeLI _ IHmrg).  exact (mergeRI _ IHmrg).  exact merge_nil. Qed.

Lemma merge_map_exM' U W (f : U -> W) fxs fys ms :
  merge fxs fys ms -> forall xs ys, fxs = (map f xs) -> fys = (map f ys) ->
  { zs : list U & merge xs ys zs & ms = map f zs }.
Proof. intro mrg. induction mrg ; intros *.
- destruct xs0 ; simpl ; intros xe ye ; inversion xe.
subst.  specialize (IHmrg _ _ eq_refl eq_refl). cD. subst.
exists (u :: IHmrg). exact (mergeLI _ IHmrg0). reflexivity.
- destruct ys0 ; simpl ; intros xe ye ; inversion ye.
subst.  specialize (IHmrg _ _ eq_refl eq_refl). cD. subst.
exists (u :: IHmrg). exact (mergeRI _ IHmrg0). reflexivity.
- destruct xs ; simpl ; intros xe ; inversion xe.
destruct ys ; simpl ; intros ye ; inversion ye.
exists []. exact merge_nil. reflexivity. Qed.

Definition merge_map_exM U W f xs ys ms mrg :=
  @merge_map_exM' U W f _ _ ms mrg xs ys eq_refl eq_refl.

Lemma merge_map_exLR' U W (f : U -> W) fxs fys ms :
  merge fxs fys ms -> forall zs, ms = (map f zs) ->
  { xs : list U & fxs = map f xs & 
    { ys : list U & fys = map f ys & merge xs ys zs }}.
Proof. intro mrg. induction mrg ; intros *.
- destruct zs0 ; simpl ; intros me ; inversion me ; subst.
specialize (IHmrg _ eq_refl). cD. subst.
exists (u :: IHmrg). reflexivity.
exists IHmrg1. reflexivity.  exact (mergeLI _ IHmrg3). 
- destruct zs0 ; simpl ; intros me ; inversion me ; subst.
specialize (IHmrg _ eq_refl). cD. subst.
exists IHmrg. reflexivity.
exists (u :: IHmrg1). reflexivity.  exact (mergeRI _ IHmrg3). 
- destruct zs ; simpl ; intros me ; inversion me ; subst.
exists [].  reflexivity.  exists [].  reflexivity.  exact merge_nil. Qed.

Definition merge_map_exLR U W f fxs fys zs mrg :=
  @merge_map_exLR' U W f fxs fys (map f zs) mrg zs eq_refl.

(* had to choose carefully the form of this lemma, because admissibility
  applies to all rules, but allowing context by fmlsruleg doesn't *)
Lemma gen_ctr W rules (qs : list W) 
  (exch : forall (seq seq' : list W), swapped seq' seq -> rules [seq'] seq) 
  (cc : forall q, InT q qs -> rsub (fmlsruleg (ctrrule q)) rules) :
  forall (us vs ws : list W),
    derl rules [us ++ qs ++ vs ++ qs ++ ws] (us ++ qs ++ vs ++ ws).
Proof. induction qs ; simpl ; intros. apply asmI.
specialize (IHqs (fun q inq => cc q (InT_cons _ inq))).
pose (exch (us ++ a :: a :: qs ++ vs ++ qs ++ ws)
  (us ++ a :: qs ++ vs ++ a :: qs ++ ws)).
require r.  rewrite !cons_app_single. swap_tac_ns.
specialize (IHqs (us ++ [a]) vs ws).
rewrite <- !app_assoc in IHqs. simpl in IHqs.
apply (derl_trans IHqs). clear IHqs.
apply derl_dersl_single.
eapply derl_trans.
specialize (cc _ (InT_eq _ _)).
apply (derl_mono cc).  apply in_derl.
apply (OSgctxt_eq _ _ _ us (qs ++ vs ++ qs ++ ws) (ctrrule_I a)).
reflexivity.  reflexivity.
simpl. unfold fmlsext. simpl.
apply derl_dersl_single.  exact (in_derl _ _ _ r). Qed.

(* gen_ctr, tailored to maell_rules *)
Lemma gen_ctr_adm W rules (qs : list W) 
  (adm_exch : forall seq seq', swapped seq' seq -> adm rules [seq'] seq) 
  (cc : forall q, InT q qs -> rsub (fmlsruleg (ctrrule q)) rules) :
  forall (us vs ws : list W),
    adm rules [us ++ qs ++ vs ++ qs ++ ws] (us ++ qs ++ vs ++ ws).
Proof. intros *. apply derl_adm. apply (gen_ctr adm_exch).
intros q inq. exact (rsub_trans (cc q inq) (rsub_adm _)). Qed.

(*
Check (gen_ctr_adm adm_exch_maell).
Print Implicit gen_ctr_adm.
Print Implicit derl_dersl_single.
Print Implicit OSgctxt_eq.
Print Implicit derl_mono.
Print Implicit derl_trans.
Print Implicit in_derl.
*)

