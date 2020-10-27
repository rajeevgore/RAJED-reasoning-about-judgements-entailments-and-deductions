
(* LJ logic, using lists of formulae *)
(* lots copied from ../modal/k4_ctr.v, often with same names *)
(* invertibility of some left rules *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.

Test Universe Polymorphism. (* NB Set this causes errors *)
Test Printing Universes.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT.
Require Import List_lemmasT.
Require Import gen_tacs swappedT.
Require Import gen_seq gstep rtcT.
Require Import ljt ljt_inv.
Require Import Coq.Program.Basics.

Inductive sctr_rel V (fml : V) : relationT (list V) :=
  | sctr_relI S : sctr_rel fml (fml :: S ++ [fml]) (fml :: S). 
  (* what is ctr_rel for ??
Inductive ctr_rel V (fml : V) : relationT (list V) :=
  | ctr_relI S : ctr_rel fml (fml :: S ++ [fml]) (fml :: S). 
  *)
Inductive lsctr_rel V (fmls : list V) : relationT (list V) :=
  | lsctr_relI S : lsctr_rel fmls (fmls ++ S ++ fmls) (fmls ++ S). 

Lemma sctr_relI_eqp V (fml : V) S seq :
  seq = (fml :: S ++ [fml]) -> sctr_rel fml seq (fml :: S).
Proof. intro. subst. apply sctr_relI. Qed.

(* note, doing contractions of Imp A B when principal,
  requires inversion and contraction of B (induction on formula)
  and contraction of Imp A B in premise (induction on derivation)
  so can't use existing can_trf framework *)
(* also, don't need separated contraction since it only arises for And A B,
  where we can use inversion and contraction on smaller formula *)

(* left contraction of And A B by induction on the formula, general version *)
Lemma gen_sctrL_And V W rules (A B : PropF V) 
  (andLinv : rel_adm rules (srs_ext_rel (@AndLinv V))):
  (forall G : W,
    rsub (fst_ext_rls (rlsmap (flip pair G) (@AndLrule V))) rules) -> 
  rel_adm rules (srs_ext_rel (sctr_rel A)) -> 
  rel_adm rules (srs_ext_rel (sctr_rel B)) -> 
  rel_adm rules (srs_ext_rel (sctr_rel (And A B))).
Proof. intros rs ctra ctrb.  apply rel_admI. 
intros * sqrc. apply radmI.
intro derp. destruct sqrc. destruct s.
(* invert one instance of And A B *)
eapply andLinv in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ Φ1 (S ++ [And A B] ++ Φ2)).
apply (AndLinv_I A B).  list_assoc_r. simpl. reflexivity.  reflexivity.
(* invert 2nd instance of And A B *)
eapply andLinv in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ (Φ1 ++ [A; B] ++ S) Φ2).
apply (AndLinv_I A B).  list_assoc_r. simpl. reflexivity.  reflexivity.
revert derp. list_assoc_r. simpl. intro derp.
(* contract A *)
destruct ctra. erequire r.  erequire r.  require r.
eapply (srs_ext_relI_eq _ _ _ Φ1 (B :: Φ2)).  
apply (sctr_relI A (B :: S)).  reflexivity.  reflexivity.
destruct r. revert d. list_assoc_r'. simpl.  intro d.
apply d in derp. clear d.
(* contract B *)
destruct ctrb.  erequire r.  erequire r.  require r.
eapply (srs_ext_relI_eq _ _ _ (Φ1 ++ [A]) Φ2).  
apply (sctr_relI B S).
list_assoc_r'. simpl.  reflexivity.
list_assoc_r'. simpl.  reflexivity.
destruct r.  apply d in derp. clear d.
(* apply AndR rule to contracted premises *)
eapply derI. apply (rsubD (rs G)). 
eapply (@fextI _ _ _ Φ1 (S ++ Φ2)).
eapply rmI_eq. apply rmI. apply AndLrule_I.
reflexivity. simpl.  reflexivity.
simpl. apply dersrec_singleI. apply derp.  Qed.

Print Implicit gen_sctrL_And.

(* left contraction of Or A B by induction on the formula, general version *)
Lemma gen_sctrL_Or V W rules (A B : PropF V) 
  (orLinv1 : rel_adm rules (srs_ext_rel (@OrLinv1 V)))
  (orLinv2 : rel_adm rules (srs_ext_rel (@OrLinv2 V))):
  (forall G : W,
    rsub (fst_ext_rls (rlsmap (flip pair G) (@OrLrule V))) rules) -> 
  rel_adm rules (srs_ext_rel (sctr_rel A)) -> 
  rel_adm rules (srs_ext_rel (sctr_rel B)) -> 
  rel_adm rules (srs_ext_rel (sctr_rel (Or A B))).
Proof. intros rs ctra ctrb.  apply rel_admI. 
intros * sqrc. apply radmI.
intro derp. destruct sqrc. destruct s.
(* invert one instance of Or A B *)
pose derp as derp'.
eapply orLinv1 in derp'.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ Φ1 (S ++ [Or A B] ++ Φ2)).
apply (OrLinv1_I A B).  list_assoc_r. reflexivity.  reflexivity.
(* invert 2nd instance of Or A B *)
eapply orLinv1 in derp'.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ (Φ1 ++ [A] ++ S) Φ2).
apply (OrLinv1_I A B).  list_assoc_r. reflexivity.  reflexivity.
revert derp'. list_assoc_r. simpl. intro derp'.
(* contract A *)
destruct ctra. erequire r.  erequire r.  require r.
eapply (srs_ext_relI_eq _ _ _ Φ1 Φ2).  
apply (sctr_relI A S).  reflexivity.  reflexivity.
destruct r. revert d. list_assoc_r'. simpl.  intro d.
apply d in derp'. clear d.
(* same again for B *)
(* invert one instance of Or A B *)
eapply orLinv2 in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ Φ1 (S ++ [Or A B] ++ Φ2)).
apply (OrLinv2_I A B).  list_assoc_r. reflexivity.  reflexivity.
(* invert 2nd instance of Or A B *)
eapply orLinv2 in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ (Φ1 ++ [B] ++ S) Φ2).
apply (OrLinv2_I A B).  list_assoc_r. reflexivity.  reflexivity.
revert derp. list_assoc_r. simpl. intro derp.
(* contract B *)
destruct ctrb. erequire r.  erequire r.  require r.
eapply (srs_ext_relI_eq _ _ _ Φ1 Φ2).  
apply (sctr_relI B S).  reflexivity.  reflexivity.
destruct r. revert d. list_assoc_r'. simpl.  intro d.
apply d in derp. clear d.
(* apply OrR rule to contracted premises *)
eapply derI. apply (rsubD (rs G)). 
eapply (@fextI _ _ _ Φ1 (S ++ Φ2)).
eapply rmI_eq. apply rmI. apply OrLrule_I.
reflexivity. simpl.  reflexivity.
simpl. apply dlCons. exact derp'.
apply dersrec_singleI. exact derp.  Qed.

Print Implicit gen_sctrL_Or.

(* note, to use the can_trf method on rules, generally doesn't work
  because (eg, for AndL), premise is A, B, And A B, ... |- G,
  so what is the transformation of the premises? 
  But of course can assume contraction on smaller formulae
  and using admissibility of contracted result from actual premises,
  see ../modal/k4_ctr.v for examples of this sort of thing *)

(* can't use similar to gen_sctrL_Or/And for Imp,
  so have to use gen_step method *)
Print Implicit gen_step_lemT.
Print gen_step.

(* desired result is rel_adm rules (srs_ext_rel (sctr_rel fml))
  but see crd_ra *)

Lemma lj_ra_And V A B : rel_adm LJrules (srs_ext_rel (sctr_rel A)) ->
  rel_adm LJrules (srs_ext_rel (sctr_rel B)) ->
  rel_adm LJrules (srs_ext_rel (sctr_rel (@And V A B))).
Proof. intros. apply gen_sctrL_And.  apply LJ_rel_adm_AndLinv.
unfold LJrules. intro. apply fer_mono.
intros ps' c' ra.  eapply lrls_nc. 
epose (rsubD (rm_mono (rsubI _ _ AndL_sl))).  exact (r _ _ ra).
exact X.  exact X0.  Qed.

Lemma lja_ra_And V A B : rel_adm LJArules (srs_ext_rel (sctr_rel A)) ->
  rel_adm LJArules (srs_ext_rel (sctr_rel B)) ->
  rel_adm LJArules (srs_ext_rel (sctr_rel (@And V A B))).
Proof. intros. apply gen_sctrL_And.  apply LJA_rel_adm_AndLinv.
unfold LJArules. intro. apply fer_mono.
intros ps' c' ra.  eapply lrls_anc. 
epose (rsubD (rm_mono (rsubI _ _ AndL_sl))).  exact (r _ _ ra).
exact X.  exact X0.  Qed.

Lemma gs_sctr_lj_And V A B ps c : gen_step
    (can_rel LJrules (fun fml' : PropF V => srs_ext_rel (sctr_rel fml'))) 
    (@And V A B) isubfml (derrec LJrules emptyT) ps c.
Proof. unfold gen_step.  intros sub fp. clear fp.
apply crd_ra.  apply lj_ra_And.
apply crd_ra.  exact (sub A (isub_AndL _ _)).
apply crd_ra.  exact (sub B (isub_AndR _ _)). Qed.

Lemma gs_sctr_lja_And V A B ps c : gen_step
    (can_rel LJArules (fun fml' : PropF V => srs_ext_rel (sctr_rel fml'))) 
    (@And V A B) isubfml (derrec LJArules emptyT) ps c.
Proof. unfold gen_step.  intros sub fp. clear fp.
apply crd_ra.  apply lja_ra_And.
apply crd_ra.  exact (sub A (isub_AndL _ _)).
apply crd_ra.  exact (sub B (isub_AndR _ _)). Qed.

Lemma lj_ra_Or V A B : rel_adm LJrules (srs_ext_rel (sctr_rel A)) ->
  rel_adm LJrules (srs_ext_rel (sctr_rel B)) ->
  rel_adm LJrules (srs_ext_rel (sctr_rel (@Or V A B))).
Proof. intros. apply gen_sctrL_Or.  
apply LJ_rel_adm_OrLinv1.  apply LJ_rel_adm_OrLinv2.
unfold LJrules. intro. apply fer_mono.
intros ps' c' ra.  eapply lrls_nc. 
epose (rsubD (rm_mono (rsubI _ _ OrL_sl))).  exact (r _ _ ra).
exact X.  exact X0.  Qed.

Lemma lja_ra_Or V A B : rel_adm LJArules (srs_ext_rel (sctr_rel A)) ->
  rel_adm LJArules (srs_ext_rel (sctr_rel B)) ->
  rel_adm LJArules (srs_ext_rel (sctr_rel (@Or V A B))).
Proof. intros. apply gen_sctrL_Or.  
apply LJA_rel_adm_OrLinv1.  apply LJA_rel_adm_OrLinv2.
unfold LJArules. intro. apply fer_mono.
intros ps' c' ra.  eapply lrls_anc. 
epose (rsubD (rm_mono (rsubI _ _ OrL_sl))).  exact (r _ _ ra).
exact X.  exact X0.  Qed.

Lemma gs_sctr_lj_Or V A B ps c : gen_step
    (can_rel LJrules (fun fml' : PropF V => srs_ext_rel (sctr_rel fml'))) 
    (@Or V A B) isubfml (derrec LJrules emptyT) ps c.
Proof. unfold gen_step.  intros sub fp. clear fp.
apply crd_ra.  apply lj_ra_Or.
apply crd_ra.  exact (sub A (isub_OrL _ _)).
apply crd_ra.  exact (sub B (isub_OrR _ _)). Qed.

Lemma gs_sctr_lja_Or V A B ps c : gen_step
    (can_rel LJArules (fun fml' : PropF V => srs_ext_rel (sctr_rel fml'))) 
    (@Or V A B) isubfml (derrec LJArules emptyT) ps c.
Proof. unfold gen_step.  intros sub fp. clear fp.
apply crd_ra.  apply lja_ra_Or.
apply crd_ra.  exact (sub A (isub_OrL _ _)).
apply crd_ra.  exact (sub B (isub_OrR _ _)). Qed.

(* may be redundant due to gen_der_Id following *)
Lemma lj_der_Id V prems Γ1 Γ2 (p : V : Set) : 
  derrec LJrules prems (Γ1 ++ Var p :: Γ2, Var p).
Proof. eapply derI.  eapply fextI_eqc'. eapply Id_nc.
apply Idrule_I. reflexivity. apply dlNil. Qed.

Lemma gen_der_Id V prems rules Γ (p : V : Set) : 
  rsub (Idrule (@Var V p)) rules -> InT (Var p) Γ ->
  derrec (fst_ext_rls rules) prems (Γ, Var p).
Proof. intros rs ing. 
apply InT_split in ing. cD. subst.
eapply derI.  eapply fextI_eqc'. 
apply rs. apply Idrule_I.
reflexivity. apply dlNil. Qed.

Lemma gs_sctr_Id V A rules p any Γ1 Γ2 ps c :
  rsub (Idrule (@Var V p)) rules -> 
  Idrule (@Var V p) ps c -> gen_step
  (can_rel (fst_ext_rls rules) (fun fml' => srs_ext_rel (sctr_rel fml'))) A
  any (derrec (fst_ext_rls rules) emptyT) (map (apfst (fmlsext Γ1 Γ2)) ps)
  (apfst (fmlsext Γ1 Γ2) c).
Proof. intros rs i sub fp dc. clear sub fp dc.
intros seq' ser.  inversion i. subst.
simpl in ser.  inversion ser. inversion X. subst. clear ser X.
unfold fmlsext in H0. simpl in H0.
eapply (gen_der_Id _ rs).
acacD'T2 ; subst ; try solve_InT.
all : acacD'T2 ; subst ; try solve_InT.
list_eq_ncT. tauto.  Qed.

Lemma usefmm U V W X Y a b c f g rls ups ps : ForallT a (map b (map c ps)) ->
  (forall p : U, a (b (c p : V) : W) -> derrec rls ups (f (g p : X) : Y)) -> 
  dersrec rls ups (map f (map g ps)).
Proof. intros fa dp.  apply dersrecI_forall.
intros c0 incp.  apply InT_mapE in incp. cD.
apply InT_mapE in incp1. cD.  subst.
eapply ForallTD_forall in fa. 
exact (dp _ fa).
exact (InT_map _ (InT_map _ incp3)).
Qed.

Lemma usefm12 U V X Y a b f g rls ups ps : ForallT a (map b ps) ->
  (forall p : U, a (b p : V) -> derrec rls ups (f (g p : X) : Y)) -> 
  dersrec rls ups (map f (map g ps)).
Proof. intros fa dp.  apply dersrecI_forall.
intros c0 incp.  apply InT_mapE in incp. cD.
apply InT_mapE in incp1. cD.  subst.
eapply ForallTD_forall in fa. 
exact (dp _ fa).
exact (InT_map _ incp3).
Qed.

Lemma usefm U V Y a b f rls ups ps : ForallT a (map b ps) ->
  (forall p : U, a (b p : V) -> derrec rls ups (f p : Y)) -> 
  dersrec rls ups (map f ps).
Proof. intros fa dp.  apply dersrecI_forall.
intros c0 incp.  apply InT_mapE in incp. cD.  subst.
eapply ForallTD_forall in fa. 
exact (dp _ fa).
exact (InT_map _ incp1).
Qed.

Lemma gs_ljg_rrules V A rules any Γ1 Γ2 ps c
  (rr_gnc' : forall ps c, LJsrrules ps c -> rules (map (pair []) ps) ([], c)) :
  rlsmap (pair []) (@LJsrrules V) ps c ->
  gen_step (can_rel (fst_ext_rls rules)
    (fun fml' : PropF V => srs_ext_rel (sctr_rel fml'))) A
    any (derrec (fst_ext_rls rules) emptyT) (map (apfst (fmlsext Γ1 Γ2)) ps)
    (apfst (fmlsext Γ1 Γ2) c).
Proof.  intro r. destruct r.  unfold gen_step.
simpl. unfold fmlsext. simpl.
intros sub fp dc seq' sc. clear sub.
inversion sc. destruct X. clear sc. subst.
acacD'T2 ; subst.
- eapply derI. eapply fextI_eqc'. exact (rr_gnc' _ _ l).
simpl. unfold fmlsext. simpl.
list_assoc_r'. reflexivity.
eapply usefmm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr).
simpl. unfold fmlsext. simpl.  rewrite ?app_nil_r.
apser'. apply sctr_relI.

- eapply derI. eapply fextI_eqc'. exact (rr_gnc' _ _ l).
simpl. unfold fmlsext. simpl.
list_assoc_r'. reflexivity.
eapply usefmm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr).
simpl. unfold fmlsext. simpl.  rewrite ?app_nil_r.
apser'. apply sctr_relI.

- eapply derI. eapply fextI_eqc'. exact (rr_gnc' _ _ l).
simpl. unfold fmlsext. simpl.
assoc_mid H6.
reflexivity.
eapply usefmm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr).
simpl. unfold fmlsext. simpl.  rewrite ?app_nil_r.
apser'.  eapply arg1_cong_imp.
2: apply sctr_relI.  list_eq_assoc.

- eapply derI. eapply fextI_eqc'. exact (rr_gnc' _ _ l).
simpl. unfold fmlsext. simpl.
list_assoc_l'. reflexivity.
eapply usefmm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr).
simpl. unfold fmlsext. simpl.  rewrite ?app_nil_r.
eapply (srs_ext_relI_eq _ _ _ Φ1 Φ2).
apply (sctr_relI A S).
list_eq_assoc.  list_eq_assoc.

- list_eq_ncT. cD. subst.
eapply derI. eapply fextI_eqc'. exact (rr_gnc' _ _ l).
simpl. unfold fmlsext. simpl.
list_assoc_l'. reflexivity.
eapply usefmm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr).
simpl. unfold fmlsext. simpl.  rewrite ?app_nil_r.
apser'.  apply (sctr_relI A S).

- eapply derI. eapply fextI_eqc'. exact (rr_gnc' _ _ l).
simpl. unfold fmlsext. simpl.
list_assoc_l'. reflexivity.
eapply usefmm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr).
simpl. unfold fmlsext. simpl.  rewrite ?app_nil_r.
apser'.  apply (sctr_relI A S).

Qed.

Check gs_ljg_rrules.

Definition gs_lj_rrules V A any Γ1 Γ2 ps c :=
  @gs_ljg_rrules V A LJncrules any Γ1 Γ2 ps c (@rrls_nc' V).
Definition gs_lja_rrules V A any Γ1 Γ2 ps c :=
  @gs_ljg_rrules V A LJAncrules any Γ1 Γ2 ps c (@rrls_anc' V).

Lemma lj_der_Bot V prems Γ1 Γ2 G : derrec LJrules prems (Γ1 ++ Bot V :: Γ2, G).
Proof. eapply derI.  eapply fextI_eqc'. apply lrls_nc'.
apply Bot_sl. apply Botrule_I. assoc_single_mid. reflexivity. apply dlNil. Qed.

Lemma lja_der_Bot V prems Γ1 Γ2 G : derrec LJArules prems (Γ1 ++ Bot V::Γ2, G).
Proof. eapply derI.  eapply fextI_eqc'. apply lrls_anc'.
apply Bot_sl. apply Botrule_I. assoc_single_mid. reflexivity. apply dlNil. Qed.

Lemma lj_ctr_lrls {V} ps s (l : @LJslrules V ps [s])
  (sub : forall A', isubfml A' s -> forall x, derrec LJrules emptyT x ->
    can_rel LJrules (fun fml' : PropF V => srs_ext_rel (sctr_rel fml')) A' x) :
  rel_adm LJrules (srs_ext_rel (sctr_rel s)).
Proof. inversion l ; subst ; clear l.
+ inversion H. subst. clear H.  apply lj_ra_And.
apply crd_ra.  exact (sub A (isub_AndL _ _)).
apply crd_ra.  exact (sub B (isub_AndR _ _)).
+ inversion H. subst. clear H.  apply lj_ra_Or.
apply crd_ra.  exact (sub A (isub_OrL _ _)).
apply crd_ra.  exact (sub B (isub_OrR _ _)).
+ (* Botrule *) clear sub.  inversion X. repeat split.
inversion X0.  inversion X1.  subst. intro.
rewrite <- app_comm_cons.  apply lj_der_Bot.
Qed.

Lemma lja_ctr_lrls {V} ps s (l : @LJslrules V ps [s])
  (sub : forall A', dnsubfml A' s -> forall x, derrec LJArules emptyT x ->
    can_rel LJArules (fun fml' : PropF V => srs_ext_rel (sctr_rel fml')) A' x) :
  rel_adm LJArules (srs_ext_rel (sctr_rel s)).
Proof. inversion l ; subst ; clear l.
+ inversion H. subst. clear H.  apply lja_ra_And.
apply crd_ra.  exact (sub A (dnsub_AndL _ _)).
apply crd_ra.  exact (sub B (dnsub_AndR _ _)).
+ inversion H. subst. clear H.  apply lja_ra_Or.
apply crd_ra.  exact (sub A (dnsub_OrL _ _)).
apply crd_ra.  exact (sub B (dnsub_OrR _ _)).
+ (* Botrule *) clear sub.  inversion X. repeat split.
inversion X0.  inversion X1.  subst. intro.
rewrite <- app_comm_cons.  apply lja_der_Bot.
Qed.

Lemma gs_ljg_glrules V A rules lrules subf Γ1 Γ2 (G : PropF V) ps c  
  (lr_single : forall ps c, lrules ps c -> {c' : PropF V & c = [c']}) 
  (lr_gnc' : forall G ps c, 
    lrules ps c -> rules (map (flip pair G) ps) (flip pair G c)) 
  (ljg_ctr_il : forall ps s, lrules ps [s] ->
    (forall A', subf A' s -> forall x, derrec (fst_ext_rls rules) emptyT x ->
      can_rel (fst_ext_rls rules)
        (fun fml' => srs_ext_rel (sctr_rel fml')) A' x) ->
    rel_adm (fst_ext_rls rules) (srs_ext_rel (sctr_rel s))) :
  rlsmap (flip pair G) lrules ps c ->
  gen_step (can_rel (fst_ext_rls rules) 
      (fun fml' : PropF V => srs_ext_rel (sctr_rel fml'))) A subf
    (derrec (fst_ext_rls rules) emptyT) (map (apfst (fmlsext Γ1 Γ2)) ps)
    (apfst (fmlsext Γ1 Γ2) c).
Proof.  intro r. destruct r.  unfold gen_step.
simpl. unfold fmlsext. simpl.
intros sub fp dc seq' sc. 
inversion sc. destruct X. clear sc. subst.
pose (lr_single _ _ l). cD. subst.  simpl in H0.
acacD'T2 ; subst ; repeat (list_eq_ncT ; cD ; subst). (* 7 subgoals *)
- (* principal formula is occurrence of contracted formula *)
clear fp. pose (rel_admD (ljg_ctr_il _ _ l sub)).
revert dc. apply r. clear sub r.  apser'. apply sctr_relI.
- clear sub. eapply derI. eapply fextI_eqc'. exact (lr_gnc' G _ _ l).
simpl. unfold fmlsext. simpl.
list_assoc_r'. reflexivity.
eapply usefmm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr).
simpl. unfold fmlsext. simpl.
apser'.  apply (sctr_relI A S).
- (* principal formula is occurrence of contracted formula *)
clear fp. pose (rel_admD (ljg_ctr_il _ _ l sub)).
revert dc. apply r. clear sub r.  apser'. apply sctr_relI.
- acacD'T2 ; subst. (* why is this necessary? *)
+ (* principal formula is occurrence of contracted formula *)
clear fp. pose (rel_admD (ljg_ctr_il _ _ l sub)).
revert dc. apply r. clear sub r.  apser'. apply sctr_relI.
+ (* principal formula between occurrences of contracted formula *)
clear sub. eapply derI. eapply fextI_eqc'. exact (lr_gnc' G _ _ l).
simpl. unfold fmlsext. simpl.
assoc_single_mid' s. reflexivity.
eapply usefmm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr).
simpl. unfold fmlsext. simpl.
apser'.  eapply arg1_cong_imp.
2: apply sctr_relI.  list_eq_assoc.
- clear sub. eapply derI. eapply fextI_eqc'. exact (lr_gnc' G _ _ l).
simpl. unfold fmlsext. simpl.
list_assoc_l'. reflexivity.
eapply usefmm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr).
simpl. unfold fmlsext. simpl.
apser'.  apply (sctr_relI A S).
- (* principal formula is occurrence of contracted formula *)
clear fp. pose (rel_admD (ljg_ctr_il _ _ l sub)).
revert dc. apply r. clear sub r.  apser'. apply sctr_relI.
- clear sub. eapply derI. eapply fextI_eqc'. exact (lr_gnc' G _ _ l).
simpl. unfold fmlsext. simpl.
list_assoc_l'. reflexivity.
eapply usefmm. exact fp.
clear fp. simpl.  intros p fpdcr.  apply (snd fpdcr).
simpl. unfold fmlsext. simpl.
apser'.  apply (sctr_relI A S).
Qed.

Definition gs_lj_lrules V A Γ1 Γ2 G ps c := @gs_ljg_glrules V
  A _ _ _ Γ1 Γ2 G ps c LJsl_single lrls_nc' lj_ctr_lrls.
Definition gs_lja_lrules V A Γ1 Γ2 G ps c := @gs_ljg_glrules V
  A _ _ _ Γ1 Γ2 G ps c LJsl_single lrls_anc' lja_ctr_lrls.

Check gs_ljg_glrules.

Lemma eq_rect_0 P Q : P -> P = Q -> Q.  Proof. intros. subst. exact X. Qed.

Ltac gsirtac2 thm L1 L2 := 
eapply (fextI_eqc' _ L1 L2) ; [ apply thm |
simpl ; unfold fmlsext ; simpl ;
list_assoc_r' ; reflexivity ].

Ltac gsirtac3 B Φ1 Φ2 A S fp :=
simpl ; apply dersrec_singleI ;
unfold fmlsext ; simpl ;
inversion fp as [ x | x l X X0 Hx ] ; subst ; 
clear fp X0 ; apply (snd X) ;
pose (srs_ext_relI _ _ _ B Φ1 Φ2 (sctr_relI A S)) as s ;
eapply eq_rect_0 ; [ exact s | list_assoc_r' ; reflexivity ].

Lemma gs_ljg_ImpR V A rules Γ1 Γ2 any ps c 
  (ImpR_gnc' : forall A B, rules [([A], B)] ([], Imp A B)) :
  ImpRrule ps c -> gen_step (can_rel (fst_ext_rls rules)
      (fun fml' : PropF V => srs_ext_rel (sctr_rel fml'))) A
    any (derrec (fst_ext_rls rules) emptyT) (map (apfst (fmlsext Γ1 Γ2)) ps)
    (apfst (fmlsext Γ1 Γ2) c).
Proof.  intro i. destruct i.  unfold gen_step.
simpl. unfold fmlsext. simpl.
intros sub fp dc seq' sc. clear sub.
inversion sc. destruct X. clear sc. subst.
acacD'T2 ; subst ; repeat (list_eq_ncT ; cD ; subst). (* 6 subgoals *)
- eapply derI. gsirtac2 ImpR_gnc' Γ1 (H0 ++ (A :: S) ++ Φ2).
gsirtac3 B (Γ1 ++ A0 :: H0) Φ2 A S fp.
- eapply derI. gsirtac2 ImpR_gnc' Φ1 ((A :: S) ++ Φ2).
gsirtac3 B (Φ1 ++ [A0]) Φ2 A S fp.
- eapply derI. gsirtac2 ImpR_gnc' (Φ1 ++ A :: H3) (H6 ++ Φ2).
gsirtac3 B Φ1 Φ2 A (H3 ++ A0 :: H6) fp.
- eapply derI. gsirtac2 ImpR_gnc' (Φ1 ++ A :: S) Φ2.
gsirtac3 B Φ1 Φ2 A (S ++ [A0]) fp.
- eapply derI. gsirtac2 ImpR_gnc' (Φ1 ++ A :: S) Φ2.
gsirtac3 B Φ1 (A0 :: Φ2) A S fp.
- eapply derI. gsirtac2 ImpR_gnc' (Φ1 ++ A :: S ++ H2) Γ2.
gsirtac3 B Φ1 (H2 ++ A0 :: Γ2) A S fp.
Qed.

Check gs_ljg_ImpR.

Definition gs_lj_ImpR V A Γ1 Γ2 any ps c :=
  @gs_ljg_ImpR V A _ Γ1 Γ2 any ps c ImpR_nc'.
Definition gs_lja_ImpR V A Γ1 Γ2 any ps c :=
  @gs_ljg_ImpR V A _ Γ1 Γ2 any ps c ImpR_anc'.

Ltac gsiltac sub fp A S1 S2 A0 B G H J K L M N :=
clear sub ; eapply derI ; [
eapply (fextI_eqc' _ H J) ; [
exact (ImpL_nc (ImpLrule_I A0 B G)) |
simpl ; unfold fmlsext ; simpl ;  list_eq_assoc ] |
simpl ; unfold fmlsext ; simpl ;
inversion fp as [x | x l X X0 a ] ; clear fp ; subst ; apply dlCons ; [
clear X0 ;  apply (snd X) ;
eapply (srs_ext_relI_eq _ _ _ K L (sctr_relI A S1)) ;
list_eq_assoc |
clear X ; inversion X0 as [x | x l X X1 a ] ; subst ; clear X1 X0 ;
apply dersrec_singleI ;  apply (snd X) ;
eapply (srs_ext_relI_eq _ _ _ M N (sctr_relI A S2)) ; list_eq_assoc ]].

(* adapt gs_lj_ImpL to lja *)
Ltac gsiltac_a sub fp A S1 S2 p B G H J K L M N :=
clear sub ; eapply derI ; [
eapply (fextI_eqc' _ H J) ; [
exact (ImpL_anc (ImpLrule_p_I p B G)) |
simpl ; unfold fmlsext ; simpl ;  list_eq_assoc ] |
simpl ; unfold fmlsext ; simpl ;
inversion fp as [x | x l X X0 a ] ; clear fp ; subst ; apply dlCons ; [
clear X0 ;  apply (snd X) ;
eapply (srs_ext_relI_eq _ _ _ K L (sctr_relI A S1)) ;
list_eq_assoc |
clear X ; inversion X0 as [x | x l X X1 a ] ; subst ; clear X1 X0 ;
apply dersrec_singleI ;  apply (snd X) ;
eapply (srs_ext_relI_eq _ _ _ M N (sctr_relI A S2)) ; list_eq_assoc ]].

Check LJ_rel_adm_ImpLinv2.  Check crd_ra.
About LJ_can_rel_ImpLinv2.

Definition srs_ext_relI_eq' W Y R ant ant' G Φ1 Φ2 seq1 raa eq1 :=
  @srs_ext_relI_eq W Y R ant ant' G Φ1 Φ2 seq1 _ raa eq1 eq_refl.
  
Print Implicit srs_ext_relI_eq.
Print Implicit fextI_eqc'.
Print Implicit sctr_relI.

Ltac gsilptac sub fp S A0 B G H J K L M N P Q := 
inversion fp as [ | x l lp frp ] ; subst ; clear fp ;
destruct lp as [ lpd lpc ] ;
unfold can_rel in lpc ;  erequire lpc ; require lpc ; [
eapply (srs_ext_relI_eq' _ _ _ H J (sctr_relI (Imp A0 B) S)) ;
list_eq_assoc | ] ;
(* now lpc is left premise, contracted *)
inversion frp as [ | x l rp f0 ] ; subst ; clear frp f0 ;
destruct rp as [ rpd rpc ] ; clear rpc ;
(* now invert Imp A0 B in right premise *)
apply LJ_can_rel_ImpLinv2 in rpd ;
unfold can_rel in rpd ;  erequire rpd ; require rpd ; [
eapply (srs_ext_relI_eq' _ _ _ K L (ImpLinv2_I A0 B)) ;
list_eq_assoc | ] ;  
(* now rpd is right premise, with other Imp A0 B inverted to give B *)
specialize (sub B (isub_ImpR _ _) _ rpd) ;
unfold can_rel in sub ;  erequire sub ; require sub ; [
eapply (srs_ext_relI_eq' _ _ _ M N (sctr_relI B S)) ;
list_eq_assoc | ] ; 
(* now sub is right premise, with B contracted *)
pose (dlCons lpc (dersrec_singleI sub)) as d ;
eapply derI ; [  eapply (fextI_eqc' _ P Q) ; [
exact (ImpL_nc (ImpLrule_I A0 B G)) | list_eq_assoc ] | 
apply (eq_rect _ _ d) ;  list_eq_assoc ].

Ltac gsilptac_a sub fp S p B G H J K L M N P Q := 
inversion fp as [ | x l lp frp ] ; subst ; clear fp ;
destruct lp as [ lpd lpc ] ;
unfold can_rel in lpc ;  erequire lpc ; require lpc ; [
eapply (srs_ext_relI_eq' _ _ _ H J (sctr_relI (Imp (Var p) B) S)) ;
list_eq_assoc | ] ;
(* now lpc is left premise, contracted *)
inversion frp as [ | x l rp f0 ] ; subst ; clear frp f0 ;
destruct rp as [ rpd rpc ] ; clear rpc ;
(* now invert Imp (Var p) B in right premise *)
apply LJA_can_rel_ImpL_Var_inv2 in rpd ; 
unfold can_rel in rpd ;  erequire rpd ; require rpd ; [
eapply (srs_ext_relI_eq' _ _ _ K L (ImpL_Var_inv2_I p B)) ;
list_eq_assoc | ] ;  
(* now rpd is right premise, with other Imp (Var p) B inverted to give B *)
specialize (sub B (dnsub_ImpR _ _) _ rpd) ;
unfold can_rel in sub ;  erequire sub ; require sub ; [
eapply (srs_ext_relI_eq' _ _ _ M N (sctr_relI B S)) ;
list_eq_assoc | ] ; 
(* now sub is right premise, with B contracted *)
pose (dlCons lpc (dersrec_singleI sub)) as d ;
eapply derI ; [  eapply (fextI_eqc' _ P Q) ; [
exact (ImpL_anc (ImpLrule_p_I p B G)) | list_eq_assoc ] | 
apply (eq_rect _ _ d) ;  list_eq_assoc ].

Lemma gs_lja_ImpL V A Γ1 Γ2 ps c : @ImpLrule_p V ps c -> gen_step
    (can_rel LJArules (fun fml' : PropF V => srs_ext_rel (sctr_rel fml'))) A
    dnsubfml (derrec LJArules emptyT) (map (apfst (fmlsext Γ1 Γ2)) ps)
    (apfst (fmlsext Γ1 Γ2) c).
Proof.  intro i. destruct i.  unfold gen_step.
simpl. unfold fmlsext. simpl.
intros sub fp dc seq' sc.
inversion sc. destruct X. clear sc. subst.
acacD'T2 ; subst ; repeat (list_eq_ncT ; cD ; subst). (* 7 subgoals *)

- (* principal formula of Impl is first occurrence of contracted formula *)
gsilptac_a sub fp S p B G Γ1 Φ2 (Γ1 ++ B :: S) Φ2 Γ1 Φ2 Γ1 (S ++ Φ2).

- gsiltac_a sub fp A S S p B G Γ1 (H2 ++ (A :: S) ++ Φ2)
  (Γ1 ++ Imp (Var p) B :: H2) Φ2 (Γ1 ++ B :: H2) Φ2.
 
- gsiltac_a sub fp A S S p B G (Φ1 ++ A :: S) Γ2
  Φ1 (Imp (Var p) B :: Γ2) Φ1 (B :: Γ2).

- (* principal formula of Impl is first occurrence of contracted formula *)
gsilptac_a sub fp S p B G Φ1 Φ2 (Φ1 ++ B :: S) Φ2 Φ1 Φ2 Φ1 (S ++ Φ2).

- acacD'T2 ; subst.
+ (* principal formula of Impl is second occurrence of contracted formula *)
gsilptac_a sub fp H3 p B G Φ1 Φ2 Φ1 (H3 ++ B :: Φ2) Φ1 Φ2 Φ1 (H3 ++ Φ2).
+ gsiltac_a sub fp A (H3 ++ Imp (Var p) B :: H5) (H3 ++ B :: H5) 
  p B G (Φ1 ++ A :: H3) (H5 ++ Φ2) Φ1 Φ2 Φ1 Φ2.

- (* principal formula of Impl is second occurrence of contracted formula *)
gsilptac_a sub fp S p B G Φ1 Φ2 Φ1 (S ++ B :: Φ2) Φ1 Φ2 Φ1 (S ++ Φ2).

- gsiltac_a sub fp A S S p B G (Φ1 ++ A :: S ++ H2) Γ2
  Φ1 (H2 ++ Imp (Var p) B :: Γ2) Φ1 (H2 ++ B :: Γ2).
Qed.

Lemma gs_lj_ImpL V A Γ1 Γ2 ps c : ImpLrule ps c -> gen_step
    (can_rel LJrules (fun fml' : PropF V => srs_ext_rel (sctr_rel fml'))) A
    isubfml (derrec (@LJrules V) emptyT) (map (apfst (fmlsext Γ1 Γ2)) ps)
    (apfst (fmlsext Γ1 Γ2) c).
Proof.  intro i. destruct i.  unfold gen_step.
simpl. unfold fmlsext. simpl.
intros sub fp dc seq' sc.
inversion sc. destruct X. clear sc. subst.
acacD'T2 ; subst ; repeat (list_eq_ncT ; cD ; subst). (* 7 subgoals *)

- (* principal formula of Impl is first occurrence of contracted formula *)
gsilptac sub fp S A0 B G Γ1 Φ2 (Γ1 ++ B :: S) Φ2 Γ1 Φ2 Γ1 (S ++ Φ2).

- gsiltac sub fp A S S A0 B G Γ1 (H2 ++ (A :: S) ++ Φ2)
  (Γ1 ++ Imp A0 B :: H2) Φ2 (Γ1 ++ B :: H2) Φ2.
 
- gsiltac sub fp A S S A0 B G (Φ1 ++ A :: S) Γ2
  Φ1 (Imp A0 B :: Γ2) Φ1 (B :: Γ2).

- (* principal formula of Impl is first occurrence of contracted formula *)
gsilptac sub fp S A0 B G Φ1 Φ2 (Φ1 ++ B :: S) Φ2 Φ1 Φ2 Φ1 (S ++ Φ2).

- acacD'T2 ; subst.
+ (* principal formula of Impl is second occurrence of contracted formula *)
gsilptac sub fp H3 A0 B G Φ1 Φ2 Φ1 (H3 ++ B :: Φ2) Φ1 Φ2 Φ1 (H3 ++ Φ2).
+ gsiltac sub fp A (H3 ++ Imp A0 B :: H5) (H3 ++ B :: H5) 
  A0 B G (Φ1 ++ A :: H3) (H5 ++ Φ2) Φ1 Φ2 Φ1 Φ2.

- (* principal formula of Impl is second occurrence of contracted formula *)
gsilptac sub fp S A0 B G Φ1 Φ2 Φ1 (S ++ B :: Φ2) Φ1 Φ2 Φ1 (S ++ Φ2).

- gsiltac sub fp A S S A0 B G (Φ1 ++ A :: S ++ H2) Γ2
  Φ1 (H2 ++ Imp A0 B :: Γ2) Φ1 (H2 ++ B :: Γ2).
Qed.

Print Implicit gs_lj_ImpL.

Lemma ctr_adm_lj V (fml : PropF V) : 
  forall seq, derrec LJrules emptyT seq -> 
  can_rel LJrules (fun fml' => srs_ext_rel (sctr_rel fml')) fml seq.
Proof. eapply gen_step_lemT. apply AccT_isubfml.
intros * ljpc. destruct ljpc.
destruct r. destruct l.
- (* ImpLrule *)
exact (gs_lj_ImpL _ _ i). 
- (* ImpRrule *)
exact (gs_lj_ImpR _ _ _ i). 
- (* Idrule *)
eapply gs_sctr_Id. 2: exact i. apply rsubI. apply Id_nc.
- (* left rules *)
exact (gs_lj_lrules _ _ r).
- (* right rules *) 
exact (gs_lj_rrules _ _ _ r).

Qed.

Print Implicit ctr_adm_lj.

(* extending contraction of one formula to contraction of a list of formulae *)
Lemma lctr_adm_lj V fmls : 
  forall seq, derrec LJrules emptyT seq -> 
  can_rel (@LJrules V) (fun fmls' => srs_ext_rel (lsctr_rel fmls')) fmls seq.
Proof. intros seq ds. unfold can_rel.
induction fmls ; intros seq' slss ; destruct slss ; inversion l ; subst.
apply (eq_rect _ _ ds). list_eq_assoc.
specialize (IHfmls (Φ1 ++ ((a :: fmls) ++ S ++ [a]) ++ Φ2, G)).
require IHfmls.  pose (lsctr_relI fmls (S ++ [a])).
pose (srs_ext_relI _ _ _ G (Φ1 ++ [a]) Φ2 l0).
eapply arg1_cong_imp'.  apply (eq_rect _ _ s).
list_eq_assoc.  list_eq_assoc.
eapply (ctr_adm_lj IHfmls).
apply srs_ext_relI.  rewrite app_assoc.  apply sctr_relI. Qed.

Print Implicit lctr_adm_lj.

Lemma asa_ser_lsctr U W T A B C D E G :
  @app_split_at U T A B C -> app_split_at T C D E ->
    srs_ext_rel (lsctr_rel T) (A, G : W) (B ++ T ++ D ++ E, G).
Proof. intros aa ac.  apply asa_eq in aa.  apply asa_eq in ac. subst.
pose (lsctr_relI T D).  pose (srs_ext_relI _ _ _ G B E l).
eapply arg1_cong_imp in s.  apply (eq_rect _ _ s).
list_eq_assoc.  list_eq_assoc. Qed.

About asa_ser_lsctr.

(* lemmas for tactics to do contraction, may not be used any more *)
Lemma ser_appL W Y R L1 L2 L2' (G : Y) :
  @srs_ext_rel W Y R (L2, G) (L2', G) ->
  srs_ext_rel R (L1 ++ L2, G) (L1 ++ L2', G).
Proof. intro ser. inversion ser. eapply srs_ext_relI_eq.
exact X. list_assoc_l'. reflexivity.
list_assoc_l'. reflexivity. Qed.

Lemma ser_appR W Y R L1 L1' L2 (G : Y) :
  @srs_ext_rel W Y R (L1, G) (L1', G) ->
  srs_ext_rel R (L1 ++ L2, G) (L1' ++ L2, G).
Proof. intro ser. inversion ser. list_assoc_r'. 
apply srs_ext_relI.  exact X. Qed.

Lemma ser_appc W Y R (c : W) L2 L2' (G : Y) :
  srs_ext_rel R (L2, G) (L2', G) ->
  srs_ext_rel R (c :: L2, G) (c :: L2', G).
Proof. intro ser. inversion ser. rewrite !app_comm_cons.
apply srs_ext_relI.  exact X. Qed.

(* for contraction on A , X is can_rel ... *)
Ltac sersctrtac X A := 
unfold can_rel in X ; erequire X ; require X ; [
apply srs_ext_relI_alt ; apply fst_relI ; ertac A ;
apply ext_relI_nil ; eapply sctr_relI_eqp ;
list_assoc_r' ; apply f_equal ; list_assoc_l' ; reflexivity | ].


  
