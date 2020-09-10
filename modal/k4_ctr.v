
(* K4 modal logic, using lists of formulae *)
(* contraction *)

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
Require Import lntT.
Require Import List_lemmasT.
Require Import gen_tacs.
Require Import swappedT.
Require Import lntacsT.
Require Import gen_seq gstep.
Require Import gen_ext.
Require Import rtcT.
Require Import k4.
Require Import k4_exch.
Require Import k4_inv.

(* want to prove admissibility of a single contraction of a given formula,
  conditional upon admissibility of contraction(s) of smaller formulae,
  for cpl, no need to do induction on the derivation at all,
  simply well-founded induction on the contraction formula,
  but for K4, box rule, need induction on the derivation *)

(* no need for exchange (might be necessary for /\ or \/ rules) *)

(* conditional contraction relation - a single contraction is in the
  relation provided that contractions on subformulae are admissible *)

(*
Check der_trf_rc_adm.
Check der_trf_rc_derl.
Check der_trf_rtc.
Check der_trf_rc.
*)

(* problem: for a box formula where the last rule is the box rule,
in the premises we require two contractions, using der_trf_rtc;
for other formulae we need admissibility of inversion, so would use
der_trf_rc_adm;
solution - prove contraction separately for each sort of formula *)

(* separated contraction *)
Inductive sctr_relL V (fml : V) : relationT (Seql V) :=
  | sctr_relLI S : sctr_relL fml (fml :: S ++ [fml], []) (fml :: S, []). 
Inductive sctr_relR V (fml : V) : relationT (Seql V) :=
  | sctr_relRI S : sctr_relR fml ([], fml :: S ++ [fml]) ([], fml :: S). 
Inductive ctr_relL V (fml : V) : relationT (Seql V) :=
  | ctr_relLI : ctr_relL fml ([fml ; fml], []) ([fml], []). 
Inductive ctr_relR V (fml : V) : relationT (Seql V) :=
  | ctr_relRI : ctr_relR fml ([], [fml ; fml]) ([], [fml]). 
Inductive del_relR V (fml : V) : relationT (Seql V) :=
  | del_relRI : del_relR fml ([], [fml]) ([], []). 

Definition sqr_sctr_relRI V fml S := seqrel_id' _ _ _ (@sctr_relRI V fml S).
Definition sqr_sctr_relLI V fml S := seqrel_id' _ _ _ (@sctr_relLI V fml S).
Definition sqr_del_relRI V fml := seqrel_id' _ _ _ (@del_relRI V fml).

Lemma sctr_relRId V (fml fmld: V) S: fml = fmld -> 
  sctr_relR fml ([], fml :: S ++ [fml]) ([], fmld :: S).
Proof.  intro. subst. apply sctr_relRI. Qed.

Lemma sqr_del_sctrR W (fml : W) : 
  rsub (seqrel (sctr_relR fml)) (seqrel (del_relR fml)).
Proof. unfold rsub. intros *. intro sqd.
destruct sqd. destruct s. unfold seqext.
apply (Sctxt_relI_eq _ [] [fml] [] [] Φ1 Φ2 (Ψ1 ++ fml :: S) Ψ2).
apply del_relRI.  
list_assoc_r.  simpl. reflexivity.
list_assoc_r.  simpl. reflexivity.  Qed.

Lemma sqr_del_ctrR W (fml : W) : 
  rsub (seqrel (ctr_relR fml)) (seqrel (del_relR fml)).
Proof. unfold rsub. intros *. intro sqd.
destruct sqd. destruct c0. unfold seqext.
apply (Sctxt_relI_eq _ [] [fml] [] [] Φ1 Φ2 Ψ1 (fml :: Ψ2)).
apply del_relRI.  simpl. reflexivity.  simpl. reflexivity.  Qed.

Lemma can_trf_sctrL_Bot V ps c: 
  can_trf_rules (seqrel (sctr_relL (@Bot V))) (seqrule (@Botrule V)) ps c.
Proof. unfold can_trf_rules.
intros c' scr.  inversion scr. destruct X. clear scr. 
exists []. split. eapply Sctxt_eq.
apply Botrule_I. simpl. reflexivity.
reflexivity.  reflexivity.  apply ForallT_nil. Qed.

Definition can_trf_sctrL_Bot_k4 V ps c (_ : K4rules ps c) :=
  can_trf_rules_mono' (@rs_BotL_k4 V) (@can_trf_sctrL_Bot V ps c).
Definition can_trf_sctrL_Bot_k4sw V ps c (_ : K4rules_sw ps c) :=
  can_trf_rules_mono' (@rs_BotL_k4sw V) (@can_trf_sctrL_Bot V ps c).

Definition K4_sctrL_Bot V := der_trf (@can_trf_sctrL_Bot_k4 V).
Definition K4sw_sctrL_Bot V := der_trf (@can_trf_sctrL_Bot_k4sw V).
Check K4_sctrL_Bot.  Check K4sw_sctrL_Bot.

(* contraction admissibility for Bot on the right: 
  follows from admissibility of deleting a single Bot on the right *)

Definition sce_impl W A B ca cs Φ1 Φ2 Ψ1 Ψ2 cae cse :=
  @Sctxt_eq _ _ _ _ ca cs _ _ Φ1 Φ2 Ψ1 Ψ2 (@ImpLe W A B) cae cse eq_refl.
Definition sce_impr W A B ca cs Φ1 Φ2 Ψ1 Ψ2 cae cse :=
  @Sctxt_eq _ _ _ _ ca cs _ _ Φ1 Φ2 Ψ1 Ψ2 (@ImpRe W A B) cae cse eq_refl.

Definition seq_del_relRI V fml := seqrel_id' _ _ _ (@del_relRI V fml).
Definition seq_ctr_relRI V fml := seqrel_id' _ _ _ (@ctr_relRI V fml).

Lemma vvapp V (fml : V) ff l: ff = [fml ; fml] -> fml :: fml :: l = ff ++ l.
Proof. intros. subst. simpl.  reflexivity. Qed.

Ltac ctdtac1 seq_relI := simpl ; apply ForallT_singleI ;
eexists ; split ; [ apply InT_eq |
apply rT_step ; sqr_simp ; subst ; apply seq_relI ].

Ltac ctdtac2 seq_relI := simpl ; apply ForallT_2I ;
[ eexists ; split ; [ apply InT_eq |
apply rT_step ; sqr_simp ; subst ; apply seq_relI ] |
eexists ; split ; [ apply InT_2nd |
apply rT_step ; sqr_simp ; subst ; apply seq_relI ]].

(* contraction of a primitive proposition *)

Definition princrule_seaL V ps U1 U2 S p :=
  sing_empty_app U1 U2 (@princrule_seL V ps (U1 ++ U2) S p).
Definition princrule_seaR V ps U S1 S2 p :=
  sing_empty_app S1 S2 (@princrule_seR V ps U (S1 ++ S2) p).

(* don't need to use is_nil here because they won't be going in 
  as args of princrule *)
Lemma princrule_appL V ps (U1 U2 S : list (PropF V)) :
  princrule ps (U1 ++ U2, S) -> (princrule ps (U1, S) * eq U2 []) + 
    (princrule ps (U2, S) * eq U1 []).
Proof. intro pa. pose pa.
apply princrule_seaL in p. sD ; subst ; simpl ; rewrite ?app_nil_r ;
simpl in pa ; rewrite ?app_nil_r in pa ; tauto. Qed.

Lemma princrule_appR V ps (U S1 S2 : list (PropF V)) :
  princrule ps (U, S1 ++ S2) -> (princrule ps (U, S1) * eq S2 []) + 
    (princrule ps (U, S2) * eq S1 []).
Proof. intro pa. pose pa.
apply princrule_seaR in p. sD ; subst ; simpl ; rewrite ?app_nil_r ;
simpl in pa ; rewrite ?app_nil_r in pa ; tauto. Qed.

Lemma princrule_nvL (V : Set) ps (pp : V) U S:
  princrule ps (Var pp :: U, S) -> 
    prod (prod (U = []) (S = [Var pp])) (ps = []).   
Proof. intro. inversion X ; subst ; 
rename_last Y ; inversion Y ; subst ; tauto. Qed.

Lemma princrule_nvR (V : Set) ps (pp : V) U S:
  princrule ps (U, Var pp :: S) -> 
    prod (prod (U = [Var pp]) (S = [])) (ps = []).   
Proof. intro. inversion X ; subst ; 
rename_last Y ; inversion Y ; subst ; tauto. Qed.

Ltac pr_arg_ant_mr :=
  match goal with
    | [ H : princrule _ (?arg1, _) |- _ ] => assoc_mid arg1 ; reflexivity
    end.

Ltac pr_arg_suc_mr :=
  match goal with
    | [ H : princrule _ (_, ?arg2) |- _ ] => assoc_mid arg2 ; reflexivity
    end.

Ltac forallgg th := 
  apply ForallTI_forall ;
  intros x inm ;
  apply InT_mapE in inm ; cD ;
  eexists ; split ; [ apply InT_map ; eassumption | 
    subst x ;  apply rT_step ;
    destruct inm ;  unfold seqext ;
    simpl ; list_assoc_l ; rewrite ?cons_single ; rewrite ?app_nil_r ;
    sqr_simp ; subst ; simpl ; apply th ].

Ltac forallg := forallgg sqr_sctr_relRI.
Ltac forallgL := forallgg sqr_sctr_relLI.

(* proof methods for contraction (?)
- have inversion of ImpL/R so if contracting A -> B then can invert
  twice and use induction on the contraction formula, but
  this method is a problem for contracting any other formula,
  have to use usual method - lots of cases
- show inversion of A -> B is height-reducing, then for any sequent
  containing A -> B (even just once), can invert, then contract by
  induction on height, then apply ImpL/R rule
- as above, but induction on the size of the sequent
*)

Ltac conc_ant_nil :=
  intro ; eexists ; split ; [ eapply Sctxt_eq ;
    [ eassumption | reflexivity | pr_arg_suc_mr | reflexivity ] |
  simpl ; rewrite ?app_nil_r ; forallgg sqr_sctr_relLI ].

Ltac conc_suc_nil :=
  intro ; eexists ; split ; [ eapply Sctxt_eq ;
    [ eassumption | pr_arg_ant_mr | reflexivity | reflexivity ] |
  simpl ; rewrite ?app_nil_r ; forallgg sqr_sctr_relRI ].

Ltac conc_gen th :=
  intro ; eexists ; split ; [ eapply Sctxt_eq ;
    [ eassumption | pr_arg_ant_mr | pr_arg_suc_mr | reflexivity ] |
  simpl ; rewrite ?app_nil_r ; forallgg th ].

Ltac conc_gen_ni th :=
  eexists ; split ; [ apply cpl_I ; eapply Sctxt_eq ;
    [ eassumption | pr_arg_ant_mr | pr_arg_suc_mr | reflexivity ] |
  simpl ; rewrite ?app_nil_r ; forallgg th ].

Ltac conc_gen_ni' th :=
  eexists ; split ; [ eapply Sctxt_eq ;
    [ eassumption | pr_arg_ant_mr | pr_arg_suc_mr | reflexivity ] |
  simpl ; rewrite ?app_nil_r ; forallgg th ].

Definition derI' x rules prems ps concl rpc drs :=
  @derI x rules prems ps concl drs rpc.

(* doing contraction requires allowing for two copies of contraction formula
  C to be separated, because a rule such as ImpR for A -> B can
  put A between the two copies of C, in the premise;
  ie use sctr_relR rather than ctr_relR;
  also try for princrule generally as much as possible *)

Lemma can_trf_sctrL_wk_any V rules any ps c 
    (adm_exchL : forall (ant ant' suc : list (PropF V)),
      swapped ant' ant -> adm rules [(ant', suc)] (ant, suc)):
    rsub (cgerule (@trivrule _)) rules -> 
    cgerule (@trivrule _) ps (c : Seqlf V) ->
  can_trf_rules_rc (seqrel (sctr_relL any)) (adm rules) ps c.
Proof. intros rs ct.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct ct. inversion t.  injection H as . subst. 
rewrite cons_singleton in g.
repeat (match goal with | [ H : _ |- _ ] => 
  apply gen_ext_splitR in H ; cD ; subst end).
repeat (match goal with | [ H : gen_ext _ [_] |- _ ] => 
  inversion H ; subst ; clear H end) ;
repeat (match goal with | [ H : gen_ext _ [] |- _ ] => 
  inversion H ; subst ; clear H end).
- eexists. split. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_step.
all: cycle 1.
apply in_adm. apply (rsubD rs). eapply CGctxt. apply trivrule_I.
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
apply sqr_appL1.  apply sqr_appL2.
list_assoc_l.  apply sqr_appR1.  apply sqr_nn2.
apply seqrel_id'.  simpl. apply sctr_relLI.
- eexists. split. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
all: cycle 1.
apply admI. intro drs. simpl in drs.
eapply (derI' _) in drs. (* why not eapply derI' in drs ?? *)
all: cycle 1. apply (rsubD rs). eapply CGctxt. apply trivrule_I.
repeat (eassumption ||
  eapply gen_ext_app || eapply gen_ext_cons || eapply gen_ext_nil).
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
erequire adm_exchL.  erequire adm_exchL.  erequire adm_exchL.
require adm_exchL. all: cycle 1.
inversion adm_exchL. apply X. clear X. 
apply dersrec_singleI. apply drs. swap_tac_Rc.
- eexists. split. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
all: cycle 1.
apply in_adm. apply (rsubD rs). eapply CGctxt. apply trivrule_I.
simpl. rewrite ?app_nil_r.
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
- eexists. split. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
all: cycle 1.
apply in_adm. apply (rsubD rs). eapply CGctxt. apply trivrule_I.
simpl. rewrite ?app_nil_r.
repeat (eassumption || eapply gen_ext_app || 
  eapply gen_ext_cons || eapply gen_ext_extra).
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
Qed.

(* very similar to can_trf_sctrL_wk_any *)
Lemma can_trf_sctrR_wk_any V rules any ps c 
    (adm_exchR : forall (ant suc suc' : list (PropF V)),
      swapped suc' suc -> adm rules [(ant, suc')] (ant, suc)):
    rsub (cgerule (@trivrule _)) rules -> 
    cgerule (@trivrule _) ps (c : Seqlf V) ->
  can_trf_rules_rc (seqrel (sctr_relR any)) (adm rules) ps c.
Proof. intros rs ct.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct ct. inversion t.  injection H as . subst. 
rewrite cons_singleton in g0.
repeat (match goal with | [ H : _ |- _ ] => 
  apply gen_ext_splitR in H ; cD ; subst end).
repeat (match goal with | [ H : gen_ext _ [_] |- _ ] => 
  inversion H ; subst ; clear H end) ;
repeat (match goal with | [ H : gen_ext _ [] |- _ ] => 
  inversion H ; subst ; clear H end).
- eexists. split. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_step.
all: cycle 1.
apply in_adm. apply (rsubD rs). eapply CGctxt. apply trivrule_I.
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
apply sqr_appL1.  apply sqr_appL2.
list_assoc_l.  apply sqr_appR2.  apply sqr_nn1.
apply seqrel_id'.  simpl. apply sctr_relRI.
- eexists. split. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
all: cycle 1.
apply admI. intro drs. simpl in drs.
eapply (derI' _) in drs. (* why not eapply derI' in drs ?? *)
all: cycle 1. apply (rsubD rs). eapply CGctxt. apply trivrule_I.
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
repeat (eassumption ||
  eapply gen_ext_app || eapply gen_ext_cons || eapply gen_ext_nil).
erequire adm_exchR.  erequire adm_exchR.  erequire adm_exchR.
require adm_exchR. all: cycle 1.
inversion adm_exchR. apply X. clear X. 
apply dersrec_singleI. apply drs. swap_tac_Rc.
- eexists. split. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
all: cycle 1.
apply in_adm. apply (rsubD rs). eapply CGctxt. apply trivrule_I.
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
simpl. rewrite ?app_nil_r.
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
- eexists. split. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
all: cycle 1.
apply in_adm. apply (rsubD rs). eapply CGctxt. apply trivrule_I.
repeat (eassumption || eapply gen_ext_app || eapply gen_ext_cons).
simpl. rewrite ?app_nil_r.
repeat (eassumption || eapply gen_ext_app || 
  eapply gen_ext_cons || eapply gen_ext_extra).
Qed.

Definition can_trf_sctrR_wk_any_ak4sw V any ps c :=
  @can_trf_sctrR_wk_any V _ any ps c (@admK4swexchR V) (@rsK4_wk V).
Definition can_trf_sctrL_wk_any_ak4sw V any ps c :=
  @can_trf_sctrL_wk_any V _ any ps c (@admK4swexchL V) (@rsK4_wk V).

Lemma can_trf_sctrR_ck4_any V any ps c: cgerule (@K4prrule V) ps c ->
  can_trf_rules_rc (seqrel (sctr_relR any)) (cgerule (@K4prrule V)) ps c.
Proof. intro k4.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4.  inversion k. clear k. injection H as . subst. 
eexists. split. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
eapply CGctxt. eapply K4prrule_I. exact g.
revert g0. list_assoc_r. simpl. list_assoc_l. intro g0.
apply gen_ext_diff in g0.  destruct g0.
+ inversion i. subst.  apply InT_gen_ext. solve_InT. inversion H0.
+ exact g0.
Qed.

Definition can_trf_sctrR_ck4_any_k4 V any ps c ck4 :=
  can_trf_rules_rc_mono' (@rsK4 V) (@can_trf_sctrR_ck4_any V any ps c ck4).

Lemma can_trf_sctrR_k4_any V any anyr ps c: @K4prrule V ps c ->
  can_trf_rules_rc (seqrel (sctr_relR any)) anyr ps c.
Proof. intro k4.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4. injection H as . subst. 
repeat (list_eq_ncT ; sD). Qed.

(* the only rule containing the formula is the Id rule *)
Inductive idonlyL W rules fml : Type := 
  | idLI : (forall (ps : list (Seql W)) U S, rules ps (fml :: U, S) -> 
    (U = []) * (S = [fml : W]) * (ps = [])) -> idonlyL W rules fml.

Inductive idonlyR W rules fml : Type := 
  | idRI : (forall (ps : list (Seql W)) U S, rules ps (U, fml :: S) -> 
    (U = [fml : W]) * (S = []) * (ps = [])) -> idonlyR W rules fml.

Lemma ido_BBoxR V fml : idonlyR (@princrule V) (BBox fml).
Proof. apply idRI. intros. inversion X ;
subst ; rename_last r ; inversion r ; tauto. Qed.

Lemma ido_BBoxL V fml : idonlyL (@princrule V) (BBox fml).
Proof. apply idLI. intros. inversion X ;
subst ; rename_last r ; inversion r ; tauto. Qed.

Lemma ido_WBoxR V fml : idonlyR (@princrule V) (WBox fml).
Proof. apply idRI. intros. inversion X ;
subst ; rename_last r ; inversion r ; tauto. Qed.

Lemma ido_WBoxL V fml : idonlyL (@princrule V) (WBox fml).
Proof. apply idLI. intros. inversion X ;
subst ; rename_last r ; inversion r ; tauto. Qed.

Lemma ido_VarR V pp : idonlyR (@princrule V) (Var pp).
Proof. apply idRI. intros. inversion X ;
subst ; rename_last r ; inversion r ; tauto. Qed.

Lemma ido_VarL V pp : idonlyL (@princrule V) (Var pp).
Proof. apply idLI. intros. inversion X ;
subst ; rename_last r ; inversion r ; tauto. Qed.

Lemma ido_BotR V : idonlyR (@princrule V) (@Bot _).
Proof. apply idRI. intros. inversion X ;
subst ; rename_last r ; inversion r ; tauto. Qed.

(* argument thm is eg idk4goal or idsprgoal *)
Ltac use_idog thm fml ido p := intro ; subst ; destruct ido as [idoe] ;
  apply idoe in p ; cD ; subst ; 
  apply (thm _ fml _ _ _) ; solve_InT.
Ltac use_idocg thm fml ido p :=
  match goal with
    | [ H : princrule _ (_, fml :: _) |- _ ] => use_idog thm fml ido p
    | [ H : princrule _ (fml :: _, _) |- _ ] => use_idog thm fml ido p
    end.

Lemma can_trf_sctrL_spr_ido V fml ps c: 
  idonlyL (@princrule V) fml -> seqrule (@princrule V) ps c ->
  can_trf_rules_rc (seqrel (sctr_relL fml)) (seqrule (@princrule V)) ps c.
Proof. intros ido spr.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
remember fml as fmld. rewrite Heqfmld in H.
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.

destruct spr.
(* now try differently from above by not destruct-ing princrule *)
destruct c as [ca cs]. unfold seqext in H. injection H as .
clear H0. (* or subst c'. *)
revert Heqfmld. (* so subst doesn't occur *)

(* note in following, subst after acacDe'T2 can result in more 
  u ++ v = x ++ y *)
repeat (acacDe'T2 ; subst ; repeat (list_eq_ncT ; sD ; subst)) ;
simpl ; rewrite ?app_nil_r ; 
simpl in p ; rewrite ?app_nil_r in p ; (* 63 subgoals *)
repeat (apply princrule_appL in p ; sD ; subst) ; (* 84 sgs *)
repeat (apply princrule_appR in p ; sD ; subst) ; (* 112 sgs *)
try (list_eq_ncT ; sD ; subst) ; (* does more than just discriminate *)
try (use_idocg idsprgoal fml ido p) ;

try (match goal with
  | [ H : princrule _ ([], _) |- _ ] => conc_ant_nil
  end) ; (* solves 4 goals *)

conc_gen sqr_sctr_relLI. Qed.

Definition can_trf_sctrL_spr_ido_k4 V fml ps c ido spr :=
  can_trf_rules_rc_mono' rscpl 
  (@can_trf_sctrL_spr_ido V fml ps c ido spr).
Definition can_trf_sctrL_spr_ido_k4sw V fml ps c ido spr :=
  can_trf_rules_rc_mono' rscplsw 
  (@can_trf_sctrL_spr_ido V fml ps c ido spr).
Definition can_trf_sctrL_spr_ido_ak4sw V fml ps c ido spr :=
  can_trf_rules_rc_mono' (rsub_trans rscplsw (@rsub_adm _ _)) 
  (@can_trf_sctrL_spr_ido V fml ps c ido spr).

Check can_trf_sctrL_spr_ido_k4.  Check can_trf_sctrL_spr_ido_k4sw.

Lemma can_trf_sctrR_spr_ido V fml ps c: 
  idonlyR (@princrule V) fml -> seqrule (@princrule V) ps c ->
  can_trf_rules_rc (seqrel (sctr_relR fml)) (seqrule (@princrule V)) ps c.
Proof. intros ido spr.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
remember fml as fmld. rewrite Heqfmld in H.
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.

destruct spr.
(* now try differently from above by not destruct-ing princrule *)
destruct c as [ca cs]. unfold seqext in H. injection H as .
clear H0. (* or subst c'. *)
revert Heqfmld. (* so subst doesn't occur *)

(* note in following, subst after acacDe'T2 can result in more 
  u ++ v = x ++ y *)
repeat (acacDe'T2 ; subst ; repeat (list_eq_ncT ; sD ; subst)) ;
simpl ; rewrite ?app_nil_r ; 
simpl in p ; rewrite ?app_nil_r in p ; (* 63 subgoals *)
repeat (apply princrule_appL in p ; sD ; subst) ; (* 84 sgs *)
repeat (apply princrule_appR in p ; sD ; subst) ; (* 112 sgs *)
try (list_eq_ncT ; sD ; subst) ; (* does more than just discriminate *)
try (use_idocg idsprgoal fml ido p) ;

try (match goal with
  | [ H : princrule _ (_, []) |- _ ] => conc_suc_nil
  end) ; (* solves 4 goals *)

conc_gen sqr_sctr_relRI. Qed.

Definition can_trf_sctrR_spr_ido_k4 V fml ps c ido spr :=
  can_trf_rules_rc_mono' rscpl 
  (@can_trf_sctrR_spr_ido V fml ps c ido spr).
Definition can_trf_sctrR_spr_ido_k4sw V fml ps c ido spr :=
  can_trf_rules_rc_mono' rscplsw 
  (@can_trf_sctrR_spr_ido V fml ps c ido spr).
Definition can_trf_sctrR_spr_ido_ak4sw V fml ps c ido spr :=
  can_trf_rules_rc_mono' (rsub_trans rscplsw (@rsub_adm _ _)) 
  (@can_trf_sctrR_spr_ido V fml ps c ido spr).

Check can_trf_sctrR_spr_ido_k4.  Check can_trf_sctrR_spr_ido_k4sw.

(* don't actually need this result but wanted to show how to do it
  much more efficiently than originally *)
Lemma can_trf_delR_Bot_sp V ps c: seqrule (@princrule V) ps c -> 
  can_trf_rules_rc (seqrel (del_relR (@Bot V))) (seqrule (@princrule V)) ps c.
Proof. intro sp.  unfold can_trf_rules_rc. intros c' sdr.
inversion sdr. clear sdr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct sp.  destruct c as [ca cs].
unfold seqext in H. injection H as .
repeat (acacDe'T2 ; subst ; repeat (list_eq_ncT ; sD ; subst)) ;
simpl ; rewrite ?app_nil_r ;
simpl in p ; rewrite ?app_nil_r in p ;
repeat (apply princrule_appL in p ; sD ; subst) ; 
repeat (apply princrule_appR in p ; sD ; subst) ; (* 28 sgs *)
try (list_eq_ncT ; sD ; subst). (* 24 sgs *) (* OK *)

all: try (conc_gen_ni' sqr_del_relRI). (* 8 sgs *) 

all: pose (@ido_BotR V) ; inversion i ; rename_last HH ;
apply HH in p ; cD ; subst ; clear HH ;
apply botspgoal ; solve_InT.
Qed.
Check can_trf_delR_Bot_sp.

(* first, simpler rule without implicit weakening *)
Lemma can_trf_delR_Bot_k4 V ps c: @K4prrule V ps c -> 
  can_trf_rules_rc (seqrel (del_relR (@Bot V))) (@K4prrule V) ps c.
Proof. intro k4.  unfold can_trf_rules_rc. intros c' sdr.
inversion sdr. clear sdr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4.  injection H as . subst. 
unfold seqext. simpl. rewrite H. clear H.
acacD'T2 ; subst.  + discriminate H0.  + list_eq_ncT. destruct H2. Qed.
Check can_trf_delR_Bot_k4.

Lemma can_trf_delR_Bot_ck4 V ps c: cgerule (@K4prrule V) ps c -> 
  can_trf_rules_rc (seqrel (del_relR (@Bot V))) (cgerule (@K4prrule V)) ps c.
Proof. intro k4.  unfold can_trf_rules_rc. intros c' sdr.
inversion sdr. clear sdr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4. 
inversion k. clear k. injection H as . subst. 
apply gen_ext_one in g0. apply InT_split in g0. cD.
acacD'T2 ; subst.
+ discriminate g5.
+ eexists. split. unfold seqext. simpl.
eapply CGctxt. 2: apply g. eapply K4prrule_I.
apply InT_gen_ext. solve_InT.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
+ discriminate g5.
+ eexists. split. unfold seqext. simpl.
eapply CGctxt. 2: apply g. eapply K4prrule_I.
apply InT_gen_ext. solve_InT.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
Qed.
Check can_trf_delR_Bot_ck4.

(* now, for weakening rule *)
Lemma can_trf_delR_Bot_wk V ps c: cgerule (@trivrule _) ps c -> 
  can_trf_rules_rc (seqrel (del_relR (@Bot V))) (cgerule (@trivrule _)) ps c.
Proof. intro wk.  unfold can_trf_rules_rc. intros c' sdr.
inversion sdr. clear sdr. destruct X.
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct wk. inversion t. subst. injection H as . subst.
unfold seqext. simpl.
apply gen_ext_splitR in g0. cD.  subst.
inversion g4 ; clear g4 ; subst.
- exists [(ca, g0 ++ l)]. split.
+ eapply CGctxt. apply trivrule_I. exact g.
apply (gen_ext_app X g3).
+ apply ForallT_singleI.
eexists. split. apply InT_eq. apply rT_step.
eapply (Sctxt_relI_eq _ _ _ _ _ []). eapply del_relRI.
simpl. reflexivity.  simpl. reflexivity. 
- eexists. split. 
+ eapply CGctxt. apply trivrule_I. exact g.
apply (gen_ext_app X g3).
+ apply ForallT_singleI.
eexists. split. apply InT_eq. apply rT_refl.
Qed.
Check can_trf_delR_Bot_wk.

Lemma can_trf_delR_Bot V ps c: K4rules ps c -> 
  can_trf_rules_rc (seqrel (del_relR (@Bot V))) K4rules ps c.
Proof. intro k4. destruct k4. 
apply (can_trf_rules_rc_mono' (@rsK4 _) (can_trf_delR_Bot_ck4 c0)).
apply (can_trf_rules_rc_mono' rscpl (can_trf_delR_Bot_sp s)).
Qed.
Check can_trf_delR_Bot.

Lemma can_trf_delR_Bot_k4_sw V ps c: K4rules_sw ps c -> 
  can_trf_rules_rc (seqrel (del_relR (@Bot V))) K4rules_sw ps c.
Proof. intro k4. destruct k4. 
apply (can_trf_rules_rc_mono' rsK4_sw (can_trf_delR_Bot_k4 k)).
apply (can_trf_rules_rc_mono' rscplsw (can_trf_delR_Bot_sp s)).
apply (can_trf_rules_rc_mono' rsK4_wk (can_trf_delR_Bot_wk c0)).
Qed.
Check can_trf_delR_Bot_k4_sw.  

Definition K4_delBotR V := der_trf_rc (@can_trf_delR_Bot V).
Definition K4_ctrBotR V c d c' sqrc := 
  @K4_delBotR V c d c' (rsubD (@sqr_del_ctrR (PropF V) (Bot V)) c c' sqrc).
Definition K4_sctrBotR V c d c' sqrc := 
  @K4_delBotR V c d c' (rsubD (@sqr_del_sctrR (PropF V) (Bot V)) c c' sqrc).
Check K4_sctrBotR.  (* NB K4_sctrBotR is same as K4_sctrR_Bot 
  which is got using more general approach *)

Definition K4_sw_delBotR V := der_trf_rc (@can_trf_delR_Bot_k4_sw V).
Definition K4_sw_ctrBotR V c d c' sqrc := 
  @K4_sw_delBotR V c d c' (rsubD (@sqr_del_ctrR (PropF V) (Bot V)) c c' sqrc).
Definition K4_sw_sctrBotR V c d c' sqrc := 
  @K4_sw_delBotR V c d c' (rsubD (@sqr_del_sctrR (PropF V) (Bot V)) c c' sqrc).

Definition can_trf_sctrR_spr_pp_k4 V pp ps c :=
  @can_trf_sctrR_spr_ido_k4 V (Var pp) ps c (ido_VarR pp).
Definition can_trf_sctrR_spr_pp_k4sw V pp ps c :=
  @can_trf_sctrR_spr_ido_k4sw V (Var pp) ps c (ido_VarR pp).
Definition can_trf_sctrR_spr_pp_ak4sw V pp ps c :=
  @can_trf_sctrR_spr_ido_ak4sw V (Var pp) ps c (ido_VarR pp).
  
Lemma can_trf_sctrR_pp_k4 V pp ps c: K4rules ps c ->
  can_trf_rules_rc (seqrel (sctr_relR (Var pp))) (K4rules (V:=V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrR_ck4_any_k4. assumption.
apply can_trf_sctrR_spr_pp_k4. assumption. Qed.
Check can_trf_sctrR_pp_k4.

Lemma can_trf_sctrR_pp_k4sw V pp ps c: K4rules_sw ps c ->
  can_trf_rules_rc (seqrel (sctr_relR (Var pp))) (adm (@K4rules_sw V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrR_k4_any. assumption. 
apply can_trf_sctrR_spr_pp_ak4sw. assumption. 
apply can_trf_sctrR_wk_any_ak4sw. assumption.
Qed.

Definition K4_sctrR_pp V pp := der_trf_rc (@can_trf_sctrR_pp_k4 V pp).
Definition K4sw_sctrR_pp V pp := der_trf_rc_adm (@can_trf_sctrR_pp_k4sw V pp).
Check K4_sctrR_pp.  Check K4sw_sctrR_pp.

Lemma K4_sctrR_pp_rel_adm V pp :
  rel_adm (@K4rules V) (seqrel (sctr_relR (Var pp))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4_sctrR_pp ; eassumption. Qed.

Lemma K4sw_sctrR_pp_rel_adm V pp :
  rel_adm (@K4rules_sw V) (seqrel (sctr_relR (Var pp))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_sctrR_pp ; eassumption. Qed.

(* right contraction of Imp A B by induction on the formula, general version *)
Lemma gen_sctrR_Imp V rules (A B : PropF V) 
  (impRinv : rel_adm rules (seqrel (@ImpRinv V))):
  rsub (seqrule (@ImpRrule V)) rules -> 
  rel_adm rules (seqrel (sctr_relL A)) -> 
  rel_adm rules (seqrel (sctr_relR B)) -> 
  rel_adm rules (seqrel (sctr_relR (Imp A B))).
Proof. intros rs ctra ctrb.  apply rel_admI. 
intros *. intro sqrc. apply radmI.
intro derp. destruct sqrc. destruct s.
unfold seqext in derp.
(* invert one instance of Imp A B *)
eapply impRinv in derp.  all:cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ Φ1 Φ2 Ψ1 (S ++ [Imp A B] ++ Ψ2)).
apply (ImpRinv_I A B).  list_assoc_r. simpl. reflexivity.  reflexivity.
(* invert 2nd instance of Imp A B *)
eapply impRinv in derp.  all:cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ Φ1 (A :: Φ2) (Ψ1 ++ B :: S) Ψ2).
apply (ImpRinv_I A B).  list_assoc_r. simpl. reflexivity.  reflexivity.
revert derp. list_assoc_r. simpl. intro derp.
(* contract A on the left *)
destruct ctra. erequire r.  erequire r.  require r.
eapply Sctxt_relI_eq.  apply (sctr_relLI A []).
reflexivity.  reflexivity.
destruct r.  simpl in d. apply d in derp. clear d.
(* contract B on the right *)
destruct ctrb.  erequire r.  erequire r.  require r.
eapply Sctxt_relI_eq.  apply (sctr_relRI B S).
reflexivity.  reflexivity.
destruct r.  revert d. list_assoc_r'. simpl. intro d.
apply d in derp. clear d.
(* apply ImpR rule to contracted premises *)
eapply derI. apply (rsubD rs). eapply Sctxt_eq.  apply ImpRrule_I.
reflexivity. simpl.  reflexivity.  reflexivity.
simpl. apply dersrec_singleI. apply derp.  Qed.

Definition K4_sctrR_Imp V A B :=
  (@gen_sctrR_Imp V _ A B (@ra_K4_ImpRinv V)) (@rs_ImpR_k4 V).
Definition K4sw_sctrR_Imp V A B :=
  (@gen_sctrR_Imp V _ A B (@ra_K4sw_ImpRinv V)) (@rs_ImpR_k4sw V).

(* left contraction of Imp A B by induction on the formula, general version *)
Lemma gen_sctrL_Imp V rules A B 
  (impLinv1 : rel_adm rules (seqrel (@ImpLinv1 V)))
  (impLinv2 : rel_adm rules (seqrel (@ImpLinv2 V))):
  rsub (seqrule (@ImpLrule V)) rules -> 
  rel_adm rules (seqrel (sctr_relR A)) -> 
  rel_adm rules (seqrel (sctr_relL B)) -> 
  rel_adm rules (seqrel (sctr_relL (Imp A B))).
Proof. intros rs ctra ctrb.  apply rel_admI. 
intros *. intro sqrc. apply radmI.
destruct sqrc. destruct s.
intro derp.  unfold seqext in derp.  pose derp as d1. pose derp as d2.

(* firstly, invert to get premise B |- . *)
(* invert one instance of Imp A B *)
eapply impLinv1 in d1.  all:cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ Φ1 (S ++ [Imp A B] ++ Φ2) Ψ1 Ψ2).
apply (ImpLinv1_I A B).  list_assoc_r. simpl. reflexivity.  reflexivity.
(* invert 2nd instance of Imp A B *)
eapply impLinv1 in d1.  all:cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ (Φ1 ++ B :: S) Φ2 Ψ1 Ψ2).
apply (ImpLinv1_I A B).  list_assoc_r. simpl. reflexivity.  reflexivity.
revert d1. list_assoc_r. simpl. intro d1.
(* contract B on the left *)
destruct ctrb. erequire r.  erequire r.  require r.
eapply Sctxt_relI_eq.  apply (sctr_relLI B S).
reflexivity.  reflexivity.
destruct r.  revert d. list_assoc_r'. simpl. intro d.
apply d in d1. clear d.

(* secondly, invert to get premise . |- A *)
(* invert one instance of Imp A B *)
eapply impLinv2 in d2.  all:cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ Φ1 (S ++ [Imp A B] ++ Φ2) Ψ1 Ψ2).
apply (ImpLinv2_I A B).  list_assoc_r. simpl. reflexivity.  reflexivity.
(* invert 2nd instance of Imp A B *)
eapply impLinv2 in d2.  all:cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ (Φ1 ++ S) Φ2 Ψ1 (A :: Ψ2)).
apply (ImpLinv2_I A B).  list_assoc_r. simpl. reflexivity.  reflexivity.
revert d2. list_assoc_r. simpl. intro d2.
(* contract A on the right *)
destruct ctra. erequire r.  erequire r.  require r.
eapply Sctxt_relI_eq.  apply (sctr_relRI A []).
reflexivity.  reflexivity.
destruct r.  revert d. list_assoc_r'. simpl. intro d.
apply d in d2. clear d.

(* apply ImpL rule to contracted premises *)
eapply derI. apply (rsubD rs). eapply Sctxt_eq.  apply ImpLrule_I.
simpl. reflexivity. simpl.  reflexivity.  reflexivity.
simpl. apply dlCons. apply d1. 
apply dlCons. apply d2.  apply dlNil.  Qed.

Definition K4_sctrL_Imp V A B := (@gen_sctrL_Imp V _ A B
  (@ra_K4_ImpLinv1 V) (@ra_K4_ImpLinv2 V)) (@rs_ImpL_k4 V).
Definition K4sw_sctrL_Imp V A B := (@gen_sctrL_Imp V _ A B
  (@ra_K4sw_ImpLinv1 V) (@ra_K4sw_ImpLinv2 V)) (@rs_ImpL_k4sw V).

Check K4_sctrL_Imp.  Check K4_sctrR_Imp. 
Check K4sw_sctrL_Imp.  Check K4sw_sctrR_Imp. 

Lemma can_trf_sctrL_ck4_pp_ck4 V pp ps c: cgerule (@K4prrule V) ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (Var pp))) (cgerule (@K4prrule V)) ps c.
Proof. intro k4.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
remember pp as ppd. rewrite Heqppd in H.
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4.  inversion k. clear k. injection H as . subst. 

eexists. split. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
eapply CGctxt. eapply K4prrule_I.
revert g. list_assoc_r. simpl. list_assoc_l. intro g.
apply gen_ext_diff in g.  destruct g.
+ apply InT_mapE in i. cD. discriminate.
+ exact g.
+ exact g0.
Qed.

(* DONE sw to HERE *)
Definition can_trf_sctrL_ck4_pp_k4 V pp ps c ck4 := 
  can_trf_rules_rc_mono' (@rsK4 V) (@can_trf_sctrL_ck4_pp_ck4 V pp ps c ck4).

(* without implicit weakening, this is trivial *)
Lemma can_trf_sctrL_k4_pp_any V pp any ps c: @K4prrule V ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (Var pp))) any ps c.
Proof. intro k4.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4.  injection H as . subst. 
apply eq_sym in H.  apply map_app_ex in H.  cD.
destruct H2 ; simpl in H3 ; try (injection H3 as ) ;  discriminate H3. Qed.

(* identical proof for BBox *)
Lemma can_trf_sctrL_k4_BBox_any V fml any ps c: @K4prrule V ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (BBox fml))) any ps c.
Proof. intro k4.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4.  injection H as . subst. 
apply eq_sym in H.  apply map_app_ex in H.  cD.
destruct H2 ; simpl in H3 ; try (injection H3 as ) ;  discriminate H3. Qed.


(* this for the case where there is a BBox but no rules for it,
  can we generalise it? do we want to? (better just omit BBox!) *)
Lemma can_trf_sctrL_ck4_BBox_k4 V fml ps c: cgerule (@K4prrule V) ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (BBox fml))) (K4rules (V:=V)) ps c.
Proof. intro k4.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
remember fml as fmld. rewrite Heqfmld in H.
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4.  inversion k. clear k. injection H as . subst. 

eexists. split. apply K4_I. unfold seqext. simpl.
all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq. apply rT_refl.
eapply CGctxt. eapply K4prrule_I.
revert g. list_assoc_r. simpl. list_assoc_l. intro g.
apply gen_ext_diff in g.  destruct g.
+ apply InT_mapE in i. cD. discriminate.
+ exact g.
+ exact g0.
Qed.

Definition can_trf_sctrL_spr_pp_k4 V pp ps c :=
  @can_trf_sctrL_spr_ido_k4 V (Var pp) ps c (ido_VarL pp).
Definition can_trf_sctrL_spr_pp_k4sw V pp ps c :=
  @can_trf_sctrL_spr_ido_k4sw V (Var pp) ps c (ido_VarL pp).
Definition can_trf_sctrL_spr_pp_ak4sw V pp ps c :=
  @can_trf_sctrL_spr_ido_ak4sw V (Var pp) ps c (ido_VarL pp).

Lemma can_trf_sctrL_pp_k4 V pp ps c: K4rules ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (Var pp))) (K4rules (V:=V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrL_ck4_pp_k4. assumption.
apply can_trf_sctrL_spr_pp_k4. assumption. Qed.
Check can_trf_sctrL_pp_k4.

Lemma can_trf_sctrL_pp_ak4sw V pp ps c: K4rules_sw ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (Var pp))) (adm (@K4rules_sw V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrL_k4_pp_any. assumption. 
apply can_trf_sctrL_spr_pp_ak4sw. assumption. 
apply can_trf_sctrL_wk_any_ak4sw. assumption.
Qed.

Definition K4_sctrL_pp V pp := der_trf_rc (@can_trf_sctrL_pp_k4 V pp).
Definition K4sw_sctrL_pp V pp := der_trf_rc_adm (@can_trf_sctrL_pp_ak4sw V pp).
Check K4_sctrL_pp. Check K4sw_sctrL_pp.

Lemma K4_sctrL_pp_rel_adm V pp :
  rel_adm (@K4rules V) (seqrel (sctr_relL (Var pp))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4_sctrL_pp ; eassumption. Qed.

Lemma K4sw_sctrL_pp_rel_adm V pp :
  rel_adm (@K4rules_sw V) (seqrel (sctr_relL (Var pp))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_sctrL_pp ; eassumption. Qed.

Definition can_trf_sctrR_spr_Bot_k4 V ps c :=
  @can_trf_sctrR_spr_ido_k4 V (Bot V) ps c (ido_BotR V).
Definition can_trf_sctrR_spr_Bot_k4sw V ps c :=
  @can_trf_sctrR_spr_ido_k4sw V (Bot V) ps c (ido_BotR V).
Definition can_trf_sctrR_spr_Bot_ak4sw V ps c :=
  @can_trf_sctrR_spr_ido_ak4sw V (Bot V) ps c (ido_BotR V).
  
Lemma can_trf_sctrR_Bot_k4 V ps c: K4rules ps c ->
  can_trf_rules_rc (seqrel (sctr_relR (Bot V))) (@K4rules V) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrR_ck4_any_k4. assumption.
apply can_trf_sctrR_spr_Bot_k4. assumption. Qed.

Lemma can_trf_sctrR_Bot_ak4sw V ps c: K4rules_sw ps c ->
  can_trf_rules_rc (seqrel (sctr_relR (Bot V))) (adm (@K4rules_sw V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrR_k4_any. assumption.
apply can_trf_sctrR_spr_Bot_ak4sw. assumption.
apply can_trf_sctrR_wk_any_ak4sw. assumption. Qed.
Check can_trf_sctrR_Bot_k4.  Check can_trf_sctrR_Bot_ak4sw.

Definition K4_sctrR_Bot V := der_trf_rc (@can_trf_sctrR_Bot_k4 V).
Definition K4sw_sctrR_Bot V := der_trf_rc_adm (@can_trf_sctrR_Bot_ak4sw V).
Check K4_sctrR_Bot.  Check K4sw_sctrR_Bot.

Lemma K4_sctrR_Bot_rel_adm V :
  rel_adm K4rules (seqrel (sctr_relR (@Bot V))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4_sctrR_Bot ; eassumption. Qed.

Lemma K4_sctrL_Bot_rel_adm V :
  rel_adm K4rules (seqrel (sctr_relL (@Bot V))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4_sctrL_Bot ; eassumption. Qed.

Lemma K4sw_sctrL_Bot_rel_adm V :
  rel_adm K4rules_sw (seqrel (sctr_relL (@Bot V))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_sctrL_Bot ; eassumption. Qed.

Lemma K4sw_sctrR_Bot_rel_adm V :
  rel_adm K4rules_sw (seqrel (sctr_relR (@Bot V))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_sctrR_Bot ; eassumption. Qed.

Definition can_trf_sctrR_spr_WBox_k4 V fml ps c :=
  @can_trf_sctrR_spr_ido_k4 V (WBox fml) ps c (ido_WBoxR fml).
Definition can_trf_sctrR_spr_WBox_ak4sw V fml ps c :=
  @can_trf_sctrR_spr_ido_ak4sw V (WBox fml) ps c (ido_WBoxR fml).
  
Lemma can_trf_sctrR_WBox_k4 V fml ps c: K4rules ps c ->
  can_trf_rules_rc (seqrel (sctr_relR (WBox fml))) (K4rules (V:=V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrR_ck4_any_k4. assumption.
apply can_trf_sctrR_spr_WBox_k4. assumption. Qed.
  
Lemma can_trf_sctrR_WBox_ak4sw V fml ps c: K4rules_sw ps c ->
  can_trf_rules_rc (seqrel (sctr_relR (WBox fml))) (adm (@K4rules_sw V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrR_k4_any. assumption.
apply can_trf_sctrR_spr_WBox_ak4sw. assumption.
apply can_trf_sctrR_wk_any_ak4sw. assumption. Qed.

Check can_trf_sctrR_WBox_k4.  Check can_trf_sctrR_WBox_ak4sw.

Definition K4_sctrR_WBox V fml := der_trf_rc (@can_trf_sctrR_WBox_k4 V fml).
Definition K4sw_sctrR_WBox V fml := 
  der_trf_rc_adm (@can_trf_sctrR_WBox_ak4sw V fml).
Check K4_sctrR_WBox.  Check K4sw_sctrR_WBox.

Lemma K4_sctrR_WBox_rel_adm V fml :
  rel_adm (@K4rules V) (seqrel (sctr_relR (WBox fml))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4_sctrR_WBox ; eassumption. Qed.

Lemma K4sw_sctrR_WBox_rel_adm V fml :
  rel_adm (@K4rules_sw V) (seqrel (sctr_relR (WBox fml))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_sctrR_WBox ; eassumption. Qed.

Definition can_trf_sctrL_spr_BBox_k4 V fml ps c :=
  @can_trf_sctrL_spr_ido_k4 V (BBox fml) ps c (ido_BBoxL fml).
Definition can_trf_sctrL_spr_BBox_ak4sw V fml ps c :=
  @can_trf_sctrL_spr_ido_ak4sw V (BBox fml) ps c (ido_BBoxL fml).
  
Lemma can_trf_sctrL_BBox_k4 V fml ps c: K4rules ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (BBox fml))) (K4rules (V:=V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrL_ck4_BBox_k4. assumption.
apply can_trf_sctrL_spr_BBox_k4. assumption. Qed.
  
Lemma can_trf_sctrL_BBox_ak4sw V fml ps c: K4rules_sw ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (BBox fml))) (adm (@K4rules_sw V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrL_k4_BBox_any. assumption. 
apply can_trf_sctrL_spr_BBox_ak4sw. assumption.
apply can_trf_sctrL_wk_any_ak4sw. assumption. Qed.

Check can_trf_sctrL_BBox_k4.  Check can_trf_sctrL_BBox_ak4sw.

Definition K4_sctrL_BBox V fml := der_trf_rc (@can_trf_sctrL_BBox_k4 V fml).
Definition K4sw_sctrL_BBox V fml := 
  der_trf_rc_adm (@can_trf_sctrL_BBox_ak4sw V fml).
Check K4_sctrL_BBox.  Check K4sw_sctrL_BBox.

Lemma K4_sctrL_BBox_rel_adm V fml :
  rel_adm (@K4rules V) (seqrel (sctr_relL (BBox fml))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4_sctrL_BBox ; eassumption. Qed.

Lemma K4sw_sctrL_BBox_rel_adm V fml :
  rel_adm (@K4rules_sw V) (seqrel (sctr_relL (BBox fml))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_sctrL_BBox ; eassumption. Qed.

Definition can_trf_sctrR_spr_BBox_k4 V fml ps c :=
  @can_trf_sctrR_spr_ido_k4 V (BBox fml) ps c (ido_BBoxR fml).
Definition can_trf_sctrR_spr_BBox_ak4sw V fml ps c :=
  @can_trf_sctrR_spr_ido_ak4sw V (BBox fml) ps c (ido_BBoxR fml).
  
Lemma can_trf_sctrR_BBox_k4 V fml ps c: K4rules ps c ->
  can_trf_rules_rc (seqrel (sctr_relR (BBox fml))) (K4rules (V:=V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrR_ck4_any_k4. assumption.
apply can_trf_sctrR_spr_BBox_k4. assumption. Qed.
  
Lemma can_trf_sctrR_BBox_ak4sw V fml ps c: K4rules_sw ps c ->
  can_trf_rules_rc (seqrel (sctr_relR (BBox fml))) (adm (@K4rules_sw V)) ps c.
Proof. intro k4. destruct k4.
apply can_trf_sctrR_k4_any. assumption.
apply can_trf_sctrR_spr_BBox_ak4sw. assumption.
apply can_trf_sctrR_wk_any_ak4sw. assumption. Qed.

Check can_trf_sctrR_BBox_k4.  Check can_trf_sctrR_BBox_ak4sw.

Definition K4_sctrR_BBox V fml := der_trf_rc (@can_trf_sctrR_BBox_k4 V fml).
Definition K4sw_sctrR_BBox V fml := 
  der_trf_rc_adm (@can_trf_sctrR_BBox_ak4sw V fml).
Check K4_sctrR_BBox.  Check K4sw_sctrR_BBox.

Lemma K4_sctrR_BBox_rel_adm V fml :
  rel_adm (@K4rules V) (seqrel (sctr_relR (BBox fml))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4_sctrR_BBox ; eassumption. Qed.

Lemma K4sw_sctrR_BBox_rel_adm V fml :
  rel_adm (@K4rules_sw V) (seqrel (sctr_relR (BBox fml))).
Proof. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_sctrR_BBox ; eassumption. Qed.

(* summary of contraction results so far 
L Var Check K4_sctrL_pp_rel_adm. Check K4_sctrL_pp.
R Var Check K4_sctrR_pp_rel_adm. Check K4_sctrR_pp.
L Imp Check K4_sctrL_Imp. 
R Imp Check K4_sctrR_Imp. 
L Bot Check K4_sctrL_Bot. Check K4_sctrL_Bot_rel_adm.
R Bot Check K4_sctrR_Bot. Check K4_sctrR_Bot_rel_adm.
R WBox Check K4_sctrR_WBox. Check K4_sctrR_WBox_rel_adm.
*)
(* how to prove it for WBox on the left?
  assume contraction admissible for smaller formulae, 
  then use der_trf_rc_adm, because one contraction for Wbox X,
  and one contraction for X using admissibility
*)

Definition can_trf_sctrL_spr_WBox_k4 V fml ps c :=
  @can_trf_sctrL_spr_ido_k4 V (WBox fml) ps c (ido_WBoxL fml).
Definition can_trf_sctrL_spr_WBox_k4sw V fml ps c :=
  @can_trf_sctrL_spr_ido_k4sw V (WBox fml) ps c (ido_WBoxL fml).

Ltac map_eq :=
  (match goal with
    | [ H : map _ _ = (_ ++ _) |- _ ] => apply map_app_ex in H ; cD 
    | [ H : map _ _ = (_ :: _) |- _ ] => apply map_cons_ex' in H ; cD 
    | [ H : map _ _ = [] |- _ ] => apply map_eq_nil in H 
    end).
  
Lemma can_trf_sctrL_k4_WBox_ak4sw V fml ps c: 
  rel_adm K4rules_sw (seqrel (sctr_relL fml)) -> @K4prrule V ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (WBox fml))) (adm K4rules_sw) ps c.
  
Proof. intros ra k4.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4. injection H as . subst. 

(* neither occurrence of contraction formula is weakened in,
  premise needs to be contracted (both boxed and unboxed formula) *)
eexists. split. all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq.  apply rT_step.
eapply (Sctxt_relI_eq _ _ _ _ _ Φ1 (Φ2 ++ Gam) [] [phi]).
apply (sctr_relLI _ S). simpl. rewrite <- H. list_eq_assoc.  reflexivity.
simpl. apply eq_sym in H.

repeat map_eq. subst.
repeat (match goal with | [ H : WBox _ = WBox _ |- _ ] => injection H as end).  
subst.

destruct ra.  erequire r.  erequire r.  require r. 
eapply (Sctxt_relI _ _ _ 
  (map (@WBox V) H ++ WBox H15 :: map (@WBox V) H9 ++
        map (WBox (V:=V)) H10 ++ H) H10 [] [phi]).
apply (sctr_relLI H15 H9).
destruct r.  apply admI.
intro drs. apply dersrec_singleD in drs.
unfold seqext in d. simpl in d. simpl in drs.
eapply arg_cong_imp' in drs.
apply d in drs.  2: list_eq_assoc. clear d.

eapply derI. apply K4_sw_I.  
eapply arg_cong_imp'.
apply (K4prrule_I (H ++ H15 :: H9 ++ H10)).
rewrite map_app. simpl.  rewrite map_app.  rewrite H1. reflexivity.
rewrite map_app. simpl.  rewrite map_app.
apply dersrec_singleI.
revert drs. list_assoc_r. intro drs. exact drs. Qed.

Check can_trf_sctrL_k4_WBox_ak4sw.

(* very similar to above and not needed
Lemma can_trf_sctrL_k4_WBox_ak4 V fml ps c: 
  rel_adm K4rules (seqrel (sctr_relL fml)) -> @K4prrule V ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (WBox fml))) (adm (@K4rules V)) ps c.
  
Proof. intros ra k4.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4. injection H as . subst. 

(* neither occurrence of contraction formula is weakened in,
  premise needs to be contracted (both boxed and unboxed formula) *)
eexists. split. all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq.  apply rT_step.
eapply (Sctxt_relI_eq _ _ _ _ _ Φ1 (Φ2 ++ Gam) [] [phi]).
apply (sctr_relLI _ S). simpl. rewrite <- H. list_eq_assoc.  reflexivity.
simpl. apply eq_sym in H.

repeat map_eq. subst.
repeat (match goal with | [ H : WBox _ = WBox _ |- _ ] => injection H as end).  
subst.

destruct ra.  erequire r.  erequire r.  require r. 
eapply (Sctxt_relI _ _ _ 
  (map (@WBox V) H ++ WBox H15 :: map (@WBox V) H9 ++
        map (WBox (V:=V)) H10 ++ H) H10 [] [phi]).
apply (sctr_relLI H15 H9).
destruct r.  apply admI.
intro drs. apply dersrec_singleD in drs.
unfold seqext in d. simpl in d. simpl in drs.
eapply arg_cong_imp' in drs.
apply d in drs.  2: list_eq_assoc. clear d.

eapply derI. apply K4_I.  eapply CGctxt. 
apply (K4prrule_I (H ++ H15 :: H9 ++ H10)).
rewrite map_app. simpl.  rewrite map_app.  apply gen_ext_refl.
rewrite H1.  apply gen_ext_refl.
rewrite map_app. simpl.  rewrite map_app.
apply dersrec_singleI.
revert drs. list_assoc_r. intro drs. exact drs. Qed.
*)

Lemma can_trf_sctrL_ck4_WBox_ak4 V fml ps c: 
  rel_adm K4rules (seqrel (sctr_relL fml)) -> cgerule (@K4prrule V) ps c ->
  can_trf_rules_rc (seqrel (sctr_relL (WBox fml))) (adm (@K4rules V)) ps c.
  
Proof. intros ra k4.  unfold can_trf_rules_rc. intros c' scr.
inversion scr. clear scr. destruct X. 
unfold seqext in H.  unfold seqext in H0.  simpl in H. simpl in H0.
destruct k4.  inversion k. clear k. injection H as . subst. 

apply gen_ext_splitR in g. cD.
revert g4. list_assoc_l. intro g4.
apply gen_ext_splitR in g4. cD.
apply gen_ext_splitR in g7. cD.  subst.
inversion g11 ; inversion g12 ; inversion X0 ; subst ; clear g11 g12 X0.

- (* neither occurrence of contraction formula is weakened in,
  premise needs to be contracted (both boxed and unboxed formula) *)
eexists. split. all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq.  apply rT_step.
eapply (Sctxt_relI_eq _ _ _ _ _ g (g5 ++ Gam) [] [phi]).
apply (sctr_relLI _ l). simpl. rewrite g2. list_eq_assoc.  reflexivity.

simpl.  repeat map_eq. subst.
repeat (match goal with | [ H : WBox _ = WBox _ |- _ ] => injection H as end).  
subst.  destruct ra.  erequire r.  erequire r.  require r. 
eapply (Sctxt_relI _ _ _ 
  (map (WBox (V:=V)) g2 ++ WBox g15 :: map (WBox (V:=V)) g22 ++
        map (WBox (V:=V)) g10 ++ g2) g10 [] [phi]).
apply (sctr_relLI g15 g22).
destruct r.  apply admI.
intro drs. apply dersrec_singleD in drs.
unfold seqext in d. simpl in d. simpl in drs.
eapply arg_cong_imp' in drs.
apply d in drs.  2: list_eq_assoc. clear d.

eapply derI. apply K4_I.  eapply CGctxt. 
apply (K4prrule_I (g2 ++ g15 :: g22 ++ g10)).
2: apply g0.
rewrite map_app. simpl.  rewrite map_app.
repeat (assumption || apply gen_ext_app || apply gen_ext_cons).
apply dersrec_singleI.
rewrite map_app. simpl.  rewrite map_app.
eapply arg_cong_imp'. exact drs. list_eq_assoc.

- (* the boxed formula to be contracted is weakened in *)
eexists. split. all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq.  apply rT_refl.
rewrite app_nil_r in g2.
apply map_app_ex in g2. cD.
apply map_app_ex in g6. cD.
destruct g6. simpl in g9. discriminate g9.
simpl in g9.  injection g9 as .
subst.  unfold seqext. rewrite app_nil_l.
apply admI. intro drs. eapply derI. 2: exact drs.
apply K4_I.  eapply CGctxt.  apply K4prrule_I.
rewrite !map_app. simpl. 
repeat (assumption || apply gen_ext_app || apply gen_ext_cons).
assumption.

- (* one boxed formula is weakened in, but not the one to be contracted,
  so will need to use exchange *)
eexists. split. all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq.  apply rT_refl.
apply map_app_ex in g2. cD.
apply map_app_ex in g6. cD.
apply map_app_ex in g10. cD.
destruct g15. simpl in g16. discriminate g16.
simpl in g16. injection g16 as .
destruct g15. simpl in H0.
2: simpl in H0. 2: discriminate H0.
subst.  unfold seqext. rewrite app_nil_l.
apply admI. intro drs.

eapply (@derI' _ _ _ _ _) in drs. (* why doesn't just derI' work? *)
all: cycle 1.
apply K4_I.  eapply CGctxt.  apply K4prrule_I.
2: eassumption.
rewrite !map_app.
repeat (eassumption || apply gen_ext_app || apply gen_ext_cons).
apply gen_ext_nil.
(* now use exchange *)
apply (exchL_K4 drs).  apply fst_relI.  swap_tac_Rc.

- (* neither of the boxed contraction formulae is in Box Gam *)
eexists. split. all: cycle 1.
apply ForallT_singleI. eexists. split. apply InT_eq.  apply rT_refl.
unfold seqext. rewrite app_nil_l.
apply admI. intro drs.
eapply (@derI' _ _ _ _ _) in drs.
all: cycle 1.
apply K4_I.  eapply CGctxt.  apply K4prrule_I.
rewrite app_nil_r in g2.
rewrite g2.
2: exact g0.
2: exact drs.
repeat (assumption || apply gen_ext_app || apply gen_ext_cons).
apply gen_ext_extra. assumption. Qed.

Check can_trf_sctrL_ck4_WBox_ak4.

Lemma can_trf_sctrL_WBox_ak4 V fml:
  rel_adm K4rules (seqrel (sctr_relL fml)) ->
  forall ps c, K4rules ps c ->
    can_trf_rules_rc (seqrel (sctr_relL (WBox fml))) (adm (@K4rules V)) ps c.
Proof. intros ra ps c k4. destruct k4.
apply can_trf_sctrL_ck4_WBox_ak4 ; assumption.
apply (can_trf_rules_rc_mono' (rsub_adm _)).
apply can_trf_sctrL_spr_WBox_k4. assumption. Qed.
Check can_trf_sctrL_WBox_ak4.

Lemma can_trf_sctrL_WBox_ak4sw V fml:
  rel_adm K4rules_sw (seqrel (sctr_relL fml)) ->
  forall ps c, K4rules_sw ps c ->
    can_trf_rules_rc (seqrel (sctr_relL (WBox fml))) (adm (@K4rules_sw V)) ps c.
Proof. intros ra ps c k4. destruct k4.
apply can_trf_sctrL_k4_WBox_ak4sw ; assumption.
apply (can_trf_rules_rc_mono' (rsub_adm _)).
apply can_trf_sctrL_spr_WBox_k4sw. assumption.
apply can_trf_sctrL_wk_any_ak4sw. assumption. Qed.
Check can_trf_sctrL_WBox_ak4sw.

Definition K4_sctrL_WBox V fml ra := 
  der_trf_rc_adm (@can_trf_sctrL_WBox_ak4 V fml ra).
Definition K4sw_sctrL_WBox V fml ra := 
  der_trf_rc_adm (@can_trf_sctrL_WBox_ak4sw V fml ra).
Check K4_sctrL_WBox.  Check K4sw_sctrL_WBox.

Lemma K4_sctrL_WBox_rel_adm V fml :
  rel_adm (@K4rules V) (seqrel (sctr_relL fml)) ->
  rel_adm (@K4rules V) (seqrel (sctr_relL (WBox fml))).
Proof. intro raf. apply rel_admI. intros. apply radmI. intro.
eapply K4_sctrL_WBox ; eassumption. Qed.

Lemma K4sw_sctrL_WBox_rel_adm V fml :
  rel_adm (@K4rules_sw V) (seqrel (sctr_relL fml)) ->
  rel_adm (@K4rules_sw V) (seqrel (sctr_relL (WBox fml))).
Proof. intro raf. apply rel_admI. intros. apply radmI. intro.
eapply K4sw_sctrL_WBox ; eassumption. Qed.

Theorem K4_sctr_rel_adm V fml :
  rel_adm (@K4rules V) (seqrel (sctr_relL fml)) *
  rel_adm (@K4rules V) (seqrel (sctr_relR fml)).
Proof. induction fml ; cD ; split.
apply K4_sctrL_pp_rel_adm.
apply K4_sctrR_pp_rel_adm.
apply K4_sctrL_Bot_rel_adm.
apply K4_sctrR_Bot_rel_adm.
apply K4_sctrL_Imp ; assumption.
apply K4_sctrR_Imp ; assumption.
apply K4_sctrL_WBox_rel_adm ; assumption.
apply K4_sctrR_WBox_rel_adm.
apply K4_sctrL_BBox_rel_adm.
apply K4_sctrR_BBox_rel_adm.
Qed.

Theorem K4sw_sctr_rel_adm V fml :
  rel_adm (@K4rules_sw V) (seqrel (sctr_relL fml)) *
  rel_adm (@K4rules_sw V) (seqrel (sctr_relR fml)).
Proof. induction fml ; cD ; split.
apply K4sw_sctrL_pp_rel_adm.
apply K4sw_sctrR_pp_rel_adm.
apply K4sw_sctrL_Bot_rel_adm.
apply K4sw_sctrR_Bot_rel_adm.
apply K4sw_sctrL_Imp ; assumption.
apply K4sw_sctrR_Imp ; assumption.
apply K4sw_sctrL_WBox_rel_adm ; assumption.
apply K4sw_sctrR_WBox_rel_adm.
apply K4sw_sctrL_BBox_rel_adm.
apply K4sw_sctrR_BBox_rel_adm.
Qed.

Definition K4_sctr_rel_admL V fml := fst (@K4_sctr_rel_adm V fml).
Definition K4_sctr_rel_admR V fml := snd (@K4_sctr_rel_adm V fml).
Definition K4sw_sctr_rel_admL V fml := fst (@K4sw_sctr_rel_adm V fml).
Definition K4sw_sctr_rel_admR V fml := snd (@K4sw_sctr_rel_adm V fml).

(* this is contraction of singletons, now want contraction of lists *)
Inductive lctr_relL V (fmls : list V) : relationT (Seql V) :=
  | lctr_relLI S : lctr_relL fmls (fmls ++ S ++ fmls, []) (fmls ++ S, []). 
Inductive lctr_relR V (fmls : list V) : relationT (Seql V) :=
  | lctr_relRI S : lctr_relR fmls ([], fmls ++ S ++ fmls) ([], fmls ++ S). 

Theorem gen_lctr_rel_admL V rules 
  (sctr_rel_admL : forall fml, rel_adm rules (seqrel (sctr_relL fml))) fmls :
  rel_adm rules (seqrel (lctr_relL (fmls : list (PropF V)))).
Proof. apply rel_admI. induction fmls.
- intros *. intro slr. apply radmI. destruct slr. destruct l.
rewrite app_nil_r. tauto.
- intros *. intro slr. apply radmI. destruct slr. destruct l.
intro daf.  erequire IHfmls.  erequire IHfmls.  require IHfmls.
all:cycle 1.
(* first, contract a *)
pose (sctr_rel_admL a).  inversion r.
erequire X.  erequire X.  require X.
all: cycle 1. destruct X. specialize (d daf).
all: cycle 2. unfold seqext.
eapply (Sctxt_relI_eq _ (a :: (fmls ++ S) ++ [a]) [] (a :: fmls ++ S) []
  Φ1 (fmls ++ Φ2) Ψ1 Ψ2).
apply sctr_relLI. list_assoc_r. simpl. reflexivity. reflexivity.
(* now use inductive result, contracting fmls *)
clear r. destruct IHfmls. apply d0. apply d.
eapply (Sctxt_relI_eq _ (fmls ++ S ++ fmls) [] (fmls ++ S) []
  (Φ1  ++ [a]) Φ2 Ψ1 Ψ2).
apply lctr_relLI. 
list_assoc_r. simpl. reflexivity.
unfold seqext.  list_assoc_r. simpl. reflexivity. Qed.

Theorem gen_lctr_rel_admR V rules
  (sctr_rel_admR : forall fml, rel_adm rules (seqrel (sctr_relR fml))) fmls :
  rel_adm rules (seqrel (lctr_relR (fmls : list (PropF V)))).
Proof. apply rel_admI. induction fmls.
- intros *. intro slr. apply radmI. destruct slr. destruct l.
rewrite app_nil_r. tauto.
- intros *. intro slr. apply radmI. destruct slr. destruct l.
intro daf.  erequire IHfmls.  erequire IHfmls.  require IHfmls.
all:cycle 1.
(* first, contract a *)
pose (@sctr_rel_admR a).  inversion r.
erequire X.  erequire X.  require X.
all: cycle 1. destruct X. specialize (d daf).
all: cycle 2. unfold seqext.
eapply (Sctxt_relI_eq _ [] (a :: (fmls ++ S) ++ [a]) [] (a :: fmls ++ S)
  Φ1 Φ2 Ψ1 (fmls ++ Ψ2)).
apply sctr_relRI. list_assoc_r. simpl. reflexivity. reflexivity.
(* now use inductive result, contracting fmls *)
clear r. destruct IHfmls. apply d0. apply d.
eapply (Sctxt_relI_eq _ [] (fmls ++ S ++ fmls) [] (fmls ++ S) 
  Φ1 Φ2 (Ψ1 ++ [a]) Ψ2).
apply lctr_relRI. 
list_assoc_r. simpl. reflexivity.
unfold seqext.  list_assoc_r. simpl. reflexivity. Qed.

Definition K4_lctr_rel_admL V := gen_lctr_rel_admL (@K4_sctr_rel_admL V).
Definition K4_lctr_rel_admR V := gen_lctr_rel_admR (@K4_sctr_rel_admR V).
Definition K4sw_lctr_rel_admL V := gen_lctr_rel_admL (@K4sw_sctr_rel_admL V).
Definition K4sw_lctr_rel_admR V := gen_lctr_rel_admR (@K4sw_sctr_rel_admR V).

