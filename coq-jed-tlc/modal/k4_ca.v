
(* K4 modal logic, using lists of formulae *)
(* cut admissibility *)

Require Export List.
Export ListNotations.
Set Implicit Arguments.

Test Universe Polymorphism. (* NB Set this causes errors *)
Test Printing Universes.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT dd_fc.
Require Import List_lemmasT.
Require Import gen_tacs gen_seq.
Require Import swappedT.
Require Import gstep.
Require Import gentree.
Require Import gen_ext.
Require Import rtcT.
Require Import k4.
Require Import k4_exch.
Require Import k4_inv.
Require Import k4_ctr.

(* derivability of conclusion of a cut, not conditional on premises
  being derivable *) 
(* need to allow cut-formula being within the list of formulae (not just
  at the front) because a rule may add formula in front in its premises *)
(* note - in this previous version cut_el_der' doesn't tell you which
  instances of A can be used as the cut-formula *)

(* but note we are going to need to allow A to be anywhere, not just at the
front, because rule my cause that to happen in the premises *)

(* note that a pair of end-sequents not of the form
  (_, _ ++ A :: _) (_ ++ A :: _, _) satisfies cut_adm *)
(* all possible results of cut on A derivable 
  (only an issue because lists distinguish different occurrences of A) *)
Inductive cedc X rules (A : X) cl cr : Type :=  
  | cedcI : (forall la ls ls' ra ra' rs, 
    cl = (la, ls ++ A :: ls') -> cr = (ra ++ A :: ra', rs) ->
      derrec rules emptyT (la ++ ra ++ ra', ls ++ ls' ++ rs)) ->
      @cedc X rules A cl cr.

Inductive cut_adm X rules (A : X) : Type :=  
  | cadmI : (forall cl cr la ls ls' ra ra' rs, 
    cl = (la, ls ++ A :: ls') -> cr = (ra ++ A :: ra', rs) ->
    derrec rules emptyT cl -> derrec rules emptyT cr ->
      derrec rules emptyT (la ++ ra ++ ra', ls ++ ls' ++ rs)) ->
      @cut_adm X rules A.

Definition cedcD X rules A cl cr (c : @cedc X rules A cl cr) := 
  match c with | cedcI _ d => d end.

Definition cadmD X rules A (c : @cut_adm X rules A) :=
  match c with | cadmI _ d => d end.

Inductive cedc_fc W rules (A : W) (dtl dtr : derrec_fc rules emptyT)  : Type :=
  | cedc_fcI : (forall la ls ls' ra ra' rs, 
      derrec_fc_concl dtl = (la, ls ++ A :: ls') ->
      derrec_fc_concl dtr = (ra ++ A :: ra', rs) ->
      derrec rules emptyT (la ++ ra ++ ra', ls ++ ls' ++ rs)) ->
      @cedc_fc W rules A dtl dtr.

Lemma cedc_fc_iff W rules A dtl dtr : iffT (@cedc_fc W rules A dtl dtr)  
    (@cedc W rules A (derrec_fc_concl dtl) (derrec_fc_concl dtr)).
Proof. apply pair.
intro cfc. destruct cfc.  eapply cedcI. exact d.
intro ce. inversion ce.  eapply cedc_fcI. exact X. Qed.

Lemma k4_cut_adm_Bot V : cut_adm K4rules (Bot V).
Proof. apply cadmI. intros *. intros cle cre dl dr.  subst. 
(* use result that deletion of Bot on right is admissible *)
clear dr. eapply K4_delBotR in dl.
all: cycle 1.  
eapply (Sctxt_relI_eq _ _ _ _ _ [] _ _ _). apply del_relRI.
reflexivity.  reflexivity. simpl in dl.
pose weakening.  unfold can_wk in c.  apply c in dl. clear c.
unfold wk_valid in dl.  pose (dl [] (ra ++ ra') [] rs).
unfold seqext in d. simpl in d. rewrite <- app_assoc in d. exact d. Qed.

Lemma k4sw_cut_adm_Bot V : cut_adm K4rules_sw  (Bot V).
Proof. apply cadmI. intros *. intros cle cre dl dr.  subst. 
(* use result that deletion of Bot on right is admissible *)
clear dr. eapply K4_sw_delBotR in dl.
all: cycle 1.  
eapply (Sctxt_relI_eq _ _ _ _ _ [] _ _ _). apply del_relRI.
reflexivity.  reflexivity. simpl in dl.
(* use weakening rule for k4_sw *)
eapply derI. all: cycle 1.
apply (dersrec_singleI dl).
apply K4_wk_I.  eapply CGctxt. apply trivrule_I.
apply gen_ext_appR'.  solve_gen_ext. Qed.

Lemma gen_cut_adm_Imp V (rules : rlsT (Seqlf V)) C D  
  (adm_exchL : forall (ant ant' suc : list (PropF V)),
    swapped ant' ant -> adm rules [(ant', suc)] (ant, suc))
  (adm_exchR : forall (ant suc suc' : list (PropF V)),
    swapped suc' suc -> adm rules [(ant, suc')] (ant, suc))
  (impLinv1 : rel_adm rules (seqrel ImpLinv1))
  (impLinv2 : rel_adm rules (seqrel ImpLinv2))
  (impRinv : rel_adm rules (seqrel ImpRinv))
  (lctr_rel_admL : forall fmls, rel_adm rules (seqrel (lctr_relL fmls)))
  (lctr_rel_admR : forall fmls, rel_adm rules (seqrel (lctr_relR fmls))):
  cut_adm rules C -> cut_adm rules D -> cut_adm rules (Imp C D : PropF V).
Proof. intros cac cad. apply cadmI. intros *.
intros cle cre dl dr. subst.  
(* apply inversion to dl and dr *)
eapply impRinv in dl. all: cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ [] _ _ _). apply ImpRinv_I.
reflexivity. reflexivity.
pose dr as dr1.  eapply impLinv1 in dr1. all: cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ _ _ [] _). apply ImpLinv1_I.
reflexivity. reflexivity.
pose dr as dr2.  eapply impLinv2 in dr2. all: cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ _ _ [] _). apply ImpLinv2_I.
reflexivity. reflexivity.
(* now use cut-admissibility for D *)
destruct cad.
erequire d.  erequire d.  erequire d.  erequire d.
erequire d.  erequire d.  erequire d.  erequire d.
require d. all: cycle 1.  require d. all: cycle 1.
require d. exact dl.  require d. exact dr1.
all: cycle 1. reflexivity.  reflexivity.
simpl in d. 
(* now use cut-admissibility for C *)
destruct cac.
specialize (d0 (ra ++ [] ++ ra', [] ++ [C] ++ rs)
  ((C :: la) ++ ra ++ ra', ls ++ ls' ++ rs)).
erequire d0.  specialize (d0 []).  erequire d0.  specialize (d0 []).
erequire d0.  erequire d0.  
require d0. all: cycle 1.  require d0. all: cycle 1.
require d0. exact dr2.  require d0. exact d.
all: cycle 1. reflexivity.  simpl. reflexivity.
simpl in d0.
(* now need contraction admissibility *)
clear dr dl dr1 dr2 d.
pose (lctr_rel_admL (ra ++ ra')).  inversion_clear r.
erequire X.  erequire X.  require X. all: cycle 1.
destruct X. specialize (d d0). all: cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ [] [] [] _).  apply (lctr_relLI _ la).
rewrite app_nil_r. simpl. reflexivity. reflexivity.
(* now contraction on the right *)
clear d0. simpl in d.
pose (lctr_rel_admR rs).  inversion_clear r.
erequire X.  erequire X.  require X. all: cycle 1.
destruct X. specialize (d0 d). all: cycle 1.
eapply (Sctxt_relI_eq _ _ _ _ _ [] _ [] []).  apply (lctr_relRI _ (ls ++ ls')).
rewrite !app_nil_r. simpl. list_assoc_r'. reflexivity. reflexivity.
simpl in d0. rewrite app_nil_r in d0. clear d.
(* now need to do exchange *)
erequire adm_exchL.  erequire adm_exchL.  erequire adm_exchL.
require adm_exchL.  all: cycle 1.  eapply adm_exchL.  apply dersrec_singleI.
erequire adm_exchR.  erequire adm_exchR.  erequire adm_exchR.
require adm_exchR.  all: cycle 1.  eapply adm_exchR.  apply dersrec_singleI.
exact d0.  swap_tac. swap_tac. Qed.

Definition k4sw_cut_adm_Imp V C D := @gen_cut_adm_Imp V K4rules_sw C D 
  (@admK4swexchL V) (@admK4swexchR V)
  (@ra_K4sw_ImpLinv1 V) (@ra_K4sw_ImpLinv2 V) (@ra_K4sw_ImpRinv V)
  (@K4sw_lctr_rel_admL V) (@K4sw_lctr_rel_admR V).

Definition k4_cut_adm_Imp V C D := @gen_cut_adm_Imp V K4rules C D 
  (@admK4exchL V) (@admK4exchR V) (@ra_K4_ImpLinv1 V) (@ra_K4_ImpLinv2 V)
  (@ra_K4_ImpRinv V) (@K4_lctr_rel_admL V) (@K4_lctr_rel_admR V) .

Check k4_cut_adm_Imp.  Check k4sw_cut_adm_Imp.

Ltac dfatac lps lps0 cin0 cin1 := 
apply dersrec_forall ;  intros c cin ;
(* now use inductive cut-admissibility *)
apply InT_mapE in cin ; cD ;
eapply ForallTD_forall in lps ;
only 2: apply (InT_map _ cin1) ; cD ;
inversion lps0 as [ci] ;
destruct cin ; unfold seqext in cin0 ;
injection cin0 as ; subst ; 
unfold seqext in ci ;
do 6 erequire ci.

(* now something similar to can_trf_sctrL_spr_ido but for gstep2 *)

(* general version *) 
Lemma gs2_spr_idoR (V : Set) (A : PropF V) rules any psa psb ca cb
  (adm_exchL : forall (ant ant' suc : list (PropF V)),
    swapped ant' ant -> adm rules [(ant', suc)] (ant, suc)) 
  (gwk : forall ca cs, can_gwk rules ca cs) :
  rsub (seqrule (@princrule V)) rules ->
  idonlyR (@princrule V) A -> seqrule (@princrule V) psa ca -> 
  gen_step2 (cedc rules) A any (derrec rules emptyT)
	(derrec rules emptyT) psa ca psb cb.
Proof. intros rs ido sqr.
unfold gen_step2. intros sub lps rps.
(* not using induction on cut formula or on derivation on the right *)
clear rps sub. intros dl dr. eapply cedcI. 
intros *. intros cae cbe. 
destruct sqr. destruct c as [cl cr]. unfold seqext in cae.
injection cae as . subst.  destruct ido.

repeat (acacDe'T2 ; subst ; repeat (list_eq_ncT ; sD ; subst)) ;
simpl ; rewrite ?app_nil_r ;
simpl in p ; rewrite ?app_nil_r in p ; (* 6 subgoals *)
repeat (apply princrule_appR in p ; sD ; subst) ; (* 7 sgs *)
try (list_eq_ncT ; sD ; subst) ; (* does more than just discriminate *)
idtac.

- clear dl. eapply derI. apply (rsubD rs).
eapply Sctxt_eq ; [ exact p | list_assoc_r' ; reflexivity |
simpl ; reflexivity | reflexivity ].
dfatac lps lps0 cin0 cin1.
require ci. list_assoc_l'. reflexivity. 
require ci. reflexivity.
revert ci.  list_assoc_r. simpl. intro d. exact d.

(* rule on left is id rule,
  conclusion is rh sequent, weakened and exchanged *)
- try (apply p0 in p ; cD ; subst ; simpl ; rewrite ?app_nil_r).
clear p0 lps dl.  
specialize (adm_exchL (A :: ra ++ ra')).
erequire adm_exchL. erequire adm_exchL. require adm_exchL.
2: pose (admDs adm_exchL dr).  swap_tac_Rc.
unfold can_gwk in gwk.  unfold gwk_valid in gwk.  eapply gwk.  exact d.
list_assoc_r.  solve_gen_ext.  solve_gen_ext.

- clear dl. eapply derI. apply (rsubD rs).
eapply Sctxt_eq ; [ exact p | list_assoc_r' ; reflexivity |
assoc_mid cr ; reflexivity | reflexivity ].
dfatac lps lps0 cin0 cin1.
require ci. list_assoc_r'. reflexivity. 
require ci. reflexivity.
revert ci.  list_assoc_r. intro d. exact d.

- clear dl. eapply derI. apply (rsubD rs).
eapply Sctxt_eq ; [ exact p | list_assoc_r' ; reflexivity |
assoc_mid H0 ; reflexivity | reflexivity ].
dfatac lps lps0 cin0 cin1.
require ci. list_assoc_l'. reflexivity. 
require ci. reflexivity.
revert ci.  list_assoc_r. intro d. exact d.

(* following same as above *)
- try (apply p0 in p ; cD ; subst ; simpl ; rewrite ?app_nil_r).
clear p0 lps dl.  
specialize (adm_exchL (A :: ra ++ ra')).
erequire adm_exchL. erequire adm_exchL. require adm_exchL.
2: pose (admDs adm_exchL dr).  swap_tac_Rc.
unfold can_gwk in gwk.  unfold gwk_valid in gwk.  eapply gwk.  exact d.
list_assoc_r.  solve_gen_ext.  solve_gen_ext.

(* start proof for last of 6 cases *)
- clear dl. eapply derI. apply (rsubD rs).
eapply Sctxt_eq ; [ exact p | list_assoc_r' ; reflexivity |
assoc_mid cr ; reflexivity | reflexivity ].
dfatac lps lps0 cin0 cin1.
require ci. list_assoc_l'. reflexivity.
require ci. reflexivity.
revert ci.  list_assoc_r. intro d. exact d.
Qed.

Lemma k4sw_weakening V ca cs: can_gwk (@K4rules_sw V) ca cs.
Proof. unfold can_gwk.  unfold gwk_valid.  intros d cea ces geca gecs.
eapply derI. apply K4_wk_I.
apply (CGctxt _ _ (trivrule_I _) geca gecs).
exact (dersrec_singleI d). Qed.  

Definition k4_gs2_spr_idoR V A any psa psb ca cb :=
  @gs2_spr_idoR V A _ any psa psb ca cb 
    (@admK4exchL V) (@gen_weakening V) (@rscpl V).

Definition k4sw_gs2_spr_idoR V A any psa psb ca cb :=
  @gs2_spr_idoR V A _ any psa psb ca cb 
    (@admK4swexchL V) (@k4sw_weakening V) (@rscplsw V).

Check gs2_spr_idoR.  Check k4_gs2_spr_idoR.  Check k4sw_gs2_spr_idoR.

Lemma gs2_spr_idoL (V : Set) (A : PropF V) rules any psa psb ca cb
  (adm_exchR : forall (ant suc suc' : list (PropF V)),
    swapped suc' suc -> adm rules [(ant, suc')] (ant, suc))
  (gwk : forall ca cs, can_gwk rules ca cs) :
  rsub (seqrule princrule) rules ->
  idonlyL princrule A -> 
  seqrule princrule psb cb -> 
  gen_step2 (cedc rules) A any (derrec rules emptyT)
	(derrec rules emptyT) psa ca psb cb.
Proof. intros rs ido sqr.
unfold gen_step2. intros sub lps rps.
(* not using induction on cut formula or on derivation on the left *)
clear lps sub. intros dl dr. eapply cedcI. 
intros *. intros cae cbe. 
destruct sqr. destruct c as [cl cr]. unfold seqext in cbe.
injection cbe as . subst.  destruct ido.

repeat (acacDe'T2 ; subst ; repeat (list_eq_ncT ; sD ; subst)) ;
simpl ; rewrite ?app_nil_r ;
simpl in p ; rewrite ?app_nil_r in p ; (* 6 subgoals *)
repeat (apply princrule_appL in p ; sD ; subst) ; (* 7 sgs *)
try (list_eq_ncT ; sD ; subst) ; (* does more than just discriminate *)
idtac.

- clear dr. eapply derI. apply (rsubD rs).
eapply Sctxt_eq ; [ exact p | simpl ; list_assoc_l' ; reflexivity |
assoc_mid cr ; reflexivity | reflexivity ].
dfatac rps rps0 cin0 cin1.
require ci. reflexivity.
require ci. list_assoc_l'. reflexivity.
revert ci.  list_assoc_r. intro d. exact d.

- try (apply p0 in p ; cD ; subst ; simpl ; rewrite ?app_nil_r).
clear p0 rps dr.  
erequire adm_exchR.  specialize (adm_exchR (ls ++ ls' ++ [A])).
erequire adm_exchR.  require adm_exchR.
2: pose (admDs adm_exchR dl).  swap_tac_Rc.
unfold can_gwk in gwk.  unfold gwk_valid in gwk.  eapply gwk.  exact d.
solve_gen_ext.  solve_gen_ext.

- clear dr. eapply derI. apply (rsubD rs).
eapply Sctxt_eq ; [ exact p | assoc_mid cl ; reflexivity |
assoc_mid cr ; reflexivity | reflexivity ].
dfatac rps rps0 cin0 cin1.
require ci. reflexivity.
require ci. list_assoc_r'. reflexivity.
revert ci.  list_assoc_r. intro d. exact d.

- clear dr. eapply derI. apply (rsubD rs).
eapply Sctxt_eq ; [ exact p | assoc_mid H ; reflexivity |
assoc_mid cr ; reflexivity | reflexivity ].
dfatac rps rps0 cin0 cin1.
require ci. reflexivity.
require ci. list_assoc_l'. reflexivity.
revert ci.  list_assoc_r. intro d. exact d.

- try (apply p0 in p ; cD ; subst ; simpl ; rewrite ?app_nil_r).
clear p0 rps dr.  
erequire adm_exchR.  specialize (adm_exchR (ls ++ ls' ++ [A])).
erequire adm_exchR.  require adm_exchR.
2: pose (admDs adm_exchR dl).  swap_tac_Rc.
unfold can_gwk in gwk.  unfold gwk_valid in gwk.  eapply gwk.  exact d.
solve_gen_ext.  solve_gen_ext.

- clear dr. eapply derI. apply (rsubD rs).
eapply Sctxt_eq ; [ exact p | assoc_mid cl ; reflexivity |
assoc_mid cr ; reflexivity | reflexivity ].
dfatac rps rps0 cin0 cin1.
require ci. reflexivity.
require ci. list_assoc_l'. reflexivity.
revert ci.  list_assoc_r. intro d. exact d.
Qed.

Definition k4_gs2_spr_idoL V A any psa psb ca cb :=
  @gs2_spr_idoL V A _ any psa psb ca cb 
    (@admK4exchR V) (@gen_weakening V) (@rscpl V).
Definition k4sw_gs2_spr_idoL V A any psa psb ca cb :=
  @gs2_spr_idoL V A _ any psa psb ca cb 
    (@admK4swexchR V) (@k4sw_weakening V) (@rscplsw V).

Check gs2_spr_idoL.  Check k4_gs2_spr_idoL.  Check k4sw_gs2_spr_idoL.

Check gen_step2_lemT.

(* need to prove
(forall (A0 : fty) (psa : list stya) (psb : list styb) 
          (ca : stya) (cb : styb),
        rlsa psa ca ->
        rlsb psb cb ->
        gen_step2 P A0 sub (derrec rlsa (emptyT (X:=stya)))
          (derrec rlsb (emptyT (X:=styb))) psa ca psb cb)
*)

Inductive isubfml {V} : PropF V -> PropF V -> Type := 
  | isub_ImpL : forall C D, isubfml C (Imp C D)
  | isub_ImpR : forall C D, isubfml D (Imp C D)
  | isub_Box : forall A, isubfml A (WBox A).

(* need to prove this from cut_adm_Imp *)
Lemma gs2_Imp (V : Set) (C D : PropF V) rules psa psb ca cb
  (cut_adm_Imp : 
       cut_adm rules C -> cut_adm rules D -> cut_adm rules (Imp C D)) :
  rules psa ca -> rules psb cb -> 
  gen_step2 (cedc rules) (Imp C D) (@isubfml V) (derrec rules emptyT)
	(derrec rules emptyT) psa ca psb cb.
Proof. intros rlsa rlsb.
unfold gen_step2.  intros isub fpl fpr dl dr.
apply cedcI. intros *. intros cae cbe. 
require cut_adm_Imp. { apply cadmI. intros *. intros cle cre dcl dcr.
pose (isub C (isub_ImpL C D) cl dcl cr dcr).
destruct c. apply d. exact cle. exact cre. }
require cut_adm_Imp. { apply cadmI. intros *. intros cle cre dcl dcr.
pose (isub D (isub_ImpR C D) cl dcl cr dcr).
destruct c. apply d. exact cle. exact cre. }
{ destruct cut_adm_Imp. eapply d. reflexivity. reflexivity. 
subst. exact dl.  subst. exact dr. } Qed.

Lemma gs2_Bot (V : Set) rules any psa psb ca cb
  (cut_adm_Bot : cut_adm rules (@Bot V)) :
  rules psa ca -> rules psb cb -> 
  gen_step2 (cedc rules) (@Bot V) any (derrec rules emptyT)
	(derrec rules emptyT) psa ca psb cb.
Proof. intros rlsa rlsb.
unfold gen_step2.  intros isub fpl fpr dl dr.
apply cedcI. intros *. intros cae cbe. clear isub fpl fpr.
destruct cut_adm_Bot.  eapply d ; eassumption. Qed.

Check gs2_Imp.  Check gs2_Bot. 
Definition k4_gs2_Bot {V} any psa psb ca cb :=
  @gs2_Bot V _ any psa psb ca cb (@k4_cut_adm_Bot _).
Definition k4_gs2_Imp {V} C D psa psb ca cb :=
  @gs2_Imp V C D _ psa psb ca cb (@k4_cut_adm_Imp _ _ _).
Definition k4sw_gs2_Bot {V} any psa psb ca cb :=
  @gs2_Bot V _ any psa psb ca cb (@k4sw_cut_adm_Bot _).
Definition k4sw_gs2_Imp {V} C D psa psb ca cb :=
  @gs2_Imp V C D _ psa psb ca cb (@k4sw_cut_adm_Imp _ _ _).

Lemma WBox_InT V A Gam: InT (WBox A) (map (WBox (V:=V)) Gam) -> InT A Gam.
Proof. intro inw.  induction Gam.
simpl in inw.  eapply InT_nilE in inw. exact inw.
inversion inw ; subst. injection H0 as . subst. apply InT_eq.
apply InT_cons. apply (IHGam H0). Qed.

Lemma gs2_wkR (W : Set) (A : W) rules any psa psb ca cb :
  rsub (cgerule (@trivrule _)) rules ->
  cgerule (@trivrule _) psb cb -> 
  gen_step2 (cedc rules) A any (derrec rules emptyT)
	(derrec rules emptyT) psa ca psb cb.
Proof. intros rs ct.
unfold gen_step2.  intros isub fpl fpr dl dr. clear isub fpl.
apply cedcI. intros *. intros cle cre. 
destruct ct.  inversion t. clear t.  injection cre as . subst.
apply ForallT_singleD in fpr. cD.
apply gen_ext_splitR in g. cD.
inversion g4 ; subst.
- (* case where A is not weakened in *)
inversion fpr0. do 6 erequire X0.
require X0. reflexivity.  require X0. reflexivity.
eapply derI'.  apply (dersrec_singleI X0).
apply (rsubD rs).  apply (CGctxt _ _ (trivrule_I _)).
repeat (assumption || apply gen_ext_refl || apply gen_ext_app).
repeat (assumption || apply gen_ext_refl || apply gen_ext_app).
- (* case where A is weakened in *)
eapply derI'.  apply (dersrec_singleI fpr).
apply (rsubD rs).  apply (CGctxt _ _ (trivrule_I _)).
apply gen_ext_appL.
repeat (assumption || apply gen_ext_refl || apply gen_ext_app).
apply gen_ext_appL.  apply gen_ext_appL. assumption.
Qed.

Lemma gs2_wkL (W : Set) (A : W) rules any psa psb ca cb :
  rsub (cgerule (@trivrule _)) rules ->
  cgerule (@trivrule _) psa ca -> 
  gen_step2 (cedc rules) A any (derrec rules emptyT)
	(derrec rules emptyT) psa ca psb cb.
Proof. intros rs ct.
unfold gen_step2.  intros isub fpl fpr dl dr. clear isub fpr.
apply cedcI. intros *. intros cle cre. 
destruct ct.  inversion t. clear t.  injection cle as . subst.
apply ForallT_singleD in fpl. cD.
apply gen_ext_splitR in g0. cD.
inversion g4 ; subst.
- (* case where A is not weakened in *)
inversion fpl0. do 6 erequire X0.
require X0. reflexivity.  require X0. reflexivity.
eapply derI'.  apply (dersrec_singleI X0).
apply (rsubD rs).  apply (CGctxt _ _ (trivrule_I _)).
repeat (assumption || apply gen_ext_refl || apply gen_ext_app).
repeat (assumption || apply gen_ext_refl || apply gen_ext_app).
- (* case where A is weakened in *)
eapply derI'.  apply (dersrec_singleI fpl).
apply (rsubD rs).  apply (CGctxt _ _ (trivrule_I _)).
apply gen_ext_appR. assumption.
repeat (assumption || apply gen_ext_refl || apply gen_ext_app).
apply gen_ext_appR. assumption.
Qed.

Check gs2_wkL.  Check gs2_wkR.

(* fails here if radm, rel_adm Polymorphic - why? *)
Lemma gs2_k4_Box_Box (V : Set) (fml : PropF V) rules psl psr cl cr
  (adm_exchL : forall (ant ant' suc : list (PropF V)),
    swapped ant' ant -> adm rules [(ant', suc)] (ant, suc))
  (lctr_rel_admL : forall fmls, rel_adm rules (seqrel (lctr_relL fmls))) :
  rsub K4prrule  rules -> 
  @K4prrule V psl cl -> @K4prrule V psr cr -> 
  gen_step2 (cedc rules) fml isubfml (derrec rules emptyT)
	(derrec rules emptyT) psl cl psr cr.
Proof. intros rs k4l k4r isub fpl fpr dl dr.
destruct k4l as [X A].  destruct k4r as [Z B]. 
apply ForallT_singleD in fpl.  apply ForallT_singleD in fpr. cD.
clear fpl0. clear fpr.
apply cedcI. intros *. intros cle cre.
injection cle as .  injection cre as . subst.
repeat map_eq. subst. 
list_eq_ncT. sD.  2: discriminate H2.  injection H2 as . subst. simpl.
inversion fpr0. clear fpr0. erequire X0.
specialize (X0 [] []).  do 3 erequire X0.
require X0. reflexivity.  require X0.
rewrite map_app.  simpl. list_assoc_r'.  reflexivity.
simpl in X0.
(* now cut on smaller formula *)
specialize (isub A (isub_Box A) _ fpl _ X0).
inversion isub. clear isub.
erequire X1.  specialize (X1 [] []).  do 3 erequire X1.
require X1. reflexivity.  require X1.
list_assoc_l'.  reflexivity. simpl in X1.
(* now contraction *)
specialize (lctr_rel_admL (map (@WBox _) X)).
destruct lctr_rel_admL. erequire r.  erequire r.  require r.
2: eapply (radmD r) in X1.
eapply (Sctxt_relI_eq _ _ _ _ _ [] _ [] _).
apply (lctr_relLI (map (@WBox _) X) X).
simpl. list_assoc_r'. reflexivity. reflexivity.
(* now box rule and exchange *)
simpl in X1.  rewrite - !map_app.
eapply derI. apply (rsubD rs).
apply K4prrule_I. apply dersrec_singleI.
clear X0 dl dr fpl rs.
do 3 erequire adm_exchL.  require adm_exchL.
2: apply (admDs adm_exchL X1).
rewrite !map_app.  swap_tac.
Qed.

Check gs2_k4_Box_Box.

Definition gs2_k4sw_k4_Box_Box (V : Set) (fml : PropF V) psl psr cl cr :=
  @gs2_k4_Box_Box V fml _ psl psr cl cr
    (@admK4swexchL _) (@K4sw_lctr_rel_admL _) (@rsK4_sw V).  

(* results so far 
Check gen_step2_lemT.
Check gs2_wkL.  Check gs2_wkR. (* last rule wk *)
Check k4_sw_cut_adm_Bot. (* cut formula Bot *)
Check k4sw_gs2_spr_idoL. (* last rule seqrule (princrule (V:=V)) *)
Check gen_cut_adm_Imp. (* cut formula Imp, inductively *)
Check gs2_Imp. (* given inductive cut_adm, gs2 holds *)
Check @k4sw_gs2_Imp. (* given inductive cut_adm, gs2 holds *)
Check @k4sw_gs2_Bot. (* given inductive cut_adm, gs2 holds *)
Check gs2_k4_Box_Box. 
*)

Lemma k4sw_gs2 V fml psl psr cl cr:
  @K4rules_sw V psl cl -> @K4rules_sw V psr cr ->
  gen_step2 (cedc K4rules_sw) fml isubfml (derrec K4rules_sw emptyT)
        (derrec K4rules_sw emptyT) psl cl psr cr.
Proof. intros k4l k4r.  destruct k4l.
- destruct k4r.
+ apply gs2_k4sw_k4_Box_Box ; assumption.
+ destruct fml.
* apply k4sw_gs2_spr_idoL.  apply (ido_VarL v). apply s.
* apply k4sw_gs2_Bot.  exact (K4_sw_I k). exact (cplsw_I s).
* apply k4sw_gs2_Imp. exact (K4_sw_I k). exact (cplsw_I s).
* apply k4sw_gs2_spr_idoL. apply ido_WBoxL. exact s.
* apply k4sw_gs2_spr_idoL. apply ido_BBoxL. exact s.
+ apply gs2_wkR. apply rsK4_wk. exact c1.
- destruct fml.
+ apply k4sw_gs2_spr_idoR.  apply (ido_VarR v). apply s.
+ apply k4sw_gs2_Bot.  exact (cplsw_I s). exact k4r.  
+ apply k4sw_gs2_Imp.  exact (cplsw_I s). exact k4r.  
+ apply k4sw_gs2_spr_idoR. apply ido_WBoxR. exact s.
+ apply k4sw_gs2_spr_idoR. apply ido_BBoxR. exact s.
- apply gs2_wkL. apply rsK4_wk. exact c0.
Qed.

Lemma AccT_isubfml V fml: AccT (@isubfml V) fml.
induction fml ; apply AccT_intro ; intros ; inversion H ; assumption. Qed.

Theorem k4sw_cut_adm V fml cl cr: derrec (@K4rules_sw V) emptyT cl ->  
  derrec K4rules_sw emptyT cr -> cedc K4rules_sw fml cl cr.
Proof. intros dl dr.
eapply (@gen_step2_lemT _ _ _ (cedc (@K4rules_sw V)) fml isubfml).
apply AccT_isubfml.
intros *. intros ra rb.  apply (k4sw_gs2 ra rb).
exact dl. exact dr.
Qed.

Check k4sw_gs2.  Check k4sw_cut_adm.

Lemma hs2_cedc_lem V dtr cf la ls ls' ra ra' rs 
  (cre : @derrec_fc_concl _ K4rules emptyT dtr = (ra ++ cf :: ra', rs)) :
  InT cf ra + InT cf ra' ->
  derrec (@K4rules V) emptyT (la ++ ra ++ ra', ls ++ ls' ++ rs).
Proof. intros *. destruct dtr. rewrite (der_fc_concl_eq d) in cre. subst.
intro inba. destruct inba ; apply InT_split in i ; cD ; subst.
+ pose (K4_sctr_rel_admL cf).
destruct r.  erequire r.  erequire r.  require r. 
eapply (Sctxt_relI _ _ _ i ra' [] rs). eapply (sctr_relLI _ i0).
destruct r. require d0. clear d0. 
revert d. simpl. list_assoc_r. simpl. intro d. exact d.
simpl in d0. clear d.
pose gen_weakening.  unfold can_gwk in c. unfold gwk_valid in c.
eapply c. apply d0. list_assoc_r. apply gen_ext_appL. apply gen_ext_refl.
list_assoc_l. apply gen_ext_appL. apply gen_ext_refl.
+ pose (K4_sctr_rel_admL cf).
destruct r.  erequire r.  erequire r.  require r. 
eapply (Sctxt_relI _ _ _ ra i0 [] rs). eapply (sctr_relLI _ i).
destruct r. require d0. clear d0. 
revert d. simpl. list_assoc_r. simpl. intro d. exact d.
simpl in d0. clear d.
(* now need to do exchange between i and cf *)
eapply admD.  apply (@admK4exchL _ _ (la ++ ra ++ cf :: i ++ i0)).
swap_tac_Rc. apply dersrec_singleI.
pose gen_weakening.  unfold can_gwk in c. unfold gwk_valid in c.
eapply c. apply d0. list_assoc_r. apply gen_ext_appL. apply gen_ext_refl.
list_assoc_l. apply gen_ext_appL. apply gen_ext_refl. 
Qed.

Lemma hs2_k4_Box V cf psl psr cl cr dtl dtr:
  cgerule (@K4prrule V) psl cl -> cgerule (@K4prrule V) psr cr ->
  botRule_fc dtl psl cl -> botRule_fc dtr psr cr -> 
  sumh_step2_tr (@cedc_fc _ K4rules) cf isubfml dtl dtr.
Proof. intros clg crg brl brr.
unfold sumh_step2_tr. unfold sum_step2_tr.
intros isub fp.
apply cedc_fcI. intros * cle cre. 

(* first, lemma to cover case where cf in ra or ra' *)
assert (InT cf ra + InT cf ra' ->
  derrec K4rules emptyT (la ++ ra ++ ra', ls ++ ls' ++ rs)) as inarr.
eapply hs2_cedc_lem. exact cre.
destruct clg as [psl' cla cls clea cles k4l gela gels].
destruct crg as [psr' cra crs crea cres k4r gera gers].
rewrite (botRule_fc_concl brl) in cle.
rewrite (botRule_fc_concl brr) in cre.
injection cle as .  injection cre as . subst.
pose gels as gels'.  apply gen_ext_diff in gels'. destruct gels'.
all: cycle 1.  (* case where box formula on left is weakened in *)
{ clear fp isub k4r gera gers brr. 
eapply derI. apply K4_I.
eapply CGctxt. exact k4l. apply gen_ext_appR. exact gela.
list_assoc_l.  apply gen_ext_appR. exact g.
exact (botRule_fc_drs brl). }
pose gera as gera'. apply gen_ext_diff in gera'.  destruct gera'. 
all: cycle 1.  (* case where box formula on right is weakened in *)
{ clear fp isub k4l gela i brl. 
eapply derI. apply K4_I.
eapply CGctxt. exact k4r. apply gen_ext_appL. exact g.
list_assoc_l.  apply gen_ext_appL. exact gers.
exact (botRule_fc_drs brr). }
(* case where box formula is not weakened in on either side *)
(* first, recreate new trees without weakening in K4 rule *)
destruct dtl.  destruct dtr. 
destruct d. destruct e. destruct d0. destruct e. simpl in fp.
(* need to show ps = psl' and ps0 = psr' *)
pose (botRule_fc_ps brl) as psl. simpl in psl.
rewrite -> (dersrec_trees_concls_eq d) in psl.
pose (botRule_fc_ps brr) as psr. simpl in psr.
rewrite -> (dersrec_trees_concls_eq d0) in psr. subst.
(* now we can reconstruct trees without weakening in the last step on left,
  and use induction with prem of box rule on right *)
pose (derI (cla, cls) (K4_I (cgerule_id _ _ _ k4l)) d) as dtl.
inversion k4r. subst.  
revert fp.  dependent inversion d0. simpl. intro fp.
specialize (fp (fcI dtl) (fcI d1)).  simpl in fp. require fp. 
apply Lt.lt_n_S. apply Plus.plus_lt_compat_l.
apply Lt.le_lt_n_Sm.  apply Max.le_max_l.
subst. inversion fp. 
rewrite (der_fc_concl_eq dtl) in X.
rewrite (der_fc_concl_eq d1) in X.
inversion k4l. subst.
inversion i ; subst. 2: inversion H0.
apply WBox_InT in i0. apply InT_split in i0.  cD. subst.
clear brl brr d2.
rewrite map_app in X.  simpl in X.
erequire X. specialize (X [] []).
revert X. list_assoc_r'. intro.
erequire X. erequire X. erequire X. require X.
simpl. reflexivity.  require X.  reflexivity. simpl in X.
(* now do a cut by induction on subformula between this (as right side)
  and premise of box rule on left *)
clear fp dtl d1. inversion d. subst.
specialize (isub phi0 (isub_Box phi0) (fcI X0) (fcI X)).
inversion isub.
rewrite (der_fc_concl_eq X0) in X2.
rewrite (der_fc_concl_eq X) in X2.
erequire X2. specialize (X2 [] []).
erequire X2. erequire X2. erequire X2. require X2.
simpl. reflexivity.  require X2. list_assoc_l'. reflexivity. simpl in X2.
(* now need to do contraction *)
clear X d0 k0 k4l k4r X0 isub i X1 d k.
pose (K4_lctr_rel_admL (map (@WBox _) Gam0)) as k4ctr.
destruct k4ctr. erequire r.  erequire r.  require r. 
eapply (Sctxt_relI _ _ _ [] _ [] _). eapply (lctr_relLI _ Gam0).
destruct r. require d. clear d.  apply (arg_cong_imp' _ X2).
simpl. list_assoc_r'. reflexivity.
(* now exchange *)
simpl in d. clear X2.
assert (derrec K4rules emptyT 
  ((map (@WBox V) (Gam0 ++ i0 ++ i1) ++ (Gam0 ++ i0 ++ i1)), [phi])).
eapply admD.  apply admK4exchL.
2: apply (dersrec_singleI d).
rewrite !map_app. swap_tac. clear d.
(* now need to work out application of box rule *)
clear gels.
rewrite map_app in gera. simpl in gera.
apply gen_ext_splitR in gera. cD.
acacD'T2 ; inversion gera3 ; subst ; clear gera3. 
- destruct gera1. 
+ simpl in H. injection H as . subst.  rewrite app_nil_r in gera4. subst.
eapply derI'. apply (dersrec_singleI X).
apply K4_I. eapply CGctxt. apply K4prrule_I.
rewrite !map_app.
repeat apply gen_ext_app ; assumption.
repeat apply gen_ext_appL. assumption.
+ simpl in H. injection H as . subst. apply inarr. right.
apply (gen_ext_InT X0). solve_InT.
- apply inarr. right.  apply (gen_ext_InT X0). solve_InT.
- injection H as . subst. rewrite app_nil_r in gera2.
eapply derI'. apply (dersrec_singleI X).
apply K4_I. eapply CGctxt. apply K4prrule_I.
rewrite !map_app.
repeat apply gen_ext_app ; assumption.
repeat apply gen_ext_appL. assumption.
- apply inarr. right.  apply (gen_ext_InT X0). solve_InT.
- apply inarr. left.  apply (gen_ext_InT gera2). solve_InT.
- apply inarr. left.  apply (gen_ext_InT gera2). solve_InT.
Qed.

Check hs2_k4_Box.

(* can't use gentree.gs2c_gs2tr directly *)
Lemma gs2c_gs2tr_cedc W rules A sub (ca cb : Seql W) dta dtb:
  iffT (@gen_step2_c _ _ rules rules W (cedc rules) A sub ca cb dta dtb)
    (gen_step2_tr (@cedc_fc W rules) A sub (fcI dta) (fcI dtb)).
Proof.  eapply iffT_trans.  apply gs2c_gs2tr.
(* problem, cedc_fc_iff not an equality *)
unfold gen_step2_tr. unfold gen_step2_c. simpl.
apply pair ; intros.
- apply cedc_fc_iff. simpl. apply X.
+ intros. apply cedc_fc_iff. eapply X0 ; eassumption.
+ intros. specialize (X1 dtna X3). apply cedc_fc_iff in X1. 
simpl in X1. exact X1.
+ intros. specialize (X2 dtnb X3). apply cedc_fc_iff in X2. 
simpl in X2. exact X2.
- require X.  intros. apply cedc_fc_iff. eapply X0 ; eassumption.
require X. intros. apply cedc_fc_iff. simpl. eapply X1 ; eassumption.
require X. intros. apply cedc_fc_iff. simpl. eapply X2 ; eassumption.
apply cedc_fc_iff in X. simpl in X. exact X. Qed.

Lemma gs2_hs2_cedc V rules sub (fml : V) psl cl psr cr dtl dtr:
  botRule_fc dtl psl cl -> botRule_fc dtr psr cr ->
  gen_step2 (cedc rules) fml sub (derrec rules emptyT)
    (derrec rules emptyT) psl cl psr cr ->
  height_step2_tr (@cedc_fc _ rules) fml sub dtl dtr.
Proof. intros brl brr gs2.  apply gs2_tr_height.
destruct dtl.  destruct dtr.
apply gs2c_gs2tr_cedc.  apply gs2_gs2c. rewrite <- !der_botr_ps_eq.
inversion brl.  inversion brr.
rewrite H. clear H.  rewrite H1. clear H1.
simpl in H0.  rewrite (der_concl_eq d) in H0.  
simpl in H2.  rewrite (der_concl_eq d0) in H2.
subst. exact gs2. Qed.

Definition gs2_sumh_cedc V rules sub fml psl cl psr cr dtl dtr brl brr gs2 :=
  hs2_sumh (@gs2_hs2_cedc V rules sub fml psl cl psr cr dtl dtr brl brr gs2).

(* results so far - look at proof of k4sw_gs2
Check k4_cut_adm_Bot. (* cut formula Bot *)
Check k4_gs2_spr_idoL. (* last rule seqrule (princrule (V:=V)) *)
Check k4_gs2_spr_idoR. (* last rule seqrule (princrule (V:=V)) *)
Check gen_cut_adm_Imp. (* cut formula Imp, inductively *)
Check gs2_Imp. (* given inductive cut_adm, gs2 holds *)
Check k4_gs2_Imp. (* given inductive cut_adm, gs2 holds *)
Check k4_gs2_Bot. (* given inductive cut_adm, gs2 holds *)
Check gs2_k4_Box_Box. 
Check hs2_k4_Box.
*)

Lemma k4_sumh V fml psl psr cl cr dtl dtr :
  @K4rules V psl cl -> @K4rules V psr cr ->
  botRule_fc dtl psl cl -> botRule_fc dtr psr cr -> 
  sumh_step2_tr (@cedc_fc _ K4rules) fml isubfml dtl dtr.
Proof. intros k4l k4r brl brr.
destruct k4l.
- destruct k4r.
+ eapply (hs2_k4_Box c0 c2 brl brr).
+ apply (gs2_sumh_cedc brl brr).  destruct fml.
* apply (k4_gs2_spr_idoL _ (ido_VarL v) s).
* apply (k4_gs2_Bot _ (botRule_fc_rules brl) (botRule_fc_rules brr)).
* apply (k4_gs2_Imp (botRule_fc_rules brl) (botRule_fc_rules brr)).
* apply (k4_gs2_spr_idoL _ (ido_WBoxL _) s).
* apply (k4_gs2_spr_idoL _ (ido_BBoxL _) s).
- apply (gs2_sumh_cedc brl brr).  destruct fml.
+ apply (k4_gs2_spr_idoR _ (ido_VarR v) s).
+ apply (k4_gs2_Bot _ (botRule_fc_rules brl) (botRule_fc_rules brr)).
+ apply (k4_gs2_Imp (botRule_fc_rules brl) (botRule_fc_rules brr)).
+ apply (k4_gs2_spr_idoR _ (ido_WBoxR _) s).
+ apply (k4_gs2_spr_idoR _ (ido_BBoxR _) s).
Qed. 

Theorem k4_cut_adm V fml (dtl : derrec_fc (@K4rules V) emptyT) 
  (dtr : derrec_fc K4rules emptyT) : @cedc_fc _ K4rules fml dtl dtr.
Proof. eapply sumh_step2_tr_lem. apply AccT_isubfml.
intros *.  pose (der_botRule dta).  pose (der_botRule dtb).  cD.
eapply k4_sumh. 3: eassumption. 3: eassumption. eassumption. eassumption. Qed.

Check k4_sumh. Check k4_cut_adm.

