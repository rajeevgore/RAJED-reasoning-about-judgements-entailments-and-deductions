
(* LJ logic, using lists of formulae *)
(* lots copied from ../modal/k4_inv.v, often with same names *)
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
Require Import gen_tacs.
Require Import gen_seq gstep rtcT.
Require Import ljt.

(* probably won't need ImpRinv, AndRinv1/2 *)
Inductive ImpRinv {V} : relationT (srseqf V) :=
  | ImpRinv_I : forall C D, ImpRinv (pair [] (Imp C D)) (pair [C] D).
(*
Inductive ImpLinv2 {V} : relationT (list (PropF V)) :=
  | ImpLinv2_I : forall C D, ImpLinv2 ([Imp C D]) ([D]).
Inductive AndLinv {V} : relationT (list (PropF V)) :=
  | AndLinv_I : forall C D, AndLinv ([And C D]) ([C ; D]).
Inductive OrLinv1 {V} : relationT (list (PropF V)) :=
  | OrLinv1_I : forall C D, OrLinv1 [Or C D] [C].
Inductive OrLinv2 {V} : relationT (list (PropF V)) :=
  | OrLinv2_I : forall C D, OrLinv2 [Or C D] [D].
  *)
Inductive ImpL_And_inv {V} : relationT (list (PropF V)) :=
  | ImpL_And_inv_I : forall B C D,
    ImpL_And_inv ([Imp (And C D) B]) ([Imp C (Imp D B)]).
Inductive ImpL_Or_inv1 {V} : relationT (list (PropF V)) :=
  | ImpL_Or_inv1_I : forall B C D, ImpL_Or_inv1 [Imp (Or C D) B] [Imp C B].
Inductive ImpL_Or_inv2 {V} : relationT (list (PropF V)) :=
  | ImpL_Or_inv2_I : forall B C D, ImpL_Or_inv2 [Imp (Or C D) B] [Imp D B].

Inductive ImpLinv2s {V} : PropF V -> list (PropF V) -> Type :=
  | ImpLinv2s_I : forall C D, ImpLinv2s (Imp C D) ([D]).
Inductive AndLinvs {V} : PropF V -> list (PropF V) -> Type :=
  | AndLinvs_I : forall C D, AndLinvs (And C D) ([C ; D]).
Inductive OrLinv1s {V} : PropF V -> list (PropF V) -> Type :=
  | OrLinv1s_I : forall C D, OrLinv1s (Or C D) [C].
Inductive OrLinv2s {V} : PropF V -> list (PropF V) -> Type :=
  | OrLinv2s_I : forall C D, OrLinv2s (Or C D) [D].

Inductive fslr U W R : list U -> W -> Type := 
  | fslr_I : forall (u : U) (w : W), R u w -> fslr R [u] w. 

Definition AndLinv {V} := fslr (@AndLinvs V).
Definition OrLinv1 {V} := fslr (@OrLinv1s V).
Definition OrLinv2 {V} := fslr (@OrLinv2s V).
Definition ImpLinv2 {V} := fslr (@ImpLinv2s V).

Lemma AndLinv_I {V} (C D : PropF V) : AndLinv [And C D] [C; D].
Proof. apply fslr_I. apply AndLinvs_I. Qed.

Lemma OrLinv1_I {V} (C D : PropF V) : OrLinv1 [Or C D] [C].
Proof. apply fslr_I. apply OrLinv1s_I. Qed.

Lemma OrLinv2_I {V} (C D : PropF V) : OrLinv2 [Or C D] [D].
Proof. apply fslr_I. apply OrLinv2s_I. Qed.

Lemma ImpLinv2_I {V} (C D : PropF V) : ImpLinv2 [Imp C D] [D].
Proof. apply fslr_I. apply ImpLinv2s_I. Qed.

(* extend relation with general context on the left and a singleton on the 
  right, suitable for ImpLinv2, AndLinv. OrLinv1/2 *)
Inductive srs_ext_rel W Y R : relationT (list W * Y) :=
  | srs_ext_relI : forall ant ant' G Φ1 Φ2, R ant ant' ->
    srs_ext_rel R (Φ1 ++ ant ++ Φ2, G) (Φ1 ++ ant' ++ Φ2, G).

Lemma srs_ext_relI_eq W Y R ant ant' G (Φ1 Φ2 : list W) seq1 seq2: R ant ant' ->
  seq1 = (Φ1 ++ ant ++ Φ2, G) -> seq2 = (Φ1 ++ ant' ++ Φ2, G : Y) -> 
  srs_ext_rel R seq1 seq2.
Proof. intros. subst. apply srs_ext_relI. exact X. Qed.

Lemma LJIE V ps A B G :
  LJncrules ps ([@Imp V A B], G) -> ps = [([Imp A B], A); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion H. reflexivity.  - inversion H.  - inversion X.
- inversion X.  inversion X0.
+ inversion H2.  + inversion H2.  + inversion X1.
- inversion X. Qed.

Lemma LJAE V ps A B G :
  LJncrules ps ([@And V A B], G) -> ps = [([A ; B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion H. - inversion H.  - inversion X.
- inversion X.  inversion X0.
+ inversion H2.  reflexivity.  + inversion H2. + inversion X1.
- inversion X. Qed.

Lemma LJOE V ps A B G :
  LJncrules ps ([@Or V A B], G) -> ps = [([A], G); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion H. - inversion H.  - inversion X.
- inversion X.  inversion X0.
+ inversion H2.  + inversion H2. reflexivity.  + inversion X1.
- inversion X. Qed.

(* for use when the last rule is the rule being inverted *)
Lemma lr_geni U Y rules Γ1 Γ2 ps0 fml fmlsi any p 
  (LJIE : forall ps G, rules ps ([fml], G) -> InT (fmlsi, G) ps) :
  rules ps0 ([fml : U], p : Y) ->
  {ps' & derl (fst_ext_rls rules) ps' (Γ1 ++ fmlsi ++ Γ2, p) *
  ForallT (fun p' => {p0 & InT p0 (map (apfst (fmlsext Γ1 Γ2)) ps0) *
     clos_reflT (srs_ext_rel any) p0 p'}) ps'}.
Proof. intro ljnc.  eexists. split. apply asmI.
apply ForallT_singleI.  eexists. split.  2: apply rT_refl.
apply LJIE in ljnc. 
eapply arg1_cong_imp.  2: exact (InT_map _ ljnc).  reflexivity. Qed.

Lemma lr_gen U Y rules Γ1 Γ2 ps0 fml fmlsi any p 
  (LJAE : forall ps G, rules ps ([fml], G) -> ps = [(fmlsi, G)]) :
  rules ps0 ([fml : U], p : Y) ->
  {ps' & derl (fst_ext_rls rules) ps' (Γ1 ++ fmlsi ++ Γ2, p) *
  ForallT (fun p' => {p0 & InT p0 (map (apfst (fmlsext Γ1 Γ2)) ps0) *
     clos_reflT (srs_ext_rel any) p0 p'}) ps'}.
Proof. apply lr_geni. intros * rpg.
rewrite (LJAE ps G rpg). apply InT_eq. Qed.

Lemma fcr U V W crtsi afcd afd ps0 :
  (forall q : U, crtsi (afcd q : V) (afd q : W)) -> 
  ForallT (fun p' : W => {p0 : V &
     InT p0 (map afcd ps0) * crtsi p0 p'}) (map afd ps0).
Proof. intro caq.  apply ForallTI_forall.  intros x inxm.
apply InT_mapE in inxm. cD. subst.
eexists. split.  exact (InT_map _ inxm1). apply caq. Qed.

Lemma ncdlj V ps0 l p Γ1 Γ2 : @LJncrules V ps0 (l, p) ->
  derl LJrules (map (apfst (fmlsext Γ1 Γ2)) ps0) (Γ1 ++ l ++ Γ2, p).
Proof. intro ljnc. apply in_derl. unfold LJrules.  eapply fextI.
eapply rmI_eq.  apply ljnc. reflexivity. reflexivity. Qed.

Lemma ncdgen W Y rules ps0 l p Γ1 Γ2 : rules ps0 (l : list W, p : Y) ->
  derl (fst_ext_rls rules) (map (apfst (fmlsext Γ1 Γ2)) ps0) (Γ1 ++ l ++ Γ2, p).
Proof. intro ljnc. apply in_derl.  eapply fextI.
eapply rmI_eq.  apply ljnc. reflexivity. reflexivity. Qed.

Lemma ncdlje V ps0 p Γ1 Γ2 : @LJncrules V ps0 ([], p) ->
  derl LJrules (map (apfst (fmlsext Γ1 Γ2)) ps0) (Γ1 ++ Γ2, p).
Proof. intro ljnc. apply in_derl. unfold LJrules.  eapply fextI.
eapply rmI_eq.  apply ljnc. reflexivity. reflexivity. Qed.

Lemma ncdgene W Y rules ps0 p Γ1 Γ2 : rules ps0 ([] : list W, p : Y) ->
  derl (fst_ext_rls rules) (map (apfst (fmlsext Γ1 Γ2)) ps0) (Γ1 ++ Γ2, p).
Proof. intro ljnc. apply in_derl.  eapply fextI.
eapply rmI_eq.  apply ljnc. reflexivity. reflexivity. Qed.

Lemma serl U W R G H J p : srs_ext_rel R (H, p) (J : list U, p : W) -> 
  srs_ext_rel R (G ++ H, p) (G ++ J, p).
Proof. intro srs. inversion srs. subst. clear srs.
pose (srs_ext_relI _ _ _ p (G ++ Φ1) Φ2 X).
rewrite -> !app_assoc in s.  rewrite !app_assoc.  exact s.  Qed.

Lemma serr U W R G H J p : srs_ext_rel R (H, p) (J : list U, p : W) -> 
  srs_ext_rel R (H ++ G, p) (J ++ G, p).
Proof. intro srs. inversion srs. subst. clear srs.
pose (srs_ext_relI _ _ _ p Φ1 (Φ2 ++ G) X).
rewrite - !app_assoc.  exact s.  Qed.

Lemma serrc U W R G H J p : srs_ext_rel R ([H], p) ([J : U], p : W) -> 
  srs_ext_rel R (H :: G, p) (J :: G, p).
Proof. intro srs. eapply serr in srs. simpl in srs. exact srs. Qed.

Lemma serrc1 U W R G H J p : srs_ext_rel R ([H : U], p) (J, p : W) -> 
  srs_ext_rel R (H :: G, p) (J ++ G, p).
Proof. intro srs. eapply serr in srs. simpl in srs. exact srs. Qed.

Lemma serrc2 U W R G H J p : srs_ext_rel R (H, p) ([J : U], p : W) -> 
  srs_ext_rel R (H ++ G, p) (J :: G, p).
Proof. intro srs. eapply serr in srs. simpl in srs. exact srs. Qed.

Lemma serlc U W R (x : U) H J p : srs_ext_rel R (H, p) (J, p : W) -> 
  srs_ext_rel R (x :: H, p) (x :: J, p).
Proof. intro srs. exact (serl [x] srs). Qed.

Lemma serc2 U W R G H J1 J2 p : 
  srs_ext_rel R ([H], p) ([J1 : U ; J2], p : W) -> 
  srs_ext_rel R (H :: G, p) (J1 :: J2 :: G, p).
Proof. intro srs. eapply serr in srs. simpl in srs. exact srs. Qed.

Lemma serne U W R H J p : R H J -> srs_ext_rel R (H, p) (J : list U, p : W).
Proof. intro rhj. 
pose (srs_ext_relI _ _ _ p [] [] rhj).
simpl in s. rewrite -> !app_nil_r in s. exact s. Qed.

Ltac apser := repeat (apply serr || apply serl) ; 
  try apply serrc2 ; try apply serrc1 ; 
  try apply serc2 ; try apply serrc ; try apply serne.

(* version which sometimes works better *)
Ltac apser' := list_assoc_l' ; repeat (apply serr) ;
  list_assoc_r' ; repeat (apply serl) ;
  try apply serc2 ; try apply serrc ; try apply serne.

Ltac apserx := apply rT_step ; simpl ; unfold fmlsext ;  apser.

Print Implicit der_trf_rc_derl.

Lemma can_trf_genLinv_geni W Y rules genLinv ps c
  (nc_seL : forall ps cl cr, rules ps (cl, cr) -> sing_empty cl) 
  (rls_unique : forall ps u w G, 
    genLinv u w -> rules ps ([u], G) -> InT (w, G) ps) :
  fst_ext_rls rules ps c ->
  can_trf_rules_rc (@srs_ext_rel W Y (fslr genLinv)) 
    (derl (fst_ext_rls rules)) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r.
unfold can_trf_rules_rc. intros c' ser.
inversion ser. clear ser. destruct c0. simpl in H0.
unfold fmlsext in H0. inversion H0. clear H0. subst.
destruct X0.  
acacD'T2 ; subst.
- rewrite ?app_nil_r in X. 
assoc_mid H2.  eexists. split.  apply ncdgen. apply X.
apply fcr. intro. destruct q. 
apserx. apply fslr_I. exact g.
- pose (nc_seL _ _ _ X).  apply sing_empty_app_cons in s.
list_eq_ncT. cD. subst. simpl.  simpl in X. rewrite ?app_nil_r.
eapply lr_geni. 2: exact X. intros *.  apply rls_unique. exact g.
- pose (nc_seL _ _ _ X).  apply sing_empty_app_cons in s.
cD. subst. simpl.  simpl in X. rewrite ?app_nil_r.
eapply lr_geni. 2: exact X. intros *.  apply rls_unique. exact g.
- eexists. split. assoc_mid l. apply ncdgen. apply X.
apply fcr. intro. destruct q. 
apserx. apply fslr_I. exact g.
- pose (nc_seL _ _ _ X).
apply sing_empty_app in s. sD. inversion s. subst. simpl.
rewrite ?app_nil_r in X.  rewrite ?app_nil_r.
eapply lr_geni. 2: exact X. intros *.  apply rls_unique. exact g.
- list_eq_ncT. cD. subst. simpl in X.
eexists. split. assoc_mid H4. apply ncdgen. apply X.
apply fcr. intro. destruct q. 
apserx. apply fslr_I. exact g.
- list_eq_ncT. sD ; subst.
+ eexists. split.  apply ncdgene. apply X.
apply fcr. intro. destruct q. 
rewrite ?app_nil_r.
apserx. apply fslr_I. exact g.
+ simpl. rewrite ?app_nil_r.  
eapply lr_geni. 2: exact X. intros *.  apply rls_unique. exact g.
- list_eq_ncT. cD.  list_eq_ncT. cD. subst. (* simpl. NO! *) list_assoc_l'.
eexists. split. apply ncdgene. apply X.
apply fcr. intro. destruct q. 
apserx. apply fslr_I. exact g.
- eexists. split. assoc_mid l. apply ncdgen. apply X.
apply fcr. intro. destruct q. 
list_assoc_r'. simpl.  
apserx. apply fslr_I. exact g.
Qed.

Print Implicit can_trf_genLinv_geni.

Lemma can_trf_genLinv_gen W Y rules genLinv ps c
  (nc_seL : forall ps cl cr, rules ps (cl, cr) -> sing_empty cl) 
  (rls_unique : forall ps u w G, 
    genLinv u w -> rules ps ([u], G) -> ps = [(w, G)]) :
  fst_ext_rls rules ps c ->
  can_trf_rules_rc (@srs_ext_rel W Y (fslr genLinv)) 
    (derl (fst_ext_rls rules)) ps c.
Proof. apply can_trf_genLinv_geni. exact nc_seL.
intros * guw rpg. rewrite (rls_unique _ _ _ _ guw rpg). apply InT_eq. Qed.

Print Implicit can_trf_genLinv_gen.

(*
Print Implicit can_trf_AndLinv_lj.
Print Implicit can_trf_AndLinv_gen.
*)

Lemma can_trf_AndLinv_gen' V Y rules ps c
  (nc_seL : forall ps cl cr, rules ps (cl, cr) -> sing_empty cl) 
  (LJAE : forall ps A B G, rules ps ([And A B], G) -> ps = [([A; B], G)]) :
  fst_ext_rls rules ps c ->
  can_trf_rules_rc (@srs_ext_rel _ Y (fslr (@AndLinvs V))) 
    (derl (fst_ext_rls rules)) ps c.
Proof. eapply can_trf_genLinv_gen.
exact nc_seL. intros * auw. destruct auw. apply LJAE. Qed.

Check can_trf_rules_rc_rel_eqv.

About can_trf_genLinv_gen.


Lemma can_trf_AndLinv_lj V ps c: @LJrules _ ps c ->
  can_trf_rules_rc (srs_ext_rel (@AndLinv V)) (derl (@LJrules _)) ps c.
Proof. apply can_trf_genLinv_gen.  apply LJnc_seL.
intros * auv.  destruct auv.  apply LJAE.  Qed.

Lemma can_trf_OrLinv1_lj V ps c: @LJrules _ ps c ->
  can_trf_rules_rc (srs_ext_rel (@OrLinv1 V)) (derl (@LJrules _)) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJOE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_OrLinv2_lj V ps c: @LJrules _ ps c ->
  can_trf_rules_rc (srs_ext_rel (@OrLinv2 V)) (derl (@LJrules _)) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJOE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_ImpLinv2_lj V ps c: @LJrules _ ps c ->
  can_trf_rules_rc (srs_ext_rel (@ImpLinv2 V)) (derl (@LJrules _)) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJIE in rocd. subst. solve_InT.  Qed.

(* now inversion results in terms of rel_adm *)
Lemma rel_adm_AndLinv V :
  rel_adm LJrules (srs_ext_rel (@AndLinv V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_AndLinv_lj V).  Qed.

Lemma rel_adm_OrLinv1 V :
  rel_adm LJrules (srs_ext_rel (@OrLinv1 V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_OrLinv1_lj V).  Qed.

Lemma rel_adm_OrLinv2 V :
  rel_adm LJrules (srs_ext_rel (@OrLinv2 V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_OrLinv2_lj V).  Qed.

Lemma can_rel_ImpLinv2 V seq :
derrec LJrules emptyT seq ->
  can_rel LJrules (srs_ext_rel (Y:=PropF V)) ImpLinv2 seq.
Proof. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_ImpLinv2_lj V).  Qed.

Lemma rel_adm_ImpLinv2 V :
  rel_adm LJrules (srs_ext_rel (@ImpLinv2 V)).
Proof. apply crd_ra. apply can_rel_ImpLinv2. Qed.
