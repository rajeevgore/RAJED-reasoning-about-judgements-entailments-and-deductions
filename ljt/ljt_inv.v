
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
Require Import List_lemmasT swappedT.
Require Import gen_tacs.
Require Import gen_seq gstep rtcT.
Require Import ljt.

Inductive ImpRinv {V} : PropF V -> srseq (PropF V) -> Type :=
  | ImpRinv_I : forall C D, ImpRinv (Imp C D) (pair [C] D).

Inductive AndRinv1 {V} : relationT (PropF V) :=
  | AndRinv1_I : forall C D, AndRinv1 (And C D) C.
Inductive AndRinv2 {V} : relationT (PropF V) :=
  | AndRinv2_I : forall C D, AndRinv2 (And C D) C.
Inductive OrRinv1 {V} : relationT (PropF V) :=
  | OrRinv1_I : forall C D, OrRinv1 (Or C D) C.
Inductive OrRinv2 {V} : relationT (PropF V) :=
  | OrRinv2_I : forall C D, OrRinv2 (Or C D) C.
Inductive BotRinv {V} : relationT (PropF V) :=
  | BotRinv_I : forall C, BotRinv (Bot V) C.

Inductive ImpL_And_invs {V} : PropF V -> list (PropF V) -> Type :=
  | ImpL_And_invs_I : forall B C D,
    ImpL_And_invs (Imp (And C D) B) ([Imp C (Imp D B)]).
Inductive ImpL_Or_invs {V} : PropF V -> list (PropF V) -> Type :=
  | ImpL_Or_invs_I : forall B C D, 
    ImpL_Or_invs (Imp (Or C D) B) [Imp C B ; Imp D B].
Inductive ImpL_Imp_inv2s {V} : PropF V -> list (PropF V) -> Type :=
  | ImpL_Imp_inv2s_I : forall B C D, ImpL_Imp_inv2s (Imp (Imp C D) B) [B].
Inductive ImpL_Var_inv2s {V} : PropF V -> list (PropF V) -> Type :=
  | ImpL_Var_inv2s_I : forall B p, ImpL_Var_inv2s (Imp (Var p) B) [B].

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
Definition ImpL_And_inv {V} := fslr (@ImpL_And_invs V).
Definition ImpL_Or_inv {V} := fslr (@ImpL_Or_invs V).
Definition ImpL_Imp_inv2 {V} := fslr (@ImpL_Imp_inv2s V).
Definition ImpL_Var_inv2 {V} := fslr (@ImpL_Var_inv2s V).

Lemma AndLinv_I {V} (C D : PropF V) : AndLinv [And C D] [C; D].
Proof. apply fslr_I. apply AndLinvs_I. Qed.

Lemma OrLinv1_I {V} (C D : PropF V) : OrLinv1 [Or C D] [C].
Proof. apply fslr_I. apply OrLinv1s_I. Qed.

Lemma OrLinv2_I {V} (C D : PropF V) : OrLinv2 [Or C D] [D].
Proof. apply fslr_I. apply OrLinv2s_I. Qed.

Lemma ImpLinv2_I {V} (C D : PropF V) : ImpLinv2 [Imp C D] [D].
Proof. apply fslr_I. apply ImpLinv2s_I. Qed.

(* extend relation on rhs with general context on the left
  suitable for AndRinv1/2 OrRinv1/2 *)
Inductive ant_rel W Y R : relationT (list W * Y) :=
  | ant_relI : forall ant suc suc', R suc suc' ->
    ant_rel R (ant, suc) (ant, suc').

(* extend relation with general context on the left and a singleton on the 
  right, suitable for ImpLinv2, AndLinv. OrLinv1/2 *)
Inductive srs_ext_rel W Y R : relationT (list W * Y) :=
  | srs_ext_relI : forall ant ant' G Φ1 Φ2, R ant ant' ->
    srs_ext_rel R (Φ1 ++ ant ++ Φ2, G) (Φ1 ++ ant' ++ Φ2, G).

Lemma srs_ext_relI_eq W Y R ant ant' G (Φ1 Φ2 : list W) seq1 seq2: R ant ant' ->
  seq1 = (Φ1 ++ ant ++ Φ2, G) -> seq2 = (Φ1 ++ ant' ++ Φ2, G : Y) -> 
  srs_ext_rel R seq1 seq2.
Proof. intros. subst. apply srs_ext_relI. exact X. Qed.

Definition srs_ext_relI_eqc W Y R ant ant' G Φ1 Φ2 seq2 raa :=
  @srs_ext_relI_eq W Y R ant ant' G Φ1 Φ2 _ seq2 raa eq_refl.

(* extend relation with general context on the left,
  given right rule which may put stuff on the left in premise, eg ImpR
  right, suitable for ImpLinv2, AndLinv. OrLinv1/2 *)
Inductive rr_ext_rel W Y R : relationT (list W * Y) :=
  | rr_ext_relI : forall ant G G' Φ1 Φ2, R G (ant, G') ->
    rr_ext_rel R (Φ1 ++ Φ2, G) (Φ1 ++ ant ++ Φ2, G').

Lemma rr_ext_relI_eq W Y R ant G G' (Φ1 Φ2 : list W) seq1 seq2:
  R G (ant, G') -> seq1 = (Φ1 ++ Φ2, G) ->
  seq2 = (Φ1 ++ ant ++ Φ2, G' : Y) -> rr_ext_rel R seq1 seq2.
Proof. intros. subst. apply rr_ext_relI. exact X. Qed.

Definition rr_ext_relI_eqc W Y R ant G G' Φ1 Φ2 seq2 rga := 
  @rr_ext_relI_eq W Y R ant G G' Φ1 Φ2 _ seq2 rga eq_refl. 

Lemma LJAIAE V ps B C D G :
  LJAncrules ps ([@Imp V (And C D) B], G) -> ps = [([Imp C (Imp D B)], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion H3 ; inversion H5. reflexivity.
- inversion H. - inversion H.  - inversion H.  - inversion X. 
- inversion X.  inversion X0. 
+ inversion H2. + inversion H2.  + inversion X1.  
- inversion X.  Qed.

Lemma LJAIOE V ps B C D G :
  LJAncrules ps ([@Imp V (Or C D) B], G) -> ps = [([Imp C B; Imp D B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion H3 ; inversion H5. reflexivity.
- inversion H. - inversion H.  - inversion H.  - inversion X. 
- inversion X.  inversion X0. 
+ inversion H2. + inversion H2.  + inversion X1.  
- inversion X.  Qed.

Lemma LJAIIE V ps B C D G :
  LJAncrules ps ([@Imp V (Imp C D) B], G) -> ps = [([Imp D B; C], D); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion H3 ; inversion H5. 
- inversion H. reflexivity.
- inversion H.  - inversion H.  - inversion X. 
- inversion X.  inversion X0. 
+ inversion H2. + inversion H2.  + inversion X1.  
- inversion X.  Qed.

Lemma LJAIpE V ps B p G : LJAncrules ps ([@Imp V (Var p) B], G) ->
  ps = [([Imp (Var p) B], Var p); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion H3 ; inversion H5. 
- inversion H.  - inversion H. reflexivity.
- inversion H.  - inversion X. 
- inversion X.  inversion X0. 
+ inversion H2. + inversion H2.  + inversion X1.  
- inversion X.  Qed.

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

Lemma LJAAE V ps A B G :
  LJAncrules ps ([@And V A B], G) -> ps = [([A ; B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion H3 ; inversion H5.
- inversion H. - inversion H.  - inversion H.  - inversion X. 
- inversion X.  inversion X0. 
+ inversion H2.  reflexivity.  + inversion H2.  + inversion X1.  
- inversion X.  Qed.

Lemma LJOE V ps A B G :
  LJncrules ps ([@Or V A B], G) -> ps = [([A], G); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion H. - inversion H.  - inversion X.
- inversion X.  inversion X0.
+ inversion H2.  + inversion H2. reflexivity.  + inversion X1.
- inversion X. Qed.

Lemma LJAOE V ps A B G :
  LJAncrules ps ([@Or V A B], G) -> ps = [([A], G); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion H3 ; inversion H5.
- inversion H. - inversion H.  - inversion H.  - inversion X. 
- inversion X.  inversion X0. 
+ inversion H2.  + inversion H2.  reflexivity.  + inversion X1.  
- inversion X.  Qed.

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

Lemma fcr2 U V W X Y crtsi afcd afd fpp fpg ps0 :
  (forall q : U, crtsi (afcd (fpp q : X) : V) (afd (fpg q : Y) : W)) -> 
  ForallT (fun p' : W => {p0 : V &
     InT p0 (map afcd (map fpp ps0)) * crtsi p0 p'}) (map afd (map fpg ps0)).
Proof. intro caq.  apply ForallTI_forall.  intros x inxm.
apply InT_mapE in inxm. cD. subst.
apply InT_mapE in inxm1. cD. subst.
eexists. split.  exact (InT_map _ (InT_map _ inxm2)). apply caq. Qed.

Lemma ncdgen W Y rules ps0 l p Γ1 Γ2 : rules ps0 (l : list W, p : Y) ->
  derl (fst_ext_rls rules) (map (apfst (fmlsext Γ1 Γ2)) ps0) (Γ1 ++ l ++ Γ2, p).
Proof. intro ljnc. apply in_derl.  eapply fextI.
eapply rmI_eq.  apply ljnc. reflexivity. reflexivity. Qed.

Definition ncagen W Y rules ps0 l p Γ1 Γ2 rplp :=
  derl_sub_adm (@ncdgen W Y rules ps0 l p Γ1 Γ2 rplp).

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

(* similar to above for rr_ext_rel *)

Lemma rrel U W R G H J p q : rr_ext_rel R (H, p) (J : list U, q : W) -> 
  rr_ext_rel R (G ++ H, p) (G ++ J, q).
Proof. intro rr. inversion rr. subst. clear rr.
pose (rr_ext_relI _ _ _ _ (G ++ Φ1) Φ2 X).
rewrite -> !app_assoc in r.  rewrite !app_assoc.  exact r.  Qed.

Lemma rrer U W R G H J p q : rr_ext_rel R (H, p) (J : list U, q : W) -> 
  rr_ext_rel R (H ++ G, p) (J ++ G, q).
Proof. intro rr. inversion rr. subst. clear rr.
pose (rr_ext_relI _ _ _ _ Φ1 (Φ2 ++ G) X).
rewrite - !app_assoc.  exact r.  Qed.

Lemma rreln U W R G J p q : R p (J : list U, q : W) -> 
  rr_ext_rel R (G, p) (G ++ J, q).
Proof. intro r. 
pose (rr_ext_relI _ _ _ _ G [] r).
rewrite -> !app_nil_r in r0. exact r0. Qed.

Lemma rrern U W R G J p q : R p (G : list U, q : W) -> 
  rr_ext_rel R (J, p) (G ++ J, q).
Proof. intro r. 
pose (rr_ext_relI _ _ _ _ [] J r).
exact r0. Qed.

Lemma rrerc U W R G H J p q : rr_ext_rel R ([H], p) ([J : U], q : W) -> 
  rr_ext_rel R (H :: G, p) (J :: G, q).
Proof. intro rr. eapply rrer in rr. simpl in rr. exact rr. Qed.

Lemma rrerc1 U W R G H J p q : rr_ext_rel R ([H : U], p) (J, q : W) -> 
  rr_ext_rel R (H :: G, p) (J ++ G, q).
Proof. intro rr. eapply rrer in rr. simpl in rr. exact rr. Qed.

Lemma rrerc2 U W R G H J p q : rr_ext_rel R (H, p) ([J : U], q : W) -> 
  rr_ext_rel R (H ++ G, p) (J :: G, q).
Proof. intro rr. eapply rrer in rr. simpl in rr. exact rr. Qed.

Lemma rrelc U W R (x : U) H J p q : rr_ext_rel R (H, p) (J, q : W) -> 
  rr_ext_rel R (x :: H, p) (x :: J, q).
Proof. intro rr. exact (rrel [x] rr). Qed.

Ltac aprre := repeat (apply rrer || apply rrel || apply rrelc) ; 
  try apply rrerc2 ; try apply rrerc1 ; try apply rrerc ;
  try apply rrern ; try apply rreln.

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

(** admissibility of inversion for LJ **)
Lemma can_trf_AndLinv_lj {V} ps c: @LJrules V ps c ->
  can_trf_rules_rc (srs_ext_rel AndLinv) (derl LJrules) ps c.
Proof. apply can_trf_genLinv_gen.  apply LJnc_seL.
intros * auv.  destruct auv.  apply LJAE.  Qed.

Lemma can_trf_OrLinv1_lj {V} ps c: @LJrules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv1) (derl LJrules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJOE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_OrLinv2_lj {V} ps c: @LJrules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv2) (derl LJrules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJOE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_ImpLinv2_lj {V} ps c: @LJrules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpLinv2) (derl LJrules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJIE in rocd. subst. solve_InT.  Qed.

(* now inversion results in terms of rel_adm *)
Lemma LJ_rel_adm_AndLinv {V} : rel_adm LJrules (srs_ext_rel (@AndLinv V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_derl.  exact can_trf_AndLinv_lj.  Qed.

Lemma LJ_rel_adm_OrLinv1 {V} : rel_adm LJrules (srs_ext_rel (@OrLinv1 V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_derl.  exact can_trf_OrLinv1_lj.  Qed.

Lemma LJ_rel_adm_OrLinv2 {V} : rel_adm LJrules (srs_ext_rel (@OrLinv2 V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_derl.  exact can_trf_OrLinv2_lj.  Qed.

Lemma LJ_can_rel_ImpLinv2 {V} seq :
derrec LJrules emptyT seq ->
  can_rel LJrules (srs_ext_rel (Y:=PropF V)) ImpLinv2 seq.
Proof. unfold can_rel.
apply der_trf_rc_derl.  exact can_trf_ImpLinv2_lj.  Qed.

Lemma LJ_rel_adm_ImpLinv2 {V} : rel_adm LJrules (srs_ext_rel (@ImpLinv2 V)).
Proof. apply crd_ra. apply LJ_can_rel_ImpLinv2. Qed.

(** admissibility of inversion for LJA **)
Lemma can_trf_AndLinv_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel AndLinv) (derl LJArules) ps c.
Proof. apply can_trf_genLinv_gen.  apply LJAnc_seL.
intros * auv.  destruct auv.  apply LJAAE.  Qed.

Lemma can_trf_OrLinv1_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv1) (derl LJArules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJAnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJAOE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_OrLinv2_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv2) (derl LJArules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJAnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJAOE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_ImpL_Or_inv_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Or_inv) (derl LJArules) ps c.
Proof. apply can_trf_genLinv_gen.  apply LJAnc_seL.
intros * auv.  destruct auv.  apply LJAIOE. Qed.

Lemma can_trf_ImpL_And_inv_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_And_inv) (derl LJArules) ps c.
Proof. apply can_trf_genLinv_gen.  apply LJAnc_seL.
intros * auv.  destruct auv.  apply LJAIAE. Qed.

Lemma can_trf_ImpL_Imp_inv_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Imp_inv2) (derl LJArules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJAnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJAIIE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_ImpL_Var_inv_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Var_inv2) (derl LJArules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJAnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJAIpE in rocd. subst. solve_InT.  Qed.

(* now inversion results in terms of rel_adm *)
Lemma LJA_rel_adm_AndLinv {V} :
  rel_adm LJArules (srs_ext_rel (@AndLinv V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_AndLinv_lja V).  Qed.

Lemma LJA_rel_adm_OrLinv1 {V} :
  rel_adm LJArules (srs_ext_rel (@OrLinv1 V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_OrLinv1_lja V).  Qed.

Lemma LJA_rel_adm_OrLinv2 {V} :
  rel_adm LJArules (srs_ext_rel (@OrLinv2 V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_OrLinv2_lja V).  Qed.

(* not sure whether we will need remaining results for LJA in the form of 
  LJA_rel_adm ... or LJA_can_rel *)

(*
Lemma LJA_can_rel_ImpLinv2 {V} seq :
derrec LJrules emptyT seq ->
  can_rel LJrules (srs_ext_rel (Y:=PropF V)) ImpLinv2 seq.
Proof. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_ImpLinv2_lj V).  Qed.

Lemma LJA_rel_adm_ImpLinv2 {V} :
  rel_adm LJrules (srs_ext_rel (@ImpLinv2 V)).
Proof. apply crd_ra. apply LJA_can_rel_ImpLinv2. Qed.
*)

(** invertibility of right rules **)
Check rr_ext_rel ImpRinv.
Check fun W Y genRinv => (@rr_ext_rel W Y genRinv).

Lemma LJAil_adm_lem {V} ps c Γ1 Γ2 G : @LJAilrules V ps c -> 
  adm LJArules (map (apfst (fmlsext Γ1 Γ2)) (map (Basics.flip pair G) ps))
    (Γ1 ++ c ++ Γ2, G).
Proof. intro il.  apply ncagen.  eapply il_anc.
eapply rmI_eq. apply il.  reflexivity.  reflexivity.  Qed.

Lemma LJsl_adm_lem {V} ps c Γ1 Γ2 G : @LJslrules V ps c -> 
  adm LJArules (map (apfst (fmlsext Γ1 Γ2)) (map (Basics.flip pair G) ps))
    (Γ1 ++ c ++ Γ2, G).
Proof. intro il.  apply ncagen.  eapply lrls_anc.
eapply rmI_eq. apply il.  reflexivity.  reflexivity.  Qed.

Ltac fcr2_tac H0 := apply fcr2 ; intro ; 
apply rT_step ; simpl ; unfold fmlsext ;  rewrite ?app_nil_r ;
aprre ; exact H0.

Ltac ljailtac H2 H0 := eexists ; split ;
  [ apply LJAil_adm_lem ; apply H2 | fcr2_tac H0 ].
Ltac ljsltac H2 H0 := eexists ; split ;
  [ apply LJsl_adm_lem ; apply H2 | fcr2_tac H0 ].

Lemma f1crr W q qs R : {p : W & InT p (q :: qs) * clos_reflT R p q}.
Proof. eexists. exact (pair (InT_eq _ _) (rT_refl _ _)). Qed.

Ltac drstac fd1 fd2 X0 X2 := simpl ;  unfold fmlsext ;  apply dlCons ; [
(* need to do weakening and exchange here *)
apply (fer_der fd1 fd2) in X0 ; apply (exchL_lja X0) ;  apply fst_relI ;
rewrite ?app_nil_r ; simpl ; swap_tac_Rc |
apply dersrec_singleI ; apply (eq_rect _ _ X2) ; list_eq_assoc ].

Ltac fictac list_assoc_x := simpl ; apply ForallT_cons ; [ apply f1crr |
apply ForallT_singleI ; eexists ; apply (pair (InT_2nd _ _ _)) ;
apply rT_step ; unfold fmlsext ; list_assoc_x ;
apply rr_ext_relI ; apply ImpRinv_I ]. 

Ltac ljartac thm fc1 fc2 := eapply (@fextI _ _ _ fc1 fc2) ;
eapply rmI_eqc ; [ apply thm |  
unfold fmlsext ; simpl ; list_eq_assoc ].

Ltac ljartac' fc1 fc2 := eapply (@fextI _ _ _ fc1 fc2) ;
eapply rmI_eqc ; [ apply ImpL_anc' |  
unfold fmlsext ; simpl ; list_eq_assoc ].

Ltac admtac X1 X3 := unfold fmlsext ; rewrite ?app_nil_r ;
apply admI ; intro drs ; inversion drs ; inversion X1 ; subst ; clear X1 X3 ;
eapply derI.

Lemma can_trf_ImpRinv_lja {V} ps c : @LJArules V ps c ->
  can_trf_rules_rc (rr_ext_rel ImpRinv) (adm LJArules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r.
unfold can_trf_rules_rc. intros c' ser.
inversion ser. clear ser. destruct c0. simpl in H.
unfold fmlsext in H. inversion H. clear H. subst.
pose (LJAnc_seL X).  inversion X ; subst.
- (* LJAilrules *)
inversion X0. subst.
acacD'T2 ; subst.
apply sing_empty_app in s. sD ; subst.
+ simpl in H2.  assoc_mid H4.  ljailtac H2 H0.
+ rewrite ?app_nil_r in H2.  assoc_mid H3.  ljailtac H2 H0.
+ assoc_mid l.  ljailtac H2 H0.
+ assoc_mid l.  ljailtac H2 H0.
- (* ImpL_Imp_rule *)
inversion H. inversion H0. subst. clear H H0 s.
acacD'T2 ; subst.
+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_r.
++ admtac X1 X3.
+++ ljartac Imp_anc' (Γ1 ++ [C0]) Γ2.
+++ drstac [C0] ([] : list (PropF V)) X0 X2.

+ list_eq_ncT. cD. subst.
eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_l.
++ admtac X1 X3.
+++ ljartac Imp_anc' Γ1 (C0 :: Γ2).
+++ drstac ([] : list (PropF V)) [C0] X0 X2.

+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_l.
++ admtac X1 X3.
+++ ljartac Imp_anc' Γ1 (H1 ++ C0 :: Φ2).
+++ drstac ([] : list (PropF V)) [C0] X0 X2.

+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_r.
++ admtac X1 X3.
+++ ljartac Imp_anc' (Φ1 ++ [C0] ++ H3) Γ2.
+++ drstac [C0] ([] : list (PropF V)) X0 X2.

- (* ImpLrule_p *)
inversion H. inversion H0. subst. clear H H0 s.
acacD'T2 ; subst.
+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_r.
++ admtac X1 X3.
+++ ljartac ImpL_anc' (Γ1 ++ [C]) Γ2.
+++ drstac [C] ([] : list (PropF V)) X0 X2.

+ list_eq_ncT. cD. subst.
eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_l.
++ admtac X1 X3.
+++ ljartac ImpL_anc' Γ1 (C :: Γ2).
+++ drstac ([] : list (PropF V)) [C] X0 X2.

+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_l.
++ admtac X1 X3.
+++ ljartac ImpL_anc' Γ1 (H1 ++ C :: Φ2).
+++ drstac ([] : list (PropF V)) [C] X0 X2.

+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_r.
++ admtac X1 X3.
+++ ljartac ImpL_anc' (Φ1 ++ [C] ++ H3) Γ2.
+++ drstac [C] ([] : list (PropF V)) X0 X2.

- (* ImpRrule *)
inversion H. inversion H0. subst.  inversion H2. subst. clear H2 H0 H.
eexists. split. all: cycle 1.
apply ForallT_singleI.  eexists. split.  apply InT_eq.  apply rT_refl.
simpl in H3.  simpl. unfold fmlsext. 
apply admI. intro d.  apply dersrec_singleD in d.
apply (exchL_lja d).  apply fst_relI.
exact (swap_ins _ _ _ _ [A] H3).
- (* Idrule (Var - so n/a) *)
inversion X0.  inversion H0. subst.  inversion H1.
- (* LJslrules *)
inversion X0. subst.
acacD'T2 ; subst.
apply sing_empty_app in s. sD ; subst.
+ simpl in X1.  assoc_mid H2. ljsltac X1 H0.
+ rewrite ?app_nil_r in X1.  assoc_mid H3.  ljsltac X1 H0.
+ assoc_mid l.  ljsltac X1 H0.
+ assoc_mid l.  ljsltac X1 H0.
- (* LJsrrules - different formulae *)
inversion H0.  inversion X0. subst. clear X0 H0.
inversion H6 ; inversion H.
Qed.

Lemma LJA_rel_adm_ImpR V : rel_adm LJArules (rr_ext_rel (@ImpRinv V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_adm.  exact can_trf_ImpRinv_lja.  Qed.

Lemma can_trf_genRinv_lja V genRinv ps c (rls_unique : forall ps u w, 
    genRinv u w -> LJAncrules ps ([], u) -> InT ([], w) ps) 
  (not_Imp : forall p q r, genRinv (Imp q r) p -> False)
  (not_Var : forall p v, genRinv (Var v) p -> False) :
  @LJArules V ps c -> can_trf_rules_rc (ant_rel genRinv) (adm LJArules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r.
unfold can_trf_rules_rc. intros c' ser.
inversion ser. clear ser. destruct c0. simpl in H0.
unfold fmlsext in H0. inversion H0. clear H0. subst.
inversion X ; subst.
- (* LJAilrules *)
inversion X1. subst. clear X1.
eexists. split. apply in_adm. eapply fextI. eapply rmI_eqc.
eapply il_anc. apply rmI. exact H1. reflexivity.
apply fcr2. intro. apply rT_step. simpl.
apply ant_relI. exact X0.
- (* ImpL_Imp_rule *)
inversion H. subst. clear H.
eexists [_ ; _]. split. all: cycle 1.
apply ForallT_cons. eexists. split. apply InT_eq. apply rT_refl.
apply ForallT_singleI.
eexists. split. apply InT_2nd. apply rT_step.
simpl. apply ant_relI. apply X0.
apply in_adm. simpl.
eapply fextI. eapply rmI_eq. apply Imp_anc'.
reflexivity.  reflexivity.
- (* ImpLrule_p *)
inversion H. subst. clear H.
eexists [_ ; _]. split. all: cycle 1.
apply ForallT_cons. eexists. split. apply InT_eq. apply rT_refl.
apply ForallT_singleI.
eexists. split. apply InT_2nd. apply rT_step.
simpl. apply ant_relI. apply X0.
apply in_adm. simpl.
eapply fextI. eapply rmI_eq. apply ImpL_anc'.
reflexivity.  reflexivity.
- (* ImpRrule *)
inversion H. subst. destruct (not_Imp _ _ _ X0).
- (* Idrule (Var - so n/a) *)
inversion X1. subst.  destruct (not_Var _ _ X0).
- (* LJslrules *)
inversion X1. subst. clear X1.
eexists. split. apply in_adm. eapply fextI. eapply rmI_eqc.
eapply lrls_anc. apply rmI. exact X2. reflexivity.
apply fcr2. intro. apply rT_step. simpl.
apply ant_relI. exact X0.
- (* LJsrrules *)
inversion X1. subst. clear X1.
specialize (rls_unique _ _ _ X0 X).
apply InT_mapE in rls_unique. cD. inversion rls_unique0. subst.
eexists. split. apply rsub_derl_adm. apply asmI.
apply ForallT_singleI.
eexists. split. simpl.
2: apply rT_refl.
eapply InT_map in rls_unique1.
eapply InT_map in rls_unique1.
eapply arg1_cong_imp.
2: apply rls_unique1.  reflexivity.
Qed.

About can_trf_genRinv_lja.
Lemma can_trf_AndRinv1_lja {V} ps c : @LJArules V ps c ->
  can_trf_rules_rc (ant_rel AndRinv1) (adm LJArules) ps c.
Proof. apply can_trf_genRinv_lja.
- intros * auw ljar.  destruct auw.
inversion ljar ; subst.
+ inversion X. simpl. subst. inversion H1 ; subst ; inversion H.
+ inversion H.  + inversion H.  + inversion H.  + inversion X.
+ inversion X. inversion X0 ; subst.
++ inversion H0.  ++ inversion H0.  ++ inversion X1.
+ inversion X. inversion H1 ; subst ; inversion H2 ; solve_InT.
- intros * ari. inversion ari.
- intros * ari. inversion ari.
Qed.

About can_trf_AndRinv1_lja. 

Lemma can_trf_AndRinv2_lja {V} ps c : @LJArules V ps c ->
  can_trf_rules_rc (ant_rel AndRinv2) (adm LJArules) ps c.
Proof. apply can_trf_genRinv_lja.
- intros * auw ljar.  destruct auw.
inversion ljar ; subst.
+ inversion X. simpl. subst. inversion H1 ; subst ; inversion H.
+ inversion H.  + inversion H.  + inversion H.  + inversion X.
+ inversion X. inversion X0 ; subst.
++ inversion H0.  ++ inversion H0.  ++ inversion X1.
+ inversion X. inversion H1 ; subst ; inversion H2 ; solve_InT.
- intros * ari. inversion ari.
- intros * ari. inversion ari.
Qed.

(* not inversion of any rule, but similar proof *) 
Lemma can_trf_BotRinv_lja {V} ps c : @LJArules V ps c ->
  can_trf_rules_rc (ant_rel BotRinv) (adm LJArules) ps c.
Proof. apply can_trf_genRinv_lja.
- intros * auw ljar.  destruct auw.
inversion ljar ; subst.
+ inversion X. simpl. subst. inversion H1 ; subst ; inversion H.
+ inversion H.  + inversion H.  + inversion H.  + inversion X.
+ inversion X. inversion X0 ; subst.
++ inversion H0.  ++ inversion H0.  ++ inversion X1.
+ inversion X. inversion H1 ; subst ; inversion H2 ; solve_InT.
- intros * ari. inversion ari.
- intros * ari. inversion ari.
Qed.

