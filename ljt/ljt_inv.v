
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

Lemma ImpL_Var_inv2_I {V} p (D : PropF V) : ImpL_Var_inv2 [Imp (Var p) D] [D].
Proof. apply fslr_I. apply ImpL_Var_inv2s_I. Qed.

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

Definition srs_ext_relI_eqp W Y R ant ant' G Φ1 Φ2 seq1 raa eq1 :=
  @srs_ext_relI_eq W Y R ant ant' G Φ1 Φ2 seq1 _ raa eq1 eq_refl.

Definition srs_ext_relI_c1 W Y R a := @srs_ext_relI W Y R [a].

Lemma srs_ext_relI_nil W Y R (ant ant' : list W) (G : Y) : 
  R ant ant' -> srs_ext_rel R (ant, G) (ant', G).
Proof. intro raa. pose (srs_ext_relI R _ _ G [] [] raa).
rewrite -> !app_nil_r in s. exact s. Qed.

Lemma srs_ext_relI_alt W Y R x y :
  fst_rel (ext_rel R) x y -> @srs_ext_rel W Y R x y.
Proof. intro rer. destruct rer. destruct e.
apply srs_ext_relI. exact r. Qed.

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
Definition rr_ext_relI_eqp W Y R ant G G' Φ1 Φ2 seq1 rga s1eq := 
  @rr_ext_relI_eq W Y R ant G G' Φ1 Φ2 seq1 _ rga s1eq eq_refl. 

Lemma LJAIAE V ps B C D G :
  LJAncrules ps ([@Imp V (And C D) B], G) -> ps = [([Imp C (Imp D B)], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion X0 ; inversion X1. reflexivity.
- inversion X. - inversion X.  - inversion X.  - inversion X. 
- inversion X.  inversion X0 ; inversion X1. 
- inversion X.  Qed.

Lemma LJAIOE V ps B C D G :
  LJAncrules ps ([@Imp V (Or C D) B], G) -> ps = [([Imp C B; Imp D B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion X0 ; inversion X1. reflexivity.
- inversion X. - inversion X.  - inversion X.  - inversion X. 
- inversion X.  inversion X0 ; inversion X1. 
- inversion X.  Qed.

Lemma LJAIIE V ps B C D G :
  LJAncrules ps ([@Imp V (Imp C D) B], G) -> ps = [([Imp D B; C], D); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion X0 ; inversion X1.
- inversion X. reflexivity.
- inversion X.  - inversion X.  - inversion X. 
- inversion X.  inversion X0 ; inversion X1. 
- inversion X.  Qed.

Lemma LJAIpE V ps B p G : LJAncrules ps ([@Imp V (Var p) B], G) ->
  ps = [([Imp (Var p) B], Var p); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion X0 ; inversion X1.
- inversion X.  - inversion X. reflexivity.
- inversion X.  - inversion X. 
- inversion X.  inversion X0 ; inversion X1.  
- inversion X.  Qed.

Lemma LJIE V ps A B G :
  LJncrules ps ([@Imp V A B], G) -> ps = [([Imp A B], A); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X. reflexivity.  - inversion X.  - inversion X.
- inversion X.  inversion X0 ; inversion X1.
- inversion X. Qed.

Lemma LJAE V ps A B G :
  LJncrules ps ([@And V A B], G) -> ps = [([A ; B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X. - inversion X.  - inversion X.
- inversion X.  inversion X0 ; inversion X1.  reflexivity. 
- inversion X. Qed.

Lemma LJAAE V ps A B G :
  LJAncrules ps ([@And V A B], G) -> ps = [([A ; B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion X0 ; inversion X1.
- inversion X. - inversion X.  - inversion X.  - inversion X. 
- inversion X.  inversion X0 ; inversion X1.  reflexivity. 
- inversion X.  Qed.

Lemma LJOE V ps A B G :
  LJncrules ps ([@Or V A B], G) -> ps = [([A], G); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X. - inversion X.  - inversion X.
- inversion X.  inversion X0 ; inversion X1. reflexivity.
- inversion X. Qed.

Lemma LJAOE V ps A B G :
  LJAncrules ps ([@Or V A B], G) -> ps = [([A], G); ([B], G)].
Proof. intro ljnc. inversion ljnc.
- inversion X.  inversion X0 ; inversion X1.
- inversion X. - inversion X.  - inversion X.  - inversion X. 
- inversion X.  inversion X0 ; inversion X1. reflexivity.
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

(* version of lr_genia with two different lots of rules,
  could do the same with lr_gen, lr_geni, etc *)
Lemma lr_genia2 U Y (rulesa rulesb : rlsT _) Γ1 Γ2 ps0 fml fmlsi any p 
  (LJIE : forall ps G, rulesa ps ([fml], G : Y) -> 
    forall Γ1 Γ2, adm (fst_ext_rls rulesb) (map (apfst (fmlsext Γ1 Γ2)) ps)
       (fmlsext Γ1 Γ2 fmlsi, G)) :
  rulesa ps0 ([fml : U], p : Y) ->
  {ps' & adm (fst_ext_rls rulesb) ps' (Γ1 ++ fmlsi ++ Γ2, p) *
  ForallT (fun p' => {p0 & InT p0 (map (apfst (fmlsext Γ1 Γ2)) ps0) *
     clos_reflT (srs_ext_rel any) p0 p'}) ps'}.
Proof. intro ljnc.  
eapply LJIE in ljnc.  
eexists. split.  exact ljnc.
apply ForallTI_forall.  intros * inxm.
eexists. split.  exact inxm.
apply rT_refl. Qed.

Definition lr_genia U Y rules := @lr_genia2 U Y rules rules.

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

Lemma ncgen W Y rules ps0 l p Γ1 Γ2 : rules ps0 (l : list W, p : Y) ->
  fst_ext_rls rules (map (apfst (fmlsext Γ1 Γ2)) ps0) (Γ1 ++ l ++ Γ2, p).
Proof. intro ljnc.  eapply fextI.
eapply rmI_eq.  apply ljnc. reflexivity. reflexivity. Qed.

Lemma ncgene W Y rules ps0 p Γ1 Γ2 : rules ps0 ([] : list W, p : Y) ->
  fst_ext_rls rules (map (apfst (fmlsext Γ1 Γ2)) ps0) (Γ1 ++ Γ2, p).
Proof. intro ljnc. eapply fextI.
eapply rmI_eq.  apply ljnc. reflexivity. reflexivity. Qed.

Definition ncdgen W Y rules ps0 l p Γ1 Γ2 rplp :=
  in_derl _ _ _ (@ncgen W Y rules ps0 l p Γ1 Γ2 rplp).
Definition ncagen W Y rules ps0 l p Γ1 Γ2 rplp :=
  in_adm _ _ _ (@ncgen W Y rules ps0 l p Γ1 Γ2 rplp).
Definition ncdgene W Y rules ps0 p Γ1 Γ2 rplp :=
  in_derl _ _ _ (@ncgene W Y rules ps0 p Γ1 Γ2 rplp).
Definition ncagene W Y rules ps0 p Γ1 Γ2 rplp :=
  in_adm _ _ _ (@ncgene W Y rules ps0 p Γ1 Γ2 rplp).

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

Lemma serat U W R (h1 h2 j1 j2 : U) G p : R [h1 ; h2] [j1 ; j2] ->
  srs_ext_rel R (h1 :: h2 :: G, p) (j1 :: j2 :: G, p : W).
Proof. intro rhj.  exact (srs_ext_relI _ _ _ p [] G rhj).  Qed.

Ltac apser := repeat (apply serr || apply serl) ; 
  try apply serrc2 ; try apply serrc1 ; 
  try apply serc2 ; try apply serrc ; try apply serne.

Ltac apserc := repeat (apply serr || apply serl || apply serlc) ; 
  try apply serrc2 ; try apply serrc1 ; 
  try apply serc2 ; try apply serrc ; try apply serne.

(* version which sometimes works better *)
Ltac apser' := list_assoc_l' ; repeat (apply serr) ;
  list_assoc_r' ; repeat (apply serl) ;
  try apply serc2 ; try apply serrc ; try apply serne.

(* version for atom rule *)
Ltac apserat := list_assoc_r' ; repeat (apply serl || apply serlc) ;
  apply serat.

Ltac apserx := apply rT_step ; simpl ; unfold fmlsext ;  apser.
Ltac apserxat := apply rT_step ; simpl ; unfold fmlsext ;  apserat.

(* for when last arg is unspecified *)
Lemma sercfr U W R u w Z Y : 
  R u w -> @srs_ext_rel U W (fslr R) (u :: Z, Y) (w ++ Z, Y).
Proof. intro ruw.  pose (fslr_I _ _ _ ruw).
exact (srs_ext_relI _ _ _ _ [] Z f). Qed.

Ltac apser2u ruw := apply rT_step ; unfold fmlsext ; list_assoc_r' ; 
  repeat (apply (sercfr _ _ _ _ _ ruw) || apply serlc || apply serl).

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

Lemma fcrd W Y rules any (p q : list W * Y) ps Γ1 Φ2 (ips : InT p ps) :
  apfst (fmlsext Γ1 Φ2) p = q -> 
  {ps' & derl (fst_ext_rls rules) ps' q *
  ForallT (fun p' => {p & InT p (map (apfst (fmlsext Γ1 Φ2)) ps) *
     clos_reflT (srs_ext_rel (fslr any)) p p'}) ps'}.
Proof. intro pq. eexists.  split.  apply asmI.
apply ForallT_singleI.  eexists. split.  2: apply rT_refl.
subst.  exact (InT_map _ ips). Qed. 
  
Lemma exch_derl_swap W Y (G : Y) rules A B :
  rsub (rlsmap (Basics.flip pair G) exch_rule) rules -> 
  @swapped W A B -> derl (fst_ext_rls rules) [(A, G)] (B, G).
Proof. intros rs sw.  destruct sw.
destruct B. subst. apply asmI.
destruct C. subst. apply asmI.
eapply dtderI.  2: apply asmsI.
subst. eapply fer_mono. exact rs.
apply (@fextI _ _ _ A D).  eapply rmI_eq.
apply rmI.  apply (exchI w w0 B C).
sfseq.  sfseq. Qed.

Lemma ctrcl1 W Y ferr seq wy sfg ps :
  clos_reflT sfg wy ps -> derl ferr [ps] seq -> 
  {ps' : list (list W * Y) & derl ferr ps' seq *
  ForallT (fun p' => {p & InT p [wy] * clos_reflT sfg p p'}) ps'}.
Proof. eexists. split. all: cycle 1. apply ForallT_singleI.
eexists. split. apply InT_eq. exact X. exact X0. Qed.

Lemma can_trf_genLinv_exch W Y rules genLinv ps c G Γ1 Γ2 :
  rsub (rlsmap (Basics.flip pair G) exch_rule) rules -> 
  rlsmap (Basics.flip pair G) exch_rule ps c ->
  can_trf_rules_rc (@srs_ext_rel W Y (fslr genLinv)) (derl (fst_ext_rls rules))
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. intros rs epc c' ser. destruct c.
inversion ser. subst. clear ser.  destruct X.
unfold fmlsext in H0. simpl in H0.
inversion epc. destruct X. subst. clear epc.
simpl. 
acacD'T2 ; subst. (* 12 subgoals *)
- list_eq_ncT. inversion H4.
- list_eq_ncT. inversion H4.
- inversion H7. subst. clear H7. 
eapply ctrcl1.  apser2u g. apply (exch_derl_swap rs).
apply (swapped_I Γ1 (x :: X) (w ++ Y0) Γ2) ; list_eq_assoc.
- acacD'T2 ; subst.
+ eapply ctrcl1.  apser2u g. apply (exch_derl_swap rs).
apply (swapped_I Γ1 (w ++ H4) (y0 :: H5) Γ2) ; list_eq_assoc.
+ eapply ctrcl1.  apser2u g. apply (exch_derl_swap rs).
apply (swapped_I Γ1 (x :: X) (y0 :: H5 ++ w ++ H7) Γ2) ; list_eq_assoc.

- inversion H4.
- eapply ctrcl1.  apser2u g. apply (exch_derl_swap rs).
apply (swapped_I Γ1 (x :: H6) (y0 :: Y0) (w ++ Φ2)) ; list_eq_assoc.
- inversion H7. subst.
eapply ctrcl1.  apser2u g. apply (exch_derl_swap rs).
apply (swapped_I Γ1 (w ++ H4) (y0 :: Y0) Γ2) ; list_eq_assoc.
- eapply ctrcl1.  apser2u g. apply (exch_derl_swap rs).
apply (swapped_I Γ1 (x :: H6 ++ w ++ H4) (y0 :: Y0) Γ2) ; list_eq_assoc.
- eapply ctrcl1.  apser2u g. apply (exch_derl_swap rs).
apply (swapped_I Γ1 (x :: X) (y0 :: Y0) (H2 ++ w ++ Φ2)) ; list_eq_assoc.
- list_eq_ncT. inversion H3.
- eapply ctrcl1.  apser2u g. apply (exch_derl_swap rs).
apply (swapped_I Φ1 (x :: X) (w ++ H4) Γ2) ; list_eq_assoc.
- eapply ctrcl1.  apser2u g. apply (exch_derl_swap rs).
apply (swapped_I (Φ1 ++ w ++ H2) (x :: X) (y0 :: Y0) Γ2) ; list_eq_assoc.
Qed.

Check can_trf_genLinv_exch.

(* a version for where rule may have a list of principal formulae *)
Lemma can_trf_genLinv_leml W Y rules genLinv ps cl cr Γ1 Γ2 :
  (forall u w X Y, genLinv u w -> cl = X ++ [u] ++ Y -> 
    InT (X ++ w ++ Y, cr) ps) -> rules ps (cl, cr) ->
  can_trf_rules_rc (@srs_ext_rel W Y (fslr genLinv)) (derl (fst_ext_rls rules)) 
    (map (apfst (fmlsext Γ1 Γ2)) ps) (Γ1 ++ cl ++ Γ2, cr).
Proof. intros clnl rpc. 
unfold can_trf_rules_rc. intros c' ser.
inversion ser. subst. clear ser.  destruct X.
acacD'T2 ; subst.
- rewrite ?app_nil_r in rpc.
assoc_mid H0.  eexists. split.  apply ncdgen. apply rpc.
apply fcr. intro. destruct q.  apserx. apply fslr_I. exact g.
- list_eq_ncT. cD. subst. simpl. 
specialize (clnl _ _ H0 [] g). 
rewrite ?app_nil_r in clnl.  specialize (clnl eq_refl).
eapply fcrd. exact clnl. sfseq.
- specialize (clnl _ _ _ _ g eq_refl). 
eapply fcrd. exact clnl. sfseq.
- eexists. split. assoc_mid cl. apply ncdgen. apply rpc.
apply fcr. intro. destruct q.  apserx. apply fslr_I. exact g.
- specialize (clnl _ _ [] _ g eq_refl). 
eapply fcrd. exact clnl. sfseq.
- list_eq_ncT. cD. subst. simpl in rpc.
eexists. split. assoc_mid H4. apply ncdgen. apply rpc.
apply fcr. intro. destruct q.  apserx. apply fslr_I. exact g.
- list_eq_ncT. sD ; subst.
+ eexists. split.  apply ncdgene. apply rpc.
apply fcr. intro. destruct q. 
rewrite ?app_nil_r.
apserx. apply fslr_I. exact g.
+ simpl. rewrite ?app_nil_r.  
require (clnl _ _ [] [] g).  rewrite ?app_nil_r. reflexivity.
rewrite ?app_nil_r in clnl.  
eapply fcrd. exact clnl. sfseq.
- list_eq_ncT. cD.  list_eq_ncT. cD. subst. (* simpl. NO! *) list_assoc_l'.
eexists. split. apply ncdgene. apply rpc.
apply fcr. intro. destruct q.  apserx. apply fslr_I. exact g.
- eexists. split. assoc_mid cl. apply ncdgen. apply rpc.
apply fcr. intro. destruct q. 
list_assoc_r'. simpl.  
apserx. apply fslr_I. exact g.  Qed.

Check can_trf_genLinv_leml.

Lemma can_trf_genLinv_lem W Y rules genLinv ps cl cr Γ1 Γ2 :
  (forall u w, genLinv u w -> InT u cl -> False) -> rules ps (cl, cr) ->
  can_trf_rules_rc (@srs_ext_rel W Y (fslr genLinv)) (derl (fst_ext_rls rules)) 
    (map (apfst (fmlsext Γ1 Γ2)) ps) (Γ1 ++ cl ++ Γ2, cr).
Proof. intros clnl.  apply can_trf_genLinv_leml.
intros * guw cleq.  require (clnl _ _ guw). subst. solve_InT.
destruct clnl. Qed.

Check can_trf_genLinv_lem.

Lemma can_trf_genLinv_genl W Y rules genLinv ps c
  (rls_unique : forall ps u w X Y G,
    genLinv u w -> rules ps (X ++ [u] ++ Y, G) -> InT (X ++ w ++ Y, G) ps) :
  fst_ext_rls rules ps c ->
  can_trf_rules_rc (@srs_ext_rel W Y (fslr genLinv))
    (derl (fst_ext_rls rules)) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r.
destruct c0.  apply can_trf_genLinv_leml.
intros * guw leq. subst.
exact (rls_unique _ _ _ _ _ _ guw X). exact X. Qed.

Check can_trf_genLinv_genl.

Lemma geni_lem W Y rules genLinv 
  (nc_seL : forall ps cl cr, rules ps (cl, cr) -> sing_empty cl) 
  (rls_unique : forall ps (u : W) w G, 
    genLinv u w -> rules ps ([u], G : Y) -> InT (w, G) ps) :
  forall ps u w X U G, genLinv u w ->
    rules ps (X ++ [u : W] ++ U, G : Y) -> InT (X ++ w ++ U, G) ps.
Proof. intros * guw rps.
specialize (nc_seL _ _ _ rps).
inversion nc_seL ; list_eq_ncT. inversion H0.
sD ; inversion H1. subst.
specialize (rls_unique _ _ _ _ guw rps).
rewrite ?app_nil_r. exact rls_unique. Qed.

(* as can_trf_genLinv_genl, but applying geni_lem to hyp *)
Definition can_trf_genLinv_geni W Y rules genLinv ps c nc_seL rls_unique :=
  @can_trf_genLinv_genl W Y rules genLinv ps c 
    (@geni_lem W Y rules genLinv nc_seL rls_unique).

(* formerly proved can_trf_genLinv_geni same as for can_trf_genLinv_geng,
  except changing lr_genia to lr_geni and ncagen.. to ncdgen.. *)

(* do we need can_trf_genLinv_geng(2) *)
(* version of can_trf_genLinv_geng with two lots of rules *)
Lemma can_trf_genLinv_geng2 W Y rulesa rulesb genLinv ps c
  (nc_seL : forall ps cl cr, rulesa ps (cl, cr) -> sing_empty cl) 
  (rls_unique : forall ps u w G, genLinv u w -> rulesa ps ([u], G) -> 
    forall Γ1 Γ2, adm (fst_ext_rls rulesb) (map (apfst (fmlsext Γ1 Γ2)) ps) 
      (fmlsext Γ1 Γ2 w, G)) :
  fst_ext_rls rulesa ps c -> rsub rulesa rulesb -> 
  can_trf_rules_rc (@srs_ext_rel W Y (fslr genLinv)) 
    (adm (fst_ext_rls rulesb)) ps c.
Proof. intros ljpc rab. destruct ljpc. inversion r. subst. clear r.
unfold can_trf_rules_rc. intros c' ser.
inversion ser. clear ser. destruct c0. simpl in H0.
unfold fmlsext in H0. inversion H0. clear H0. subst.
destruct X0.  
acacD'T2 ; subst.
- rewrite ?app_nil_r in X. 
assoc_mid H2.  eexists. split.  apply ncagen. exact (rab _ _ X).
apply fcr. intro. destruct q. 
apserx. apply fslr_I. exact g.
- pose (nc_seL _ _ _ X).  apply sing_empty_app_cons in s.
list_eq_ncT. cD. subst. simpl.  simpl in X. rewrite ?app_nil_r.
eapply lr_genia2.  2: exact X.  intros *.  apply rls_unique. exact g.
- pose (nc_seL _ _ _ X).  apply sing_empty_app_cons in s.
cD. subst. simpl.  simpl in X. rewrite ?app_nil_r.
eapply lr_genia2. 2: exact X. intros *.  apply rls_unique. exact g.
- eexists. split. assoc_mid l. apply ncagen. exact (rab _ _ X).
apply fcr. intro. destruct q. 
apserx. apply fslr_I. exact g.
- pose (nc_seL _ _ _ X).
apply sing_empty_app in s. sD. inversion s. subst. simpl.
rewrite ?app_nil_r in X.  rewrite ?app_nil_r.
eapply lr_genia2. 2: exact X. intros *.  apply rls_unique. exact g.
- list_eq_ncT. cD. subst. simpl in X.
eexists. split. assoc_mid H4. apply ncagen. exact (rab _ _ X).
apply fcr. intro. destruct q. 
apserx. apply fslr_I. exact g.
- list_eq_ncT. sD ; subst.
+ eexists. split.  apply ncagene. exact (rab _ _ X).
apply fcr. intro. destruct q. 
rewrite ?app_nil_r.
apserx. apply fslr_I. exact g.
+ simpl. rewrite ?app_nil_r.  
eapply lr_genia2. 2: exact X. intros *.  apply rls_unique. exact g.
- list_eq_ncT. cD.  list_eq_ncT. cD. subst. (* simpl. NO! *) list_assoc_l'.
eexists. split. apply ncagene. exact (rab _ _ X).
apply fcr. intro. destruct q. 
apserx. apply fslr_I. exact g.
- eexists. split. assoc_mid l. apply ncagen. exact (rab _ _ X).
apply fcr. intro. destruct q. 
list_assoc_r'. simpl.  
apserx. apply fslr_I. exact g.
Qed.

Print Implicit can_trf_genLinv_geng2.

Definition can_trf_genLinv_geng W Y rules genLinv ps c seL ru ljpc :=
  @can_trf_genLinv_geng2 W Y _ _ genLinv ps c seL ru ljpc (rsub_id rules).

Lemma eq_single_in X (wg : X) ps : ps = [wg] -> InT wg ps.
Proof. intro. subst. apply InT_eq. Qed.

(* as can_trf_genLinv_geni but adm in place of derl *)
Definition can_trf_genLinv_genia W Y rules genLinv ps c nc_seL ru fer :=
  (can_trf_rules_rc_mono (@rsub_derl_adm _ _) 
    (@can_trf_genLinv_geni W Y rules genLinv ps c nc_seL ru fer)).

(* as can_trf_genLinv_genia, but in rls_unique, ps = [(w, G)] *)
Definition can_trf_genLinv_gena W Y rules genLinv ps c nc_seL rls_unique :=
  @can_trf_genLinv_genia W Y rules genLinv ps c nc_seL 
  (fun ps u w G gl rps => eq_single_in (rls_unique ps u w G gl rps)).

(* as can_trf_genLinv_geni, but in rls_unique, ps = [(w, G)] *)
Definition can_trf_genLinv_gen W Y rules genLinv ps c nc_seL rls_unique :=
  @can_trf_genLinv_geni W Y rules genLinv ps c nc_seL 
  (fun ps u w G gl rps => eq_single_in (rls_unique ps u w G gl rps)).

(** admissibility of inversion for LJ **)
Lemma can_trf_AndLinv_lj {V} ps c: @LJrules V ps c ->
  can_trf_rules_rc (srs_ext_rel AndLinv) (adm LJrules) ps c.
Proof. apply can_trf_genLinv_gena.  apply LJnc_seL.
intros * auv.  destruct auv.  apply LJAE.  Qed.

Lemma can_trf_OrLinv1_lj {V} ps c: @LJrules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv1) (adm LJrules) ps c.
Proof. apply can_trf_genLinv_genia.  apply LJnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJOE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_OrLinv2_lj {V} ps c: @LJrules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv2) (adm LJrules) ps c.
Proof. apply can_trf_genLinv_genia.  apply LJnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJOE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_ImpLinv2_lj {V} ps c: @LJrules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpLinv2) (adm LJrules) ps c.
Proof. apply can_trf_genLinv_genia.  apply LJnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJIE in rocd. subst. solve_InT.  Qed.

(* now inversion results in terms of rel_adm *)
Lemma LJ_rel_adm_AndLinv {V} : rel_adm LJrules (srs_ext_rel (@AndLinv V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_adm.  exact can_trf_AndLinv_lj.  Qed.

Lemma LJ_rel_adm_OrLinv1 {V} : rel_adm LJrules (srs_ext_rel (@OrLinv1 V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_adm.  exact can_trf_OrLinv1_lj.  Qed.

Lemma LJ_rel_adm_OrLinv2 {V} : rel_adm LJrules (srs_ext_rel (@OrLinv2 V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_adm.  exact can_trf_OrLinv2_lj.  Qed.

Lemma LJ_can_rel_ImpLinv2 {V} seq :
derrec LJrules emptyT seq ->
  can_rel LJrules (srs_ext_rel (Y:=PropF V)) ImpLinv2 seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact can_trf_ImpLinv2_lj.  Qed.

Lemma LJ_rel_adm_ImpLinv2 {V} : rel_adm LJrules (srs_ext_rel (@ImpLinv2 V)).
Proof. apply crd_ra. apply LJ_can_rel_ImpLinv2. Qed.

(** admissibility of inversion for LJA **)
Lemma can_trf_AndLinv_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel AndLinv) (adm LJArules) ps c.
Proof. apply can_trf_genLinv_gena.  apply LJAnc_seL.
intros * auv.  destruct auv.  apply LJAAE.  Qed.

Lemma can_trf_OrLinv1_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv1) (adm LJArules) ps c.
Proof. apply can_trf_genLinv_genia.  apply LJAnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJAOE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_OrLinv2_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv2) (adm LJArules) ps c.
Proof. apply can_trf_genLinv_genia.  apply LJAnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJAOE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_ImpL_Or_inv_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Or_inv) (adm LJArules) ps c.
Proof. apply can_trf_genLinv_gena.  apply LJAnc_seL.
intros * auv.  destruct auv.  apply LJAIOE. Qed.

Lemma can_trf_ImpL_And_inv_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_And_inv) (adm LJArules) ps c.
Proof. apply can_trf_genLinv_gena.  apply LJAnc_seL.
intros * auv.  destruct auv.  apply LJAIAE. Qed.

Lemma can_trf_ImpL_Imp_inv2_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Imp_inv2) (adm LJArules) ps c.
Proof. apply can_trf_genLinv_genia.  apply LJAnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJAIIE in rocd. subst. solve_InT.  Qed.

Lemma can_trf_ImpL_Var_inv2_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Var_inv2) (adm LJArules) ps c.
Proof. apply can_trf_genLinv_genia.  apply LJAnc_seL.
intros * auv.  destruct auv. intro rocd.  
apply LJAIpE in rocd. subst. solve_InT.  Qed.

(* now inversion results in terms of can_rel *)
Lemma LJA_can_rel_AndLinv {V} seq :
  derrec LJArules emptyT seq ->
  can_rel LJArules (@srs_ext_rel _ _) (@AndLinv V) seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact (@can_trf_AndLinv_lja V).  Qed.

Lemma LJA_can_rel_OrLinv1 {V} seq :
  derrec LJArules emptyT seq ->
  can_rel LJArules (@srs_ext_rel _ _) (@OrLinv1 V) seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact (@can_trf_OrLinv1_lja V).  Qed.

Lemma LJA_can_rel_OrLinv2 {V} seq :
  derrec LJArules emptyT seq ->
  can_rel LJArules (@srs_ext_rel _ _) (@OrLinv2 V) seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact (@can_trf_OrLinv2_lja V).  Qed.

Definition LJA_rel_adm_AndLinv V := snd (crd_ra _ _ _) (@LJA_can_rel_AndLinv V).
Definition LJA_rel_adm_OrLinv1 V := snd (crd_ra _ _ _) (@LJA_can_rel_OrLinv1 V).
Definition LJA_rel_adm_OrLinv2 V := snd (crd_ra _ _ _) (@LJA_can_rel_OrLinv2 V).

Lemma LJA_can_rel_ImpL_And_inv {V} seq :
  derrec LJArules emptyT seq ->
  can_rel LJArules (@srs_ext_rel _ _) (@ImpL_And_inv V) seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact (@can_trf_ImpL_And_inv_lja V).  Qed.

Lemma LJA_can_rel_ImpL_Or_inv {V} seq :
  derrec LJArules emptyT seq ->
  can_rel LJArules (@srs_ext_rel _ _) (@ImpL_Or_inv V) seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact (@can_trf_ImpL_Or_inv_lja V).  Qed.

Lemma LJA_can_rel_ImpL_Var_inv2 {V} seq :
  derrec LJArules emptyT seq ->
  can_rel LJArules (@srs_ext_rel _ _) (@ImpL_Var_inv2 V) seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact (@can_trf_ImpL_Var_inv2_lja V).  Qed.

Lemma LJA_can_rel_ImpL_Imp_inv2 {V} seq :
  derrec LJArules emptyT seq ->
  can_rel LJArules (@srs_ext_rel _ _) (@ImpL_Imp_inv2 V) seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact (@can_trf_ImpL_Imp_inv2_lja V).  Qed.

(* not sure whether we will need remaining results for LJA in the form of 
  LJA_rel_adm ... or LJA_can_rel *)

(*
Lemma LJA_can_rel_ImpLinv2 {V} seq :
derrec LJrules emptyT seq ->
  can_rel LJrules (srs_ext_rel (Y:=PropF V)) ImpLinv2 seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact (@can_trf_ImpLinv2_lj V).  Qed.

Lemma LJA_rel_adm_ImpLinv2 {V} :
  rel_adm LJrules (srs_ext_rel (@ImpLinv2 V)).
Proof. apply crd_ra. apply LJA_can_rel_ImpLinv2. Qed.
*)

(** invertibility of right rules **)
Check rr_ext_rel ImpRinv.
Check fun W Y genRinv => (@rr_ext_rel W Y genRinv).

Lemma LJAil_lem_ljts {V} ps c Γ1 Γ2 G : @LJAilrules V ps c -> 
  LJTSrules (map (apfst (fmlsext Γ1 Γ2)) (map (Basics.flip pair G) ps))
    (Γ1 ++ c ++ Γ2, G).
Proof. intro il.  apply ncgen.  eapply il_tsnc.
eapply rmI_eq. apply il.  reflexivity.  reflexivity.  Qed.

Lemma LJsl_lem_ljts {V} ps c Γ1 Γ2 G : @LJslrules V ps c -> 
  LJTSrules (map (apfst (fmlsext Γ1 Γ2)) (map (Basics.flip pair G) ps))
    (Γ1 ++ c ++ Γ2, G).
Proof. intro il.  apply ncgen.  eapply lrls_tsnc.
eapply rmI_eq. apply il.  reflexivity.  reflexivity.  Qed.

Definition LJAil_lem_lja {V} ps c Γ1 Γ2 G ljpc :=
  ljts_sub_lja (@LJAil_lem_ljts V ps c Γ1 Γ2 G ljpc).
Definition LJAil_lem_ljt {V} ps c Γ1 Γ2 G ljpc :=
  ljts_sub_ljt (@LJAil_lem_ljts V ps c Γ1 Γ2 G ljpc).

Definition LJAil_derl_lem_ljts {V} ps c Γ1 Γ2 G ljpc :=
  in_derl _ _ _ (@LJAil_lem_ljts V ps c Γ1 Γ2 G ljpc).
Definition LJAil_derl_lem_lja {V} ps c Γ1 Γ2 G ljpc :=
  in_derl _ _ _ (@LJAil_lem_lja V ps c Γ1 Γ2 G ljpc).
Definition LJAil_derl_lem_ljt {V} ps c Γ1 Γ2 G ljpc :=
  in_derl _ _ _ (@LJAil_lem_ljt V ps c Γ1 Γ2 G ljpc).

Definition LJAil_adm_lem_ljts {V} ps c Γ1 Γ2 G ljpc :=
  in_adm _ _ _ (@LJAil_lem_ljts V ps c Γ1 Γ2 G ljpc).
Definition LJAil_adm_lem_lja {V} ps c Γ1 Γ2 G ljpc :=
  in_adm _ _ _ (@LJAil_lem_lja V ps c Γ1 Γ2 G ljpc).
Definition LJAil_adm_lem_ljt {V} ps c Γ1 Γ2 G ljpc :=
  in_adm _ _ _ (@LJAil_lem_ljt V ps c Γ1 Γ2 G ljpc).

Definition LJsl_lem_lja {V} ps c Γ1 Γ2 G ljpc :=
  ljts_sub_lja (@LJsl_lem_ljts V ps c Γ1 Γ2 G ljpc).
Definition LJsl_lem_ljt {V} ps c Γ1 Γ2 G ljpc :=
  ljts_sub_ljt (@LJsl_lem_ljts V ps c Γ1 Γ2 G ljpc).

Definition LJsl_derl_lem_lja {V} ps c Γ1 Γ2 G ljpc :=
  in_derl _ _ _ (@LJsl_lem_lja V ps c Γ1 Γ2 G ljpc).
Definition LJsl_derl_lem_ljt {V} ps c Γ1 Γ2 G ljpc :=
  in_derl _ _ _ (@LJsl_lem_ljt V ps c Γ1 Γ2 G ljpc).

Definition LJsl_adm_lem_lja {V} ps c Γ1 Γ2 G ljpc :=
  in_adm _ _ _ (@LJsl_lem_lja V ps c Γ1 Γ2 G ljpc).
Definition LJsl_adm_lem_ljt {V} ps c Γ1 Γ2 G ljpc :=
  in_adm _ _ _ (@LJsl_lem_ljt V ps c Γ1 Γ2 G ljpc).

(* TODO rename these to LJAil_adm_lem_lja, LJsl_adm_lem_lja *)
Definition LJAil_adm_lem {V} ps c Γ1 Γ2 G rpc :=
  in_adm _ _ _ (@LJAil_lem_lja V ps c Γ1 Γ2 G rpc).
Definition LJsl_adm_lem {V} ps c Γ1 Γ2 G rpc :=
  in_adm _ _ _ (@LJsl_lem_lja V ps c Γ1 Γ2 G rpc).

Ltac fcr2_tac H0 := apply fcr2 ; intro ; 
apply rT_step ; simpl ; unfold fmlsext ;  rewrite ?app_nil_r ;
aprre ; exact H0.

Ltac ljgltac thm H2 H0 := eexists ; split ;
  [ apply thm ; apply H2 | fcr2_tac H0 ].
Ltac ljailtac H2 H0 := eexists ; split ;
  [ apply LJAil_adm_lem ; apply H2 | fcr2_tac H0 ].
Ltac ljsltac H2 H0 := eexists ; split ;
  [ apply LJsl_adm_lem ; apply H2 | fcr2_tac H0 ].

Lemma f1cf W q qs f : f q -> {p : W & InT p (q :: qs) * f p}.
Proof. intro. eexists. exact (pair (InT_eq _ _) X). Qed.

Lemma f1crr W q qs R : {p : W & InT p (q :: qs) * clos_reflT R p q}.
Proof. apply f1cf. apply rT_refl. Qed.

Ltac drstac_tn th C0 X0 X2 := simpl ;  unfold fmlsext ;  apply dlCons ; [
assoc_single_mid' C0 ; apply (th _ _ _ [C0]) ;
apply (eq_rect _ _ X0) ; list_eq_assoc |
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

Ltac rinv_tac C := 
apply ForallT_singleI ; apply f1cf ;
apply rT_step ; simpl ; unfold fmlsext ; simpl ;
assoc_single_mid' C ; eapply (rr_ext_relI_eqp _ [C]) ;
[apply ImpRinv_I |  list_eq_assoc].

(* TODO - try for commonality between this and can_trf_ImpRinv_lja *)
Lemma can_trf_ImpRinv_ljt {V} ps c : @LJTrules V ps c ->
  can_trf_rules_rc (rr_ext_rel ImpRinv) (adm LJTrules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r as [? ? Y]. subst. clear r.
unfold can_trf_rules_rc. intros c' ser.
inversion ser. clear ser. destruct c0. simpl in H.
unfold fmlsext in H. inversion H. clear H. subst.
(* pose (LJTSnc_seL X). *)  inversion Y ; subst.
- pose (LJTSnc_seL X). inversion X.
-- (* LJAilrules *)
inversion X0. subst.
acacD'T2 ; subst.
apply sing_empty_app in s. sD ; subst.
+ simpl in X1.  assoc_mid H2.  ljgltac @LJAil_adm_lem_ljt X1 H0.
+ rewrite ?app_nil_r in X1.  assoc_mid H3.  ljgltac @LJAil_adm_lem_ljt X1 H0.
+ assoc_mid l.  ljgltac @LJAil_adm_lem_ljt X1 H0.
+ assoc_mid l.  ljgltac @LJAil_adm_lem_ljt X1 H0.

-- (* ImpL_Imp_rule *)
inversion X0. inversion H0. subst. clear X0 H0 s.
acacD'T2 ; subst.
+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_r.
++ admtac X1 X3.
+++ ljartac Imp_tnc' (Γ1 ++ [C0]) Γ2.
+++ drstac_tn insL_ljt C0 X0 X2.

+ list_eq_ncT. cD. subst.
eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_l.
++ admtac X1 X3.
+++ ljartac Imp_tnc' Γ1 (C0 :: Γ2).
+++ drstac_tn insL_ljt C0 X0 X2.

+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_l.
++ admtac X1 X3.
+++ ljartac Imp_tnc' Γ1 (H1 ++ C0 :: Φ2).
+++ drstac_tn insL_ljt C0 X0 X2.

+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_r.
++ admtac X1 X3.
+++ ljartac Imp_tnc' (Φ1 ++ [C0] ++ H3) Γ2.
+++ drstac_tn insL_ljt C0 X0 X2.

-- (* ImpRrule *)
inversion X0. inversion H0. subst.  inversion H4. subst. clear H4 H0 X0.
eexists. split. all: cycle 1.
apply ForallT_singleI.  eexists. split.  apply InT_eq.  apply rT_refl.
simpl in H3.  simpl. unfold fmlsext. 
apply admI. intro d.  apply dersrec_singleD in d.
apply (exchL_ljt d).  apply fst_relI.
exact (swap_ins _ _ _ _ [A] H3).
-- (* Idrule (Var - so n/a) *)
inversion X0.  inversion H0. subst.  inversion H4.
-- (* LJslrules *)
inversion X0. subst.
acacD'T2 ; subst.
apply sing_empty_app in s. sD ; subst.

+ simpl in X1.  assoc_mid H2.  ljgltac @LJsl_adm_lem_ljt X1 H0.
+ rewrite ?app_nil_r in X1.  assoc_mid H3.  ljgltac @LJsl_adm_lem_ljt X1 H0.
+ assoc_mid l.  ljgltac @LJsl_adm_lem_ljt X1 H0.
+ assoc_mid l.  ljgltac @LJsl_adm_lem_ljt X1 H0.
-- (* LJsrrules - different formulae *)
inversion H0.  inversion X0. subst. clear X0 H0.
inversion X1 ; inversion X0.

- (* ImpL_atom_rule *)
inversion X.  inversion H0.  destruct X0. subst. clear X H0 Y. simpl.
acacD'T2 ; subst.
-- rewrite ?app_nil_r.  eexists. split. apply in_adm.
apply (@fextI _ _ _ (Γ1 ++ [C]) Γ2).
eapply rmI_eqc.  apply atom_tnc'.
sfseq.
apply ForallT_singleI ; apply f1cf.
apply rT_step.  sfs.
eapply (rr_ext_relI_eq _ [C] Γ1 (B :: Var p0 :: Γ2)).
apply ImpRinv_I.  list_eq_assoc.  list_eq_assoc.

-- (* C between Imp (Var p0) B and Var p0 *)
eexists [ _ ]. split. all: cycle 1.
apply ForallT_singleI. apply f1cf. apply rT_step.
eapply (rr_ext_relI_eqp _ [C] _ []).
apply ImpRinv_I. simpl. reflexivity.
simpl. apply derl_sub_adm.  eapply derl_trans.
apply sw_ljt.  apply fst_relI.
eapply (swapped_I [] [C]). reflexivity. simpl. reflexivity.

apply derl_dersl_single. apply in_derl.
apply (@fextI _ _ _ (C :: Γ1) Γ2).
eapply rmI_eq. apply atom_tnc'.
sfs. reflexivity.
sfseq.

-- list_eq_ncT. cD. subst.
eexists. split. apply in_adm.
apply (@fextI _ _ _ Γ1 (C :: Γ2)).
eapply rmI_eqc.  apply atom_tnc'.
sfseq.
apply ForallT_singleI ; apply f1cf.
apply rT_step.  sfs.
eapply (rr_ext_relI_eq _ [C] (Γ1 ++ [B; Var p0]) Γ2).
apply ImpRinv_I.  list_eq_assoc.  list_eq_assoc.

-- eexists. split. apply in_adm.
apply (@fextI _ _ _ Γ1 (H1 ++ C :: Φ2)).
eapply rmI_eqc.  apply atom_tnc'.
sfseq.
apply ForallT_singleI ; apply f1cf.
apply rT_step.  sfs.
eapply (rr_ext_relI_eq _ [C] (Γ1 ++ B :: Var p0 :: H1) Φ2).
apply ImpRinv_I.  list_eq_assoc.  list_eq_assoc.

-- eexists. split. apply in_adm.
apply (@fextI _ _ _ (Φ1 ++ C :: H3) Γ2).
eapply rmI_eqc.  apply atom_tnc'.
sfseq.
apply ForallT_singleI ; apply f1cf.
apply rT_step.  sfs.
eapply (rr_ext_relI_eq _ [C] Φ1 (H3 ++ B :: Var p0 :: Γ2)).
apply ImpRinv_I.  list_eq_assoc.  list_eq_assoc.

- (* exch_rule *)
inversion X.  inversion H0.  destruct X0. subst. clear X H0 Y. simpl.
acacD'T2 ; subst. (* 6 subgoals *)

-- rewrite ?app_nil_r.  eexists. split. apply in_adm.
apply (@fextI _ _ _ (Γ1 ++ [C]) Γ2).
eapply rmI_eqc.  eapply exch_tnc.  apply rmI. apply exchI.
sfseq.  rinv_tac C.

-- eexists. split. apply in_adm.
apply (@fextI _ _ _ Γ1 Γ2).
eapply rmI_eqc.  eapply exch_tnc.  apply rmI. 
apply (exchI x y X0 (H5 ++ C :: H2)).
sfseq.  rinv_tac C.

-- rewrite ?app_nil_r.  eexists. split. apply in_adm.
apply (@fextI _ _ _ Γ1 Γ2).
eapply rmI_eqc.  eapply exch_tnc.  apply rmI.
apply (exchI x y X0 (Y0 ++ [C])).
sfseq.  rinv_tac C.

-- eexists. split. apply in_adm.
apply (@fextI _ _ _ Γ1 Γ2).
eapply rmI_eqc.  eapply exch_tnc.  apply rmI.
apply (exchI x y (H6 ++ C :: H1) Y0).
sfseq.  rinv_tac C.

-- eexists. split. apply in_adm.
apply (@fextI _ _ _ Γ1 (H1 ++ C :: Φ2)).
eapply rmI_eqc.  eapply exch_tnc.  apply rmI.
apply (exchI x y X0 Y0).
sfseq.  rinv_tac C.

-- eexists. split. apply in_adm.
apply (@fextI _ _ _ (Φ1 ++ C :: H3) Γ2).
eapply rmI_eqc.  eapply exch_tnc.  apply rmI.
apply (exchI x y X0 Y0).
sfseq.  rinv_tac C.

Qed.

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
+ simpl in X1.  assoc_mid H2.  ljailtac X1 H0.
+ rewrite ?app_nil_r in X1.  assoc_mid H3.  ljailtac X1 H0.
+ assoc_mid l.  ljailtac X1 H0.
+ assoc_mid l.  ljailtac X1 H0.

- (* ImpL_Imp_rule *)
inversion X0. inversion H0. subst. clear X0 H0 s.
acacD'T2 ; subst.
+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_r.
++ admtac X1 X3.
+++ ljartac Imp_anc' (Γ1 ++ [C0]) Γ2.
+++ drstac_tn insL_lja C0 X0 X2.

+ list_eq_ncT. cD. subst.
eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_l.
++ admtac X1 X3.
+++ ljartac Imp_anc' Γ1 (C0 :: Γ2).
+++ drstac_tn insL_lja C0 X0 X2.

+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_l.
++ admtac X1 X3.
+++ ljartac Imp_anc' Γ1 (H1 ++ C0 :: Φ2).
+++ drstac_tn insL_lja C0 X0 X2.

+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_r.
++ admtac X1 X3.
+++ ljartac Imp_anc' (Φ1 ++ [C0] ++ H3) Γ2.
+++ drstac_tn insL_lja C0 X0 X2.

- (* ImpLrule_p *)
inversion X0. inversion H0. subst. clear X0 H0 s.
acacD'T2 ; subst.
+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_r.
++ admtac X1 X3.
+++ ljartac ImpL_anc' (Γ1 ++ [C]) Γ2.
+++ drstac_tn insL_lja C X0 X2.

+ list_eq_ncT. cD. subst.
eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_l.
++ admtac X1 X3.
+++ ljartac ImpL_anc' Γ1 (C :: Γ2).
+++ drstac_tn insL_lja C X0 X2.

+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_l.
++ admtac X1 X3.
+++ ljartac ImpL_anc' Γ1 (H1 ++ C :: Φ2).
+++ drstac_tn insL_lja C X0 X2.

+ eexists [ _ ; _ ]. split. all: cycle 1. 
++ fictac list_assoc_r.
++ admtac X1 X3.
+++ ljartac ImpL_anc' (Φ1 ++ [C] ++ H3) Γ2.
+++ drstac_tn insL_lja C X0 X2.

- (* ImpRrule *)
inversion X0. inversion H0. subst.  inversion H1. subst. clear H1 H0 X0.
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
inversion X1 ; inversion X0.
Qed.

(* we don't have a theorem of invertibility of ImpR for LJ
  because normally it is needed only for contraction on the right *)
Lemma LJA_rel_adm_ImpR V : rel_adm LJArules (rr_ext_rel (@ImpRinv V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_adm.  exact can_trf_ImpRinv_lja.  Qed.

Lemma LJT_rel_adm_ImpR V : rel_adm LJTrules (rr_ext_rel (@ImpRinv V)).
Proof. apply crd_ra. unfold can_rel.
apply der_trf_rc_adm.  exact can_trf_ImpRinv_ljt.  Qed.

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
eapply il_anc. apply rmI. exact X2. reflexivity.
apply fcr2. intro. apply rT_step. simpl.
apply ant_relI. exact X0.
- (* ImpL_Imp_rule *)
inversion X1. subst. clear X1.
eexists [_ ; _]. split. all: cycle 1.
apply ForallT_cons. eexists. split. apply InT_eq. apply rT_refl.
apply ForallT_singleI.
eexists. split. apply InT_2nd. apply rT_step.
simpl. apply ant_relI. apply X0.
apply in_adm. simpl.
eapply fextI. eapply rmI_eq. apply Imp_anc'.
reflexivity.  reflexivity.
- (* ImpLrule_p *)
inversion X1. subst. clear X1.
eexists [_ ; _]. split. all: cycle 1.
apply ForallT_cons. eexists. split. apply InT_eq. apply rT_refl.
apply ForallT_singleI.
eexists. split. apply InT_2nd. apply rT_step.
simpl. apply ant_relI. apply X0.
apply in_adm. simpl.
eapply fextI. eapply rmI_eq. apply ImpL_anc'.
reflexivity.  reflexivity.
- (* ImpRrule *)
inversion X1. subst. destruct (not_Imp _ _ _ X0).
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
+ inversion X. simpl. subst. inversion X0 ; subst ; inversion X1.
+ inversion X.  + inversion X.  + inversion X.  + inversion X.
+ inversion X. inversion X0 ; subst ; inversion X1.
+ inversion X. inversion X0 ; subst ; inversion X1 ; solve_InT.
- intros * ari. inversion ari.
- intros * ari. inversion ari.
Qed.

About can_trf_AndRinv1_lja. 

Lemma can_trf_AndRinv2_lja {V} ps c : @LJArules V ps c ->
  can_trf_rules_rc (ant_rel AndRinv2) (adm LJArules) ps c.
Proof. apply can_trf_genRinv_lja.
- intros * auw ljar.  destruct auw.
inversion ljar ; subst.
+ inversion X. simpl. subst. inversion X0 ; subst ; inversion X1.
+ inversion X.  + inversion X.  + inversion X.  + inversion X.
+ inversion X. inversion X0 ; subst ; inversion X1.
+ inversion X. inversion X0 ; subst ; inversion X1 ; solve_InT.
- intros * ari. inversion ari.
- intros * ari. inversion ari.
Qed.

(* not inversion of any rule, but similar proof *) 
Lemma can_trf_BotRinv_lja {V} ps c : @LJArules V ps c ->
  can_trf_rules_rc (ant_rel BotRinv) (adm LJArules) ps c.
Proof. apply can_trf_genRinv_lja.
- intros * auw ljar.  destruct auw.
inversion ljar ; subst.
+ inversion X. simpl. subst. inversion X0 ; subst ; inversion X1.
+ inversion X.  + inversion X.  + inversion X.  + inversion X.
+ inversion X. inversion X0 ; subst ; inversion X1.
+ inversion X. inversion X0 ; subst ; inversion X1 ; solve_InT.
- intros * ari. inversion ari.
- intros * ari. inversion ari.
Qed.

(* following is copies of lines 518 to 605 *)
(** admissibility of inversion for LJT **)
(* doesn't work for LJT as counterpart of LJAnc_seL doesn't hold *)
Lemma can_trf_AndLinv_ljts {V} ps c: @LJTSrules V ps c ->
  can_trf_rules_rc (srs_ext_rel AndLinv) (derl LJTSrules) ps c.
Proof. apply can_trf_genLinv_gen.  apply LJTSnc_seL.
intros * auv.  destruct auv.  
intro ljts. exact (LJAAE (sing_anc ljts)).  Qed.

Lemma can_trf_OrLinv1_ljts {V} ps c: @LJTSrules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv1) (derl LJTSrules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJTSnc_seL.
intros * auv.  destruct auv.  intro rocd.
pose (LJAOE (sing_anc rocd)). clearbody e. subst. solve_InT.  Qed.

Lemma can_trf_OrLinv2_ljts {V} ps c: @LJTSrules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv2) (derl LJTSrules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJTSnc_seL.
intros * auv.  destruct auv.  intro rocd.
pose (LJAOE (sing_anc rocd)). clearbody e. subst. solve_InT.  Qed.

Lemma can_trf_ImpL_Or_inv_ljts {V} ps c: @LJTSrules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Or_inv) (derl LJTSrules) ps c.
Proof. apply can_trf_genLinv_gen.  apply LJTSnc_seL.
intros * auv.  destruct auv.  intro ljts. exact (LJAIOE (sing_anc ljts)). Qed.

Lemma can_trf_ImpL_And_inv_ljts {V} ps c: @LJTSrules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_And_inv) (derl LJTSrules) ps c.
Proof. apply can_trf_genLinv_gen.  apply LJTSnc_seL.
intros * auv.  destruct auv.  intro ljts. exact (LJAIAE (sing_anc ljts)). Qed.

Lemma can_trf_ImpL_Imp_inv2_ljts {V} ps c: @LJTSrules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Imp_inv2) (derl LJTSrules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJTSnc_seL.
intros * auv.  destruct auv. intro rocd.  
pose (LJAIIE (sing_anc rocd)). clearbody e. subst. solve_InT.  Qed.

Lemma can_trf_ImpL_Var_inv2_ljts {V} ps c: @LJTSrules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Var_inv2) (derl LJTSrules) ps c.
Proof. apply can_trf_genLinv_geni.  apply LJTSnc_seL.
intros * auv.  destruct auv. intro rocd.  
pose (LJAIpE (sing_anc rocd)). clearbody e. subst. solve_InT.  Qed.

Definition ctrc_d_f_mono V R := @can_trf_rules_rc_mono _ R _ _ 
  (derl_mono (fer_mono (rsubI _ _ (@sing_tnc V)))).
  
Lemma can_trf_AndLinv_ljt {V} ps c: @LJTrules V ps c ->
  can_trf_rules_rc (srs_ext_rel AndLinv) (derl LJTrules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r. destruct X.
(* note, now, ps and c are the skeleton of the final rule *)
- (* LJTSncrules *)
eapply ctrc_d_f_mono.
apply can_trf_AndLinv_ljts.
eapply fextI.  apply rmI.  exact l.
- (* ImpL_atom_rule *)
unfold AndLinv. destruct c. 
apply can_trf_genLinv_lem.
inversion r. subst. clear r. destruct X.
intros * auw. destruct auw.
intro ia.  inversion ia. inversion H0.
inversion H0. inversion H3.  inversion H3.
exact (atom_tnc r).
- (* exch_rule *) unfold AndLinv.
eapply can_trf_genLinv_exch. apply rsubI. apply exch_tnc. exact r.  Qed.

Lemma can_trf_OrLinv1_ljt {V} ps c: @LJTrules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv1) (derl LJTrules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r. destruct X.
- (* LJTSncrules *)
eapply ctrc_d_f_mono.
apply can_trf_OrLinv1_ljts.
eapply fextI.  apply rmI.  exact l.
- (* ImpL_atom_rule *)
unfold OrLinv1. destruct c. 
apply can_trf_genLinv_lem.
inversion r. subst. clear r. destruct X.
intros * auw. destruct auw.
intro ia.  inversion ia. inversion H0.
inversion H0. inversion H3.  inversion H3.
exact (atom_tnc r).
- (* exch_rule *) unfold OrLinv1.
eapply can_trf_genLinv_exch. apply rsubI. apply exch_tnc. exact r.  Qed.

Lemma can_trf_OrLinv2_ljt {V} ps c: @LJTrules V ps c ->
  can_trf_rules_rc (srs_ext_rel OrLinv2) (derl LJTrules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r. destruct X.
- (* LJTSncrules *)
eapply ctrc_d_f_mono.
apply can_trf_OrLinv2_ljts.
eapply fextI.  apply rmI.  exact l.
- (* ImpL_atom_rule *)
unfold OrLinv2. destruct c. 
apply can_trf_genLinv_lem.
inversion r. subst. clear r. destruct X.
intros * auw. destruct auw.
intro ia.  inversion ia. inversion H0.
inversion H0. inversion H3.  inversion H3.
exact (atom_tnc r).
- (* exch_rule *) unfold OrLinv2.
eapply can_trf_genLinv_exch. apply rsubI. apply exch_tnc. exact r.  Qed.

Lemma can_trf_ImpL_Or_inv_ljt {V} ps c: @LJTrules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Or_inv) (derl LJTrules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r. destruct X.
- (* LJTSncrules *)
eapply ctrc_d_f_mono.
apply can_trf_ImpL_Or_inv_ljts.
eapply fextI.  apply rmI.  exact l.
- (* ImpL_atom_rule *)
unfold ImpL_Or_inv. destruct c. 
apply can_trf_genLinv_lem.
inversion r. subst. clear r. destruct X.
intros * auw. destruct auw.
intro ia.  inversion ia. inversion H0.
inversion H0. inversion H3.  inversion H3.
exact (atom_tnc r).
- (* exch_rule *) unfold ImpL_Or_inv.
eapply can_trf_genLinv_exch. apply rsubI. apply exch_tnc. exact r.  Qed.

Lemma can_trf_ImpL_And_inv_ljt {V} ps c: @LJTrules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_And_inv) (derl LJTrules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r. destruct X.
- (* LJTSncrules *)
eapply ctrc_d_f_mono.
apply can_trf_ImpL_And_inv_ljts.
eapply fextI.  apply rmI.  exact l.
- (* ImpL_atom_rule *)
unfold ImpL_And_inv. destruct c. 
apply can_trf_genLinv_lem.
inversion r. subst. clear r. destruct X.
intros * auw. destruct auw.
intro ia.  inversion ia. inversion H0.
inversion H0. inversion H3.  inversion H3.
exact (atom_tnc r).
- (* exch_rule *) unfold ImpL_And_inv.
eapply can_trf_genLinv_exch. apply rsubI. apply exch_tnc. exact r.  Qed.

Lemma can_trf_ImpL_Imp_inv2_ljt {V} ps c: @LJTrules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Imp_inv2) (derl LJTrules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r. destruct X.
- (* LJTSncrules *)
eapply ctrc_d_f_mono.
apply can_trf_ImpL_Imp_inv2_ljts.
eapply fextI.  apply rmI.  exact l.
- (* ImpL_atom_rule *)
unfold ImpL_Imp_inv2. destruct c. 
apply can_trf_genLinv_lem.
inversion r. subst. clear r. destruct X.
intros * auw. destruct auw.
intro ia.  inversion ia. inversion H0.
inversion H0. inversion H3.  inversion H3.
exact (atom_tnc r).
- (* exch_rule *) unfold ImpL_Imp_inv2.
eapply can_trf_genLinv_exch. apply rsubI. apply exch_tnc. exact r.  Qed.

Lemma can_trf_ImpL_Var_inv2_ljt {V} ps c: @LJTrules V ps c ->
  can_trf_rules_rc (srs_ext_rel ImpL_Var_inv2) (derl LJTrules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r. destruct X.
- (* LJTSncrules *)
eapply ctrc_d_f_mono.
apply can_trf_ImpL_Var_inv2_ljts.
eapply fextI.  apply rmI.  exact l.
- (* ImpL_atom_rule *)
unfold ImpL_Var_inv2.
inversion r. subst. clear r. destruct X.
sfs.  unfold can_trf_rules_rc. intros c' ser.
inversion ser. clear ser. subst. 
destruct H2. simpl in H. destruct i.
(* notge - the rule involves Var p, B, inversion involves Var p0, B0 *)
acacD'T2 ; subst.

+ eexists. split. apply asmI.
apply ForallT_singleI ; apply f1cf.
rewrite app_nil_r.  apply rT_refl.

+ inversion H4.
+ eexists. split. apply in_derl.
apply (@fextI _ _ _ Γ1 (H3 ++ B0 :: Φ2)).
eapply rmI_eqc. apply atom_tnc'. sfseq.
apply ForallT_singleI ; apply f1cf.
apply rT_step.  sfs.
eapply (srs_ext_relI_eq _ [Imp (Var p0) B0] [B0] (Γ1 ++ B :: Var p :: H3) Φ2).
apply ImpL_Var_inv2_I.  list_eq_assoc.  list_eq_assoc.

+ eexists. split. apply asmI.
apply ForallT_singleI ; apply f1cf.
rewrite app_nil_r.  apply rT_refl.

+ eexists. split. apply in_derl.
apply (@fextI _ _ _ (Φ1 ++ [B0] ++ H1) Γ2).
eapply rmI_eqc. apply atom_tnc'. sfseq.
apply ForallT_singleI ; apply f1cf.
apply rT_step.  sfs.
eapply (srs_ext_relI_eq _ [Imp (Var p0) B0] [B0] Φ1 (H1 ++ B :: Var p :: Γ2)).
apply ImpL_Var_inv2_I.  list_eq_assoc.  list_eq_assoc.

- inversion r. subst. clear r. 
eapply can_trf_genLinv_exch. intro. apply exch_tnc.
apply rmI. exact X. Qed.

(* now inversion results in terms of can_rel *)
Lemma LJT_can_rel_AndLinv {V} seq :
  derrec LJTrules emptyT seq ->
  can_rel LJTrules (@srs_ext_rel _ _) (@AndLinv V) seq.
Proof. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_AndLinv_ljt V).  Qed.

Lemma LJT_can_rel_OrLinv1 {V} seq :
  derrec LJTrules emptyT seq ->
  can_rel LJTrules (@srs_ext_rel _ _) (@OrLinv1 V) seq.
Proof. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_OrLinv1_ljt V).  Qed.

Lemma LJT_can_rel_OrLinv2 {V} seq :
  derrec LJTrules emptyT seq ->
  can_rel LJTrules (@srs_ext_rel _ _) (@OrLinv2 V) seq.
Proof. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_OrLinv2_ljt V).  Qed.

Definition LJT_rel_adm_AndLinv V := snd (crd_ra _ _ _) (@LJT_can_rel_AndLinv V).
Definition LJT_rel_adm_OrLinv1 V := snd (crd_ra _ _ _) (@LJT_can_rel_OrLinv1 V).
Definition LJT_rel_adm_OrLinv2 V := snd (crd_ra _ _ _) (@LJT_can_rel_OrLinv2 V).

Lemma LJT_can_rel_ImpL_And_inv {V} seq :
  derrec LJTrules emptyT seq ->
  can_rel LJTrules (@srs_ext_rel _ _) (@ImpL_And_inv V) seq.
Proof. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_ImpL_And_inv_ljt V).  Qed.

Lemma LJT_can_rel_ImpL_Or_inv {V} seq :
  derrec LJTrules emptyT seq ->
  can_rel LJTrules (@srs_ext_rel _ _) (@ImpL_Or_inv V) seq.
Proof. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_ImpL_Or_inv_ljt V).  Qed.

Lemma LJT_can_rel_ImpL_Imp_inv2 {V} seq :
  derrec LJTrules emptyT seq ->
  can_rel LJTrules (@srs_ext_rel _ _) (@ImpL_Imp_inv2 V) seq.
Proof. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_ImpL_Imp_inv2_ljt V).  Qed.

Lemma LJT_can_rel_ImpL_Var_inv2 {V} seq :
  derrec LJTrules emptyT seq ->
  can_rel LJTrules (@srs_ext_rel _ _) (@ImpL_Var_inv2 V) seq.
Proof. unfold can_rel.
apply der_trf_rc_derl.  exact (@can_trf_ImpL_Var_inv2_ljt V).  Qed.

(* invertibility of atom rule for LJT - different as two principal formulae *)
(* TODO these two to ljt *)
Lemma ljts_niv V p B G ps tl :
  @LJTSncrules V ps (Imp (Var p) B :: tl, G) -> False.
Proof. intro. inversion X ; inversion X0 ; inversion X1 ; inversion X2. Qed.

Lemma ljts_nv V p G ps tl :
  @LJTSncrules V ps (Var p :: tl, G) -> (G = Var p) * (tl = []) * (ps = []).
Proof. intro. inversion X ; inversion X0.
inversion X1 ; inversion X2.  tauto.  inversion X1 ; inversion X2.  Qed.

(* notes
Lemma can_trf_ImpL_Var_inv2_ljt {V} ps c: done
Lemma LJT_can_rel_ImpL_Var_inv2 {V} seq :
*)
