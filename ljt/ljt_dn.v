
(* LJA logic, using lists of formulae *)
(* lemmas in Roy Dyckhoff and Sara Negri,
Admissibility of Structural Rules for Contraction-Free Systems of
Intuitionistic Logic, JSL 65 (2000), 1499-1518 *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.

Test Universe Polymorphism. (* NB Set this causes errors *)
Test Printing Universes.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT dd_fc.
Require Import List_lemmasT swappedT.
Require Import gen_tacs.
Require Import gen_seq gstep gentree rtcT.
Require Import ljt ljt_inv.
Require Import Coq.Program.Basics.

(* a definition of subformula corresponding to the weight defined by D&N *)
Inductive dnsubfml {V} : PropF V -> PropF V -> Type :=
  | dnsub_Imp_ImpL : forall B C D, dnsubfml (Imp D B) (Imp (Imp C D) B)
  | dnsub_Imp_AndL : forall B C D, dnsubfml (Imp C (Imp D B)) (Imp (And C D) B)
  | dnsub_Imp_OrL2 : forall B C D, dnsubfml (Imp D B) (Imp (Or C D) B)
  | dnsub_Imp_OrL1 : forall B C D, dnsubfml (Imp C B) (Imp (Or C D) B)
  | dnsub_ImpL : forall C D, dnsubfml C (Imp C D)
  | dnsub_ImpR : forall C D, dnsubfml D (Imp C D)
  | dnsub_AndL : forall C D, dnsubfml C (And C D)
  | dnsub_AndR : forall C D, dnsubfml D (And C D)
  | dnsub_OrL : forall C D, dnsubfml C (Or C D)
  | dnsub_OrR : forall C D, dnsubfml D (Or C D).

(*
Lemma AccT_dnsubfml {V} (A : PropF V) : AccT dnsubfml A.
Proof. induction A ; apply AccT_intro ; intros A' isf ;
  inversion isf ; subst ; assumption. Qed.
  *)

Axiom AccT_dnsubfml : forall V (A : PropF V), AccT dnsubfml A.

(* Lemma 3.2(1) of Dyckhoff & Negri JSL 2000 *)
Lemma LJA_der_id {V} :
  forall (A : PropF V) (a : AccT dnsubfml A), 
  forall G, derrec LJArules emptyT (A :: G, A).
Proof. 
epose (AccT_rect (fun A _ => 
  (forall G, derrec LJArules emptyT (A :: G, A)))).
apply d. clear d.  intros A adn IH G.  destruct A.
- eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eqc. eapply Id_anc. eapply Idrule_I.  
reflexivity. apply dlNil.
- eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eqc. eapply lrls_anc. apply rmI.  apply Bot_sl. apply Botrule_I.
reflexivity. apply dlNil.
- (* Imp *)
eapply derI. eapply (@fextI _ _ _ [_] G).
eapply rmI_eqc. apply ImpR_anc'. reflexivity.
apply dersrec_singleI.  destruct A1.
+ eapply derI. eapply (@fextI _ _ _ [] (Var v :: G)).
eapply rmI_eqc. apply ImpL_anc'. reflexivity. 
apply dlCons.
eapply derI. eapply (@fextI _ _ _ [_] G).
eapply rmI_eqc. apply Id_anc'. reflexivity. apply dlNil.
apply dersrec_singleI.
apply IH.  apply dnsub_ImpR.
+ eapply derI. eapply (@fextI _ _ _ [_] G).
eapply rmI_eqc. apply lrls_anc'. apply Bot_sl. apply Botrule_I.  reflexivity.
apply dlNil.
+ eapply derI. eapply (@fextI _ _ _ [] (_ :: G)).
eapply rmI_eqc. apply Imp_anc'. reflexivity.
apply dlCons.  (* now invert ImpR rule *)
pose (LJA_rel_adm_ImpR V).  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r).  simpl. unfold fmlsext. simpl.
eapply (rr_ext_relI_eqc _ _ _ [_] (_ :: G)).
apply ImpRinv_I. reflexivity.
specialize (IH _ (dnsub_ImpL _ _) (Imp A1_2 A2 :: G)). 
apply (exchL_lja IH).  apply fst_relI.  apply swapped_cc.
apply dersrec_singleI.
apply (IH _ (dnsub_ImpR _ _)).

+ eapply derI. eapply (@fextI _ _ _ [_] G).
eapply rmI_eqc. apply lrls_anc'. apply AndL_sl. apply AndLrule_I.  reflexivity.
apply dersrec_singleI.
eapply derI. eapply (@fextI _ _ _ [] _).
eapply rmI_eqc. apply il_anc'.
apply And_ail. apply ImpL_And_rule_I.  reflexivity.
apply dersrec_singleI.  simpl.
(* now use invertibility of ImpR twice *)
pose (LJA_rel_adm_ImpR V).  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r).  unfold fmlsext. simpl.
eapply (rr_ext_relI_eqc _ _ _ [_ ; _] G).
apply ImpRinv_I. reflexivity. clear r.
pose (LJA_rel_adm_ImpR V).  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r).  
eapply (rr_ext_relI_eqc _ _ _ [_] G).
apply ImpRinv_I. reflexivity.
apply (IH _ (dnsub_Imp_AndL _ _ _)).

+ eapply derI. eapply (@fextI _ _ _ [] _).
eapply rmI_eqc. apply il_anc'.
apply Or_ail. apply ImpL_Or_rule_I.  reflexivity.
apply dersrec_singleI.  simpl.
eapply derI. eapply (@fextI _ _ _ [_ ; _] _).
eapply rmI_eqc. apply lrls_anc'. apply OrL_sl. apply OrLrule_I.  reflexivity.
simpl. unfold fmlsext. simpl. apply dlCons.
(* now invert ImpR rule *)
pose (LJA_rel_adm_ImpR V).  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r).
eapply (rr_ext_relI_eqc _ _ _ [_ ; _] G).
apply ImpRinv_I. reflexivity.
apply (IH _ (dnsub_Imp_OrL1 _ _ _)).
apply dersrec_singleI.  (* now invert ImpR rule *)
pose (LJA_rel_adm_ImpR V).  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r).
eapply (rr_ext_relI_eqc _ _ _ [_ ; _] G).
apply ImpRinv_I. reflexivity.
(* now need to use exchange *)
specialize (IH _ (dnsub_Imp_OrL2 _ _ _) (Imp A1_1 A2 :: G)).
apply (exchL_lja IH).  apply fst_relI.  apply swapped_cc.

- eapply derI. eapply (@fextI _ _ _ [] (And A1 A2 :: G)).
eapply rmI_eqc. apply rrls_anc. apply rmI. apply AndR_sr.  apply AndRrule_I.
reflexivity.  apply dlCons.
-- eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eqc. eapply lrls_anc. apply rmI. apply AndL_sl.  apply AndLrule_I.
reflexivity.  apply dersrec_singleI.
apply IH. apply dnsub_AndL. 
-- apply dersrec_singleI.
eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eqc. eapply lrls_anc. apply rmI. apply AndL_sl.  apply AndLrule_I.
reflexivity.  apply dersrec_singleI.
(* need to use exchange *)
simpl. unfold fmlsext. simpl.
specialize (IH _ (dnsub_AndR _ _) (A1 :: G)). 
apply (exchL_lja IH). apply fst_relI. apply swapped_cc.
- eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eqc. eapply lrls_anc. apply rmI. apply OrL_sl.  apply OrLrule_I.
reflexivity.  apply dlCons.
-- eapply derI. eapply (@fextI _ _ _ [A1] G).
eapply rmI_eqc. apply rrls_anc. apply rmI. apply OrR1_sr.  apply OrR1rule_I.
reflexivity.  apply dersrec_singleI.
apply (IH _ (dnsub_OrL _ _)).
-- apply dersrec_singleI.
eapply derI. eapply (@fextI _ _ _ [A2] G).
eapply rmI_eqc. apply rrls_anc. apply rmI. apply OrR2_sr.  apply OrR2rule_I.
reflexivity.  apply dersrec_singleI.
apply (IH _ (dnsub_OrR _ _)).
Qed.

Print Implicit LJA_der_id.

(*
don't do this - wrong, follow proof in paper, just do Lemma 3.2 (1) first
Lemma LJA_der_id_mp {V} :
  forall (A : PropF V) (a : AccT dnsubfml A), 
  (forall G, derrec LJArules emptyT (A :: G, A)) *
  (forall B H, derrec LJArules emptyT (A :: Imp A B :: H, B)).
*)

(* Lemma 3.2(2) of Dyckhoff & Negri JSL 2000 *)
Lemma LJA_der_mp {V} (A B : PropF V) H :
  derrec LJArules emptyT (A :: Imp A B :: H, B).
Proof. 
pose (LJA_rel_adm_ImpR V).  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r). 
eapply (rr_ext_relI_eqc _ _ _ [] _).
apply ImpRinv_I. reflexivity. clear r.
apply LJA_der_id. apply AccT_dnsubfml. Qed.

(* Lemma 4.1 of Dyckhoff & Negri JSL 2000 *)
(* relevant property of sequent to be proved by induction *)
Definition l41prop {V} (D : PropF V) seq := 
  forall G1 G2, seq = (G1 ++ G2, D) -> 
  forall B E, derrec LJArules emptyT (fmlsext G1 G2 [B], E) ->
  derrec LJArules emptyT (apfst (fmlsext G1 G2) ([Imp D B], E)).

Lemma LJA_inv_sl V G1 G2 E ps c :
  (@LJslrules V) ps c ->
  derrec LJArules emptyT (G1 ++ c ++ G2, E) -> 
  dersrec LJArules emptyT (map (apfst (fmlsext G1 G2)) 
  (map (flip pair E) ps)).
Proof. intros ljpc dce.  destruct ljpc.
- destruct a.
apply LJA_can_rel_AndLinv in dce.
unfold can_rel in dce.
apply dersrec_singleI.
apply dce.  simpl.  unfold fmlsext.
eapply srs_ext_relI_eq.  apply fslr_I.
apply AndLinvs_I.  reflexivity.  reflexivity.
- destruct o.
apply dlCons.
+ apply LJA_can_rel_OrLinv1 in dce.
unfold can_rel in dce.
apply dce.  simpl.  unfold fmlsext.
eapply srs_ext_relI_eq.  apply fslr_I.
apply OrLinv1s_I.  reflexivity.  reflexivity.
+ apply dersrec_singleI.
apply LJA_can_rel_OrLinv2 in dce.
unfold can_rel in dce.
apply dce.  simpl.  unfold fmlsext.
eapply srs_ext_relI_eq.  apply fslr_I.
apply OrLinv2s_I.  reflexivity.  reflexivity.
- (* Botrule *)
destruct b. apply dlNil. Qed.

Lemma LJA_inv_ail V G1 G2 E ps c :
  (@LJAilrules V) ps c ->
  derrec LJArules emptyT (G1 ++ c ++ G2, E) -> 
  dersrec LJArules emptyT (map (apfst (fmlsext G1 G2)) 
  (map (flip pair E) ps)).
Proof. intros ljpc dce.  destruct ljpc ; destruct i.
- apply LJA_can_rel_ImpL_And_inv in dce.
unfold can_rel in dce.
apply dersrec_singleI.
apply dce.  simpl.  unfold fmlsext.
eapply srs_ext_relI_eq.  apply fslr_I.
apply ImpL_And_invs_I.  reflexivity.  reflexivity.
- apply LJA_can_rel_ImpL_Or_inv in dce.
unfold can_rel in dce.
apply dersrec_singleI.
apply dce.  simpl.  unfold fmlsext.
eapply srs_ext_relI_eq.  apply fslr_I.
apply ImpL_Or_invs_I.  reflexivity.  reflexivity. Qed.

(* not sure if we need this *)
Lemma LJAil_psne V ps c : (@LJAilrules V) ps c ->
  sigT (fun p => sigT (fun pt => ps = p :: pt)).
Proof. intro ljpc. 
destruct ljpc ; destruct i ; eexists ; eexists ; reflexivity. Qed.

Lemma LJAil_sing V ps c : (@LJAilrules V) ps c -> sigT (fun c' => c = [c']).
Proof. intro ljpc.  destruct ljpc ; destruct i ; eexists ; reflexivity. Qed.

Lemma LJAil_sing_empty V ps c : (@LJAilrules V) ps c -> sing_empty c.
Proof. intro ljpc.  destruct ljpc ; destruct i ; apply se_single. Qed.

Lemma LJsl_sing_empty V ps c : (@LJslrules V) ps c -> sing_empty c.
Proof. intro ljpc.  destruct ljpc. 
destruct a. apply se_single. 
destruct o. apply se_single. 
destruct b. apply se_single.  Qed.

Lemma pair_eqD U W a b c d : (a : U, b : W) = (c, d) -> (a = c) * (b = d).
Proof. intro H. inversion H. tauto. Qed.

Ltac appe := match goal with
    | [ H : _ = _ |- _ ] => apply pair_eqD in H ; destruct H end.

(* apply rule in desired conclusion *)

Ltac inv_gl_tac gl_anc LJA_inv_gl c0 H fp dbe cin1 := 
simpl ;  unfold fmlsext ;  assoc_mid c0 ;
eapply derI ; [ eapply fextI ;  eapply rmI_eqc ; [
eapply gl_anc ;  apply rmI ;  apply H | reflexivity ] | ] ;
apply dersrecI_forall ;  intros c cin ;
apply InT_mapE in cin ; cD ; rename_last cin1 ;
apply InT_mapE in cin1 ; cD ;
(* invert rule in dbe *)
revert dbe ; unfold fmlsext ; assoc_mid c0 ; intro dbe ;
pose (LJA_inv_gl _ _ _ _ _ _ H dbe) as d ;
eapply dersrecD_forall in d ; [ |
apply InT_map ;  apply InT_map ; eassumption ] ;
eapply ForallTD_forall in fp ; [ |
apply InT_map ;  apply InT_map ; eassumption ] ;
unfold l41prop in fp ;
appe ; appe ; subst ;
unfold fmlsext ;  assoc_single_mid ;
simpl in fp ;  unfold fmlsext in fp ;
apply (snd fp) ; [ list_eq_assoc |
simpl in d ;  unfold fmlsext in d ;
apply (eq_rect _ _ d) ; list_eq_assoc ].

Lemma gs_LJA_ImpL_Ail V (D : PropF V) ps c Γ1 Γ2 G 
  (r : rlsmap (flip pair G) LJAilrules ps c) :
  gen_step l41prop D isubfml (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad.
unfold l41prop. intros * ceq * dbe.
inversion r. subst. clear r. 
rewrite ceq in dc.
simpl in ceq. unfold fmlsext in ceq.
inversion ceq. subst. clear ceq.
acacD'T2 ; subst.

- inv_gl_tac (@il_anc) LJA_inv_ail c0 H fp dbe cin1.

- pose (LJAil_sing_empty H). apply sing_empty_app in s.  sD ; subst.
+ simpl in H.  rewrite ?app_nil_r.
rewrite ?app_nil_r in dbe.  rewrite ?app_nil_r in dc.
inv_gl_tac (@il_anc) LJA_inv_ail H2 H fp dbe cin1.
+ rewrite ?app_nil_r in H.  simpl in dc.  simpl in dbe.
inv_gl_tac (@il_anc) LJA_inv_ail H1 H fp dbe cin1.

- inv_gl_tac (@il_anc) LJA_inv_ail c0 H fp dbe cin1.
Qed.

Check gs_LJA_ImpL_Ail.

Lemma gs_LJA_ImpL_sl V (D : PropF V) ps c Γ1 Γ2 G 
  (r : rlsmap (flip pair G) LJslrules ps c) :
  gen_step l41prop D isubfml (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad.
unfold l41prop. intros * ceq * dbe.
inversion r. subst. clear r. 
rewrite ceq in dc.
simpl in ceq. unfold fmlsext in ceq.
inversion ceq. subst. clear ceq.
acacD'T2 ; subst.

- inv_gl_tac (@lrls_anc) LJA_inv_sl c0 X fp dbe cin1.

- pose (LJsl_sing_empty X). apply sing_empty_app in s.  sD ; subst.
+ simpl in X.  rewrite ?app_nil_r.
rewrite ?app_nil_r in dbe.  rewrite ?app_nil_r in dc.
inv_gl_tac (@lrls_anc) LJA_inv_sl H2 X fp dbe cin1.
+ rewrite ?app_nil_r in X.  simpl in dc.  simpl in dbe.
inv_gl_tac (@lrls_anc) LJA_inv_sl H0 X fp dbe cin1.

- inv_gl_tac (@lrls_anc) LJA_inv_sl c0 X fp dbe cin1.
Qed.

Check gs_LJA_ImpL_sl.

Ltac gs_Imp_p_tac V c p A B D E X X0 X1 dbe L1 L2 L3 L4 L5 L6 L7 L8 :=
erequire c ; require c ; [
(* inversion of ImpLrule_p (2nd premise) in dbe *)
eapply (srs_ext_relI_eqp _ [Imp (Var p) A] [A] L1 L2) ; [
split ; apply ImpL_Var_inv2s_I |
unfold fmlsext ; list_eq_assoc ] | ] ; 
(* apply IH to 2nd premise of ... |- D *)
clear dbe ; unfold l41prop in X0 ; specialize (X0 L3 L4) ;
require X0 ; [ list_eq_assoc | ] ;
specialize (X0 B E) ;
require X0 ; [ unfold fmlsext ; apply (eq_rect _ _ c) ; list_eq_assoc | ] ;
(* weaken Imp D B into X *)
clear X1 c ; simpl in X0 ; unfold fmlsext in X0 ;
pose (@insL_lja V L5 L6 [Imp D B] (Var p)) as d ;
require d ; [ apply (eq_rect _ _ X) ; list_eq_assoc | ] ;
clear X ; simpl ; unfold fmlsext ;
(* now apply ImpLrule_p *)
eapply derI ; [ eapply (@fextI _ _ _ L7 L8) ;
eapply rmI_eqc ; [ apply ImpL_anc' |
simpl ; unfold fmlsext ; list_eq_assoc ] |
apply dlCons ; [
  simpl ; unfold fmlsext ; apply (eq_rect _ _ d) ; list_eq_assoc |
apply dersrec_singleI ;
simpl ; unfold fmlsext ; apply (eq_rect _ _ X0) ; list_eq_assoc ] ].

Lemma gs_LJA_ImpL_Imp_p V (D : PropF V) ps c Γ1 Γ2 (r : ImpLrule_p ps c) :
  gen_step l41prop D isubfml (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad dc.
unfold l41prop. intros * ceq * dbe.  destruct r as [p A D'].
inversion ceq. subst. clear ceq. 
inversion fp.  inversion X0. clear fp X0 X2. subst.

unfold fmlsext in H0.  unfold fmlsext in X.  unfold fmlsext in X1.
pose (LJA_can_rel_ImpL_Var_inv2 dbe). 
unfold can_rel in c.
acacD'T2 ; subst ; clear X2.

- gs_Imp_p_tac V c p A B D E X X0 X1 dbe
(G1 ++ [B] ++ H0) Γ2 G1 (H0 ++ [A] ++ Γ2)
 G1 (H0 ++ [Imp (Var p) A] ++ Γ2) (G1 ++ [Imp D B] ++ H0) Γ2.

- gs_Imp_p_tac V c p A B D E X X0 X1 dbe
(Γ1 ++ [B]) Γ2 Γ1 ([A] ++ Γ2) Γ1 ([Imp (Var p) A] ++ Γ2) (Γ1 ++ [Imp D B]) Γ2.

- list_eq_ncT. cD. subst.
gs_Imp_p_tac V c p A B D E X X0 X1 dbe
 Γ1 ([B] ++ Γ2) (Γ1 ++ [A]) Γ2 (Γ1 ++ [Imp (Var p) A]) Γ2 Γ1 ([Imp D B] ++ Γ2).

- gs_Imp_p_tac V c p A B D E X X0 X1 dbe
 Γ1 (H2 ++ [B] ++ G2) (Γ1 ++ [A] ++ H2) G2
 (Γ1 ++ [Imp (Var p) A] ++ H2) G2 Γ1 (H2 ++ [Imp D B] ++ G2).

Qed.

Check gs_LJA_ImpL_Imp_p.

Lemma gs_LJA_ImpL_sr V (D : PropF V) ps c Γ1 Γ2 
  (r : rlsmap (pair []) LJsrrules ps c) :
  gen_step l41prop D isubfml (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. 
unfold l41prop. intros * ceq * dbe.
inversion r. subst. clear r. 
inversion ceq. subst. clear ceq. 
destruct H.
- destruct a.  simpl in fp.  inversion fp.
inversion X0. clear fp X0 X2. subst.
rewrite H1 in X.  rewrite H1 in X1.
pose (sad _ (isub_AndR _ _) _ (fst X1)).
specialize (l _ _ eq_refl _ _ dbe).
specialize (sad _ (isub_AndL _ _) _ (fst X)).
specialize (sad _ _ eq_refl _ _ l).
clear dc dbe H1 X X1 l.
eapply derI. eapply fextI. apply rmI.
apply il_anc'. apply And_ail'.
exact (dersrec_singleI sad).
- destruct o.  simpl in fp.  inversion fp.  clear fp X0. subst.
rewrite H1 in X.
specialize (sad _ (isub_OrL _ _) _ (fst X)).
specialize (sad _ _ eq_refl _ _ dbe).
clear dc dbe H1 X.
eapply derI. eapply fextI. apply rmI.
apply il_anc'. apply Or_ail'. simpl. simpl in sad.
pose (insL_lja (G1 ++ [Imp A B]) G2 [Imp B0 B]).
rewrite <- !app_assoc in d.
apply d in sad.  unfold fmlsext.  exact (dersrec_singleI sad).
- destruct o.  simpl in fp.  inversion fp.  clear fp X0. subst.
rewrite H1 in X.
specialize (sad _ (isub_OrR _ _) _ (fst X)).
specialize (sad _ _ eq_refl _ _ dbe).
clear dc dbe H1 X.
eapply derI. eapply fextI. apply rmI.
apply il_anc'. apply Or_ail'. simpl. simpl in sad.
pose (insL_lja G1 (Imp B0 B :: G2) [Imp A B]).
apply d in sad.  unfold fmlsext.  exact (dersrec_singleI sad).
Qed.

Check gs_LJA_ImpL_sr.

(*

Check gen_step_lemT.
Check gen_step_c_lem.  Check gen_step_tr_lem. Check gf2_step_tr_lem.
Check height_step_tr_lem.

(* proof using gen_step_lemT, don't think we want this *)
Definition l41dtprop {V} rules prems (D : PropF V) dt := 
  l41prop D (@derrec_fc_concl _ rules prems dt).
  
Lemma hs_LJA_ImpL_adm V (D : PropF V)
  c (dt : derrec LJArules emptyT c) ps (br : botRule_fc (fcI dt) ps c) :
  @LJArules V ps c -> 
  height_step_tr (dtfun l41prop) D isubfml (fcI dt).
Proof. intro ljpc. inversion ljpc ; subst ; clear ljpc.
inversion X ; subst ; clear X.
destruct X0.
- (* left compound Imp rules, invertible *)
apply (gs_hs br).  eapply gs_LJA_ImpL_Ail. exact r.

- admit.
- (* ImpLrule_p *) apply (gs_hs br).  apply gs_LJA_ImpL_Imp_p. exact i.

- (* ImpRrule, IH not used *) destruct i.
apply (gs_hs br). clear br dt.  unfold gen_step.
intros sub fdt dab. clear sub dab.
inversion fdt. clear X0 fdt. subst.  unfold l41prop.
intros * abeq * dbe. destruct X. clear l.
inversion abeq. clear abeq. subst.
(* apply ImpL_Imp_rule *)
eapply derI.  eapply fextI.  apply rmI.  apply Imp_anc'.
unfold fmlsext in H0. simpl in H0.
eapply swap_ins in H0.
unfold fmlsext in d.  eapply exchL_lja in d.
2: apply fst_relI. 2: exact (swapped_comm H0).
apply dlCons.  exact (insL_lja _ _ [Imp B B0] d).
apply dersrec_singleI. exact dbe.

- (* Idrule, so D is Var _ , IH not used *) destruct i.
unfold height_step_tr.  unfold gf2_step_tr.  intros sub fdt. clear sub fdt br.  
unfold dtfun.  rewrite der_fc_concl_eq.  unfold l41prop.
intros * vveq * dbe.  inversion vveq. clear vveq.
eapply derI.  eapply fextI.  apply rmI.  apply ImpL_anc'.
simpl in dt. rewrite -> H0 in dt.
apply dlCons.  exact (insL_lja _ _ [Imp (Var A) B] dt).
apply dersrec_singleI. exact dbe.

- (* common left rules, invertible *)
apply (gs_hs br).  eapply gs_LJA_ImpL_sl. exact r.

- (* simple right rules *)
apply (gs_hs br).  eapply gs_LJA_ImpL_sr. exact r.

Admitted.



Lemma LJA_ImpL_adm V D : forall seq, derrec LJArules emptyT seq -> 
  @l41prop V D seq.
Proof.  intros seq dt.
assert (dtfun l41prop D (fcI dt)).
all: cycle 1.
unfold dtfun in X. simpl in X.  rewrite !der_concl_eq in X. exact X.
apply (height_step_tr_lem _ (AccT_isubfml D)).
intros. clear seq dt.  destruct dt0.
apply (hs_LJA_ImpL_adm (get_botrule _) (bot_is_rule _)).  Qed.
  

*)
