
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

(*

Check gen_step_lemT.
Check gen_step_c_lem.  Check gen_step_tr_lem. Check gf2_step_tr_lem.
Check height_step_tr_lem.

(* proof using gen_step_lemT *)
Definition l41dtprop {V} rules prems (D : PropF V) dt := 
  l41prop D (@derrec_fc_concl _ rules prems dt).


Lemma LJA_ImpL_adm V D : forall dt,
  @l41dtprop V LJArules emptyT D dt.
Proof. intro.
eapply height_step_tr_lem.
admit.
clear dt.
intros. 
unfold height_step_tr.
unfold gf2_step_tr.
intros sub fdt.
unfold l41dtprop.
unfold l41prop.

  
  
Lemma LJA_ImpL_adm V D : forall seq, derrec LJArules emptyT seq -> 
  @l41prop V D seq.
Proof. eapply gen_step_lemT.
admit.
intros * ljpc.
unfold gen_step.
intros acc fdl der.
unfold l41prop.
intros * cgg * dbe.
destruct ljpc.
inversion r. clear r. subst. destruct X.
- admit.
- 

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

Lemma LJAil_psne V ps c : (@LJAilrules V) ps c ->
  sigT (fun p => sigT (fun pt => ps = p :: pt)).
Proof. intro ljpc. 
destruct ljpc ; destruct i ; eexists ; eexists ; reflexivity. Qed.

Lemma hs_LJA_ImpL_adm V (D : PropF V)
  c (dt : derrec LJArules emptyT c) ps (br : botRule_fc (fcI dt) ps c) :
  @LJArules V ps c -> 
  height_step_tr (dtfun l41prop) D isubfml (fcI dt).
Proof. intro ljpc. inversion ljpc ; subst ; clear ljpc.
inversion X ; subst ; clear X.
destruct X0.
- (* left compound Imp rules, invertible *)
apply (gs_hs br).

need to make this a separate lemma 

unfold gen_step. intros sad fp dc. clear sad br.
unfold l41prop. intros * ceq * dbe.
inversion r. subst. clear r. 
rewrite ceq in dc.
simpl in ceq. unfold fmlsext in ceq.
inversion ceq. subst. clear ceq.
acacD'T2 ; subst.
+
(* apply rule in desired conclusion *)
simpl.  unfold fmlsext.  assoc_mid c0.
eapply derI.  eapply fextI.  eapply rmI_eqc.
eapply il_anc.  apply rmI.  apply H. reflexivity.
apply dersrecI_forall.  intros c cin.
apply InT_mapE in cin. cD.  apply InT_mapE in cin1. cD.
(* invert rule in dbe *)
revert dbe. unfold fmlsext. assoc_mid c0. intro dbe.
pose (LJA_inv_ail _ _ H dbe).
eapply dersrecD_forall in d. 
2: apply InT_map.  2: apply InT_map. 2: eassumption.
eapply ForallTD_forall in fp.
2: apply InT_map.  2: apply InT_map. 2: eassumption.
unfold l41prop in fp.
inversion cin3. inversion cin0. subst. clear cin3 cin0.
unfold fmlsext.  assoc_single_mid.
simpl in fp.  unfold fmlsext in fp.
apply (snd fp). list_eq_assoc.
simpl in d.  unfold fmlsext in d.
apply (eq_rect _ _ d). list_eq_assoc.





Lemma LJA_ImpL_adm V D : forall seq, derrec LJArules emptyT seq -> 
  @l41prop V D seq.
Proof.  intros seq dt.
assert (dtfun l41prop D (fcI dt)).
all: cycle 1.
unfold dtfun in X. simpl in X.  rewrite !der_concl_eq in X. exact X.
apply (height_step_tr_lem _ (AccT_isubfml D)).
intros. clear seq dt.  destruct dt0.
apply (hs_LJA_ImpL_adm (get_botrule _) (bot_is_rule _)).  Qed.
  

    A isubfml (fcI dl) (fcI dr).
Proof. intros ma mb. inversion mb ; subst.
- inversion ma ; subst.
apply (gs2_hs2 brl brr).


*)

