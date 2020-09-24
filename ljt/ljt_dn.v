
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
Require Import gen genT ddT.
Require Import List_lemmasT swappedT.
Require Import gen_tacs.
Require Import gen_seq gstep rtcT.
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


