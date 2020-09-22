
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

(*
Lemma LJA_der_id_mp {V} :
  forall (A : PropF V) (a : AccT dnsubfml A), 
  (forall G, derrec LJArules emptyT (A :: G, A)) *
  (forall B H, derrec LJArules emptyT (A :: Imp A B :: H, B)).
Proof. 
epose (AccT_rect (fun A _ => 
  (forall G, derrec LJArules emptyT (A :: G, A)) *
  (forall B H, derrec LJArules emptyT (A :: Imp A B :: H, B)))).
apply p. clear p.  intros A adn IH.  split.
- intro G. destruct A.
+ eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eq. eapply Id_anc. eapply Idrule_I.  reflexivity.
reflexivity. apply dlNil.
+ eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eq. eapply lrls_anc. apply rmI.  apply Bot_sl. apply Botrule_I.
reflexivity.  reflexivity. apply dlNil.
+ eapply derI. eapply (@fextI _ _ _ [] (Imp A1 A2 :: G)).
eapply rmI_eq. eapply ImpR_anc. apply ImpRrule_I.
reflexivity.  reflexivity. 
apply dersrec_singleI.  apply IH. apply dnsub_ImpL.
+ eapply derI. eapply (@fextI _ _ _ [] (And A1 A2 :: G)).
eapply rmI_eq. apply rrls_anc. apply rmI. apply AndR_sr.  apply AndRrule_I.
reflexivity.  reflexivity.  apply dlCons.
++ eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eq. eapply lrls_anc. apply rmI. apply AndL_sl.  apply AndLrule_I.
reflexivity.  reflexivity.  apply dersrec_singleI.
apply IH. apply dnsub_AndL. tauto. (* why? *)
++ apply dersrec_singleI.
eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eq. eapply lrls_anc. apply rmI. apply AndL_sl.  apply AndLrule_I.
reflexivity.  reflexivity.  apply dersrec_singleI.
(* need to use exchange *)
simpl. unfold fmlsext. simpl.
specialize (IH _ (dnsub_AndR _ _)).  pose (fst IH (A1 :: G)).
apply (exchL_lja d). apply fst_relI. apply swapped_cc.
+ eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eq. eapply lrls_anc. apply rmI. apply OrL_sl.  apply OrLrule_I.
reflexivity.  reflexivity.  apply dlCons.
++ eapply derI. eapply (@fextI _ _ _ [A1] G).
eapply rmI_eq. apply rrls_anc. apply rmI. apply OrR1_sr.  apply OrR1rule_I.
reflexivity.  reflexivity.  apply dersrec_singleI.
apply (fst (IH _ (dnsub_OrL _ _))).
++ apply dersrec_singleI.
eapply derI. eapply (@fextI _ _ _ [A2] G).
eapply rmI_eq. apply rrls_anc. apply rmI. apply OrR2_sr.  apply OrR2rule_I.
reflexivity.  reflexivity.  apply dersrec_singleI.
apply (fst (IH _ (dnsub_OrR _ _))).

- intros.  destruct A.
+ need to use invertibility of ImpR
