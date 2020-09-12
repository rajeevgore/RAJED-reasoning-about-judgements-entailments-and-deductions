
(* Contraction-Free Sequent Calculi for Intuitionistic Logic, Roy Dyckhoff
Journal of Symbolic Logic ,  57 (1992), 795-807
Stable URL: http://www.jstor.com/stable/2275431 *)

Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT ddT.
Require Import gstep.
Require Import List_lemmasT gen_tacs swappedT.
Require Import gen_seq.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive PropF (V : Set): Type :=
 | Var : V -> PropF V
 | Bot : PropF V
 | Imp : PropF V -> PropF V -> PropF V
 | And : PropF V -> PropF V -> PropF V
 | Or : PropF V -> PropF V -> PropF V.

Inductive isubfml {V} : PropF V -> PropF V -> Type :=
  | isub_ImpL : forall C D, isubfml C (Imp C D)
  | isub_ImpR : forall C D, isubfml D (Imp C D)
  | isub_AndL : forall C D, isubfml C (And C D)
  | isub_AndR : forall C D, isubfml D (And C D)
  | isub_OrL : forall C D, isubfml C (Or C D)
  | isub_OrR : forall C D, isubfml D (Or C D).

Lemma AccT_isubfml {V} (A : PropF V) : AccT isubfml A.
Proof. induction A ; apply AccT_intro ; intros A' isf ;
  inversion isf ; subst ; assumption. Qed.

(* singleton-on-the-right sequent *)
Definition srseq A := prod (list A) A.

(* singleton-on-the-right sequent of formulae *)
Definition srseqf V := srseq (PropF V).

(* specifying formula, so we can limit it to propositions *)
Inductive Idrule {V} A : rlsT (srseq (PropF V)) :=
  | Idrule_I : Idrule A [] (pair [A] A).

Inductive Botrule {V} : rlsT (list (PropF V)) :=
  | Botrule_I : Botrule [] [Bot V].

Inductive OrR1rule {V} : rlsT (PropF V) :=
  | OrR1rule_I : forall A B, OrR1rule [A] (Or A B).

Inductive OrR2rule {V} : rlsT (PropF V) :=
  | OrR2rule_I : forall A B, OrR2rule [B] (Or A B).

Inductive OrLrule {V} : rlsT (list (PropF V)) :=
  | OrLrule_I : forall A B, OrLrule [[A] ; [B]] [Or A B].

Inductive AndLrule {V} : rlsT (list (PropF V)) :=
  | AndLrule_I : forall A B, AndLrule [[A ; B]] [And A B].

Inductive AndRrule {V} : rlsT (PropF V) :=
  | AndRrule_I : forall A B, AndRrule [A ; B] (And A B).

Inductive ImpRrule {V} : rlsT (srseq (PropF V)) :=
  | ImpRrule_I : forall A B, ImpRrule [pair [A] B] (pair [] (Imp A B)).

Inductive ImpLrule {V} : rlsT (srseq (PropF V)) :=
  | ImpLrule_I : forall A B G, 
    ImpLrule [pair [Imp A B] A ; pair [B] G] (pair [Imp A B] G).

(* right rules which just have context on the left *)
Inductive LJsrrules {V} : rlsT (PropF V) :=
  | AndR_sr : forall ps c, AndRrule ps c -> LJsrrules ps c
  | OrR1_sr : forall ps c, OrR1rule ps c -> LJsrrules ps c
  | OrR2_sr : forall ps c, OrR2rule ps c -> LJsrrules ps c
  .

(* left rules which just have context on the left and right *)
Inductive LJslrules {V} : rlsT (list (PropF V)) :=
  | AndL_sl : forall ps c, AndLrule ps c -> LJslrules ps c
  | OrL_sl : forall ps c, OrLrule ps c -> LJslrules ps c
  | Bot_sl : forall ps c, Botrule ps c -> LJslrules ps c
  .

Lemma LJsl_single V ps c : @LJslrules V ps c -> {c' & c = [c']}.
Proof. intro ljsl.  destruct ljsl ; rename_last r ;
destruct r ; subst ; eexists ; reflexivity. Qed.

(* all rules, without left context,
  note Idrule for propositions only, saves effort doing invertibility
  see eg ImpLthm1/2 in ../modal/k4_inv.v *)

Inductive LJncrules {V} : rlsT (srseq (PropF V)) :=
  | ImpL_nc : forall ps c, ImpLrule ps c -> LJncrules ps c
  | ImpR_nc : forall ps c, ImpRrule ps c -> LJncrules ps c
  | Id_nc : forall A ps c, Idrule (Var A) ps c -> LJncrules ps c
  | lrls_nc : forall G ps c,
    rlsmap (flip pair G) LJslrules ps c -> LJncrules ps c
  | rrls_nc : forall ps c, rlsmap (pair []) LJsrrules ps c -> LJncrules ps c
  .

Definition LJrules {V} := fst_ext_rls (@LJncrules V).

Definition rrls_nc' V ps c rpc := @rrls_nc V _ _ (rmI _ _ ps c rpc).
Definition lrls_nc' V G ps c rpc := @lrls_nc V G _ _ (rmI _ _ ps c rpc).
Definition ImpR_nc' V A B := ImpR_nc (@ImpRrule_I V A B).
Definition ImpL_nc' V A B G := ImpL_nc (@ImpLrule_I V A B G).

Lemma LJrules_req V : req (@LJrules V) (fst_ext_rls LJncrules).
Proof.  unfold LJrules. apply req_refl. Qed.

Lemma LJrules_nc_rsub V : rsub LJncrules (@LJrules V).
Proof.  unfold LJrules. intros ps c nc. 
apply (@fextI _ _ _ [] []). eapply rmI_eq. apply nc.
clear nc. induction ps.
reflexivity. simpl. rewrite - IHps.
destruct a. simpl. unfold fmlsext.  simpl. rewrite app_nil_r.  reflexivity.
destruct c. simpl. unfold fmlsext.  simpl. rewrite app_nil_r.  reflexivity.
Qed.

Lemma LJnc_seL V ps cl cr : @LJncrules V ps (cl, cr) -> sing_empty cl.
Proof. intro ljnc. inversion ljnc ; subst ; clear ljnc.
- inversion H. apply se_single.
- inversion H. apply se_empty.
- inversion X. apply se_single.
- inversion X. destruct X0. + destruct a.  apply se_single.
  + destruct o.  apply se_single.  + destruct b.  apply se_single.
- inversion X.  apply se_empty. Qed.

Definition LJweakening V seq :=
  can_wkL_req (req_sym (LJrules_req V)) (@weakeningL _ _ seq _).

Print Implicit LJweakening.

(* need to check derivability of Idrule for any formula *)
Lemma idrule_der {V} A : derrec LJrules emptyT ([A : PropF V], A).
Proof. induction A.
- eapply derI. apply LJrules_nc_rsub.
eapply Id_nc. apply Idrule_I. apply dlNil.
- eapply derI. apply LJrules_nc_rsub.
eapply lrls_nc. eapply rmI_eq.  apply Bot_sl.
apply Botrule_I.  reflexivity.  reflexivity.  apply dlNil.

- (* Imp *) eapply derI.
+ eapply (@fextI _ _ _ [_] []).  eapply rmI_eq.
apply ImpR_nc.  apply ImpRrule_I.
reflexivity.  simpl.  unfold fmlsext.  reflexivity.
+ simpl.  unfold fmlsext.  simpl.
apply dersrec_singleI.  eapply derI.
++ eapply (@fextI _ _ _ [] [A1]).  eapply rmI_eq.
eapply ImpL_nc.  apply ImpLrule_I.
reflexivity.  simpl.  unfold fmlsext.  reflexivity.
++ simpl.  unfold fmlsext.  simpl.  apply dlCons.
+++ epose (@LJweakening _ _).  unfold can_wkL in c.  specialize (c IHA1).
unfold wkL_valid' in c.  unfold wkL_valid in c.  specialize (c [Imp A1 A2] []).
unfold fmlsext in c.  simpl in c. exact c.
+++ apply dersrec_singleI.  epose (@LJweakening _ _).  unfold can_wkL in c.
specialize (c IHA2).  unfold wkL_valid' in c.  unfold wkL_valid in c.
specialize (c [] [A1]).  unfold fmlsext in c.  simpl in c. exact c.

- (* And *) eapply derI. 
+ apply LJrules_nc_rsub.  eapply lrls_nc.  eapply rmI_eq.
apply AndL_sl.  apply AndLrule_I.  reflexivity.  reflexivity.
+ simpl.  apply dersrec_singleI. eapply derI.
++ eapply (@fextI _ _ _ [A1 ; A2] []).  eapply rmI_eq.
eapply rrls_nc.  apply rmI.
apply AndR_sr.  apply AndRrule_I.  reflexivity.  reflexivity.
++ simpl. unfold fmlsext. simpl.  apply dlCons.
+++ epose (@LJweakening _ _).  unfold can_wkL in c.  specialize (c IHA1).
unfold wkL_valid' in c.  unfold wkL_valid in c.  specialize (c [] [A2]).
unfold fmlsext in c.  simpl in c. exact c.
+++ apply dersrec_singleI.
epose (@LJweakening _ _).  unfold can_wkL in c.  specialize (c IHA2).
unfold wkL_valid' in c.  unfold wkL_valid in c.  specialize (c [A1] []).
unfold fmlsext in c.  simpl in c. exact c.

- (* Or *) eapply derI. 
+ apply LJrules_nc_rsub.  eapply lrls_nc.  eapply rmI_eq.
apply OrL_sl.  apply OrLrule_I.  reflexivity.  reflexivity.
+ simpl. apply dlCons.
++ eapply derI.
+++ eapply (@fextI _ _ _ [A1] []).  eapply rmI_eq.
eapply rrls_nc.  apply rmI.
apply OrR1_sr.  apply OrR1rule_I.  reflexivity.
simpl. unfold fmlsext. reflexivity.
+++ simpl. unfold fmlsext. simpl. apply dersrec_singleI. apply IHA1.
++ apply dersrec_singleI.  eapply derI.
+++ eapply (@fextI _ _ _ [A2] []).  eapply rmI_eq.
eapply rrls_nc.  apply rmI.
apply OrR2_sr.  apply OrR2rule_I.  reflexivity.
simpl. unfold fmlsext. reflexivity.
+++ simpl. unfold fmlsext. simpl. apply dersrec_singleI. apply IHA2.
Qed.

Print Implicit idrule_der.

Lemma fer_Id V A ant : InT A ant -> fst_ext_rls (@Idrule V A) [] (ant, A).
Proof. intro ia. apply InT_split in ia.  cD. subst.
eapply fextI_eq'. apply Idrule_I. reflexivity. reflexivity. Qed.

(** exchange - largely copied from ../modal/k4_exch.v **)
(* properties can exchange adjacent sublists, and resulting sequent
  is derivable (not conditional on unexchanged version being derivable *)

Print Implicit exchL_std_rule.

(* exchange for LJ system *)
Lemma exchL_lj: forall V concl,
  derrec (@LJrules V) emptyT concl ->
     forall concl', fst_rel (@swapped _) concl concl' ->
    derrec (@LJrules V) emptyT concl'.
Proof. unfold LJrules. intro. apply der_trf.
apply exchL_std_rule. apply LJnc_seL. Qed.

