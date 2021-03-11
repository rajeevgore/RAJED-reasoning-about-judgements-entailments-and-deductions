
(* Contraction-Free Sequent Calculi for Intuitionistic Logic, Roy Dyckhoff
Journal of Symbolic Logic ,  57 (1992), 795-807
Stable URL: http://www.jstor.com/stable/2275431 *)

Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT rtcT.
Require Import gstep.
Require Import List_lemmasT gen_tacs swappedT.
Require Import gen_seq.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import PeanoNat.

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

(* formula weight per Dyckhoff and Negri, 2000 *)
Fixpoint dnfw {V} fml :=
  match (fml : PropF V) with
    (* note, next two lines swap 1 and 0 from Dyckhoff *)
    | Bot _ => 1
    | Var _ => 0
    | Imp A B => S (dnfw A + dnfw B)
    | And A B => S (S (dnfw A + dnfw B))
    | Or A B => S (S (S (dnfw A + dnfw B)))
  end.

Lemma dnsub_fw {V} : rsub (@dnsubfml V) (measure dnfw).
Proof. intros u v dn. destruct dn ; unfold measure ; simpl ; 
rewrite ?add_S ; apply Lt.le_lt_n_Sm ; repeat (apply Le.le_n_S) ;
repeat (apply le_S) ; try (apply Plus.le_plus_l) ; 
try (apply Plus.le_plus_r) ; try (apply Le.le_refl) ;
rewrite - ?Nat.add_assoc ; try (apply Plus.le_plus_l) ; 
try (apply Plus.le_plus_r) ; try (apply Le.le_refl).
apply Plus.plus_le_compat_l. apply Plus.le_plus_r. Qed.

Lemma tc_dnsub_fw {V} : rsub (clos_transT (@dnsubfml V)) (measure dnfw).
Proof. eapply rsub_trans.  apply (clos_transT_mono dnsub_fw).
apply clos_transT_measure. Qed.

Definition dnlw {V} fmls := fold_right Nat.add 0 (map (@dnfw V) fmls).

(* dnsw : sequent weight - note that ImpL_Imp_rule can have premise with
  larger sequent weight than conclusion *)
Definition dnsw {V} seq :=
  match seq with
    | (X, A) => fold_right Nat.add (@dnfw V A) (map (@dnfw V) X)
  end.

Lemma dnlw_app {V} xs ys : @dnlw V (xs ++ ys) = (dnlw xs + dnlw ys)%nat.
Proof. unfold dnlw.
induction xs ; simpl.  reflexivity.
rewrite IHxs. apply Nat.add_assoc. Qed.

Lemma dnsw_alt {V} xs A : @dnsw V (xs, A) = (dnlw xs + dnfw A)%nat.
Proof. unfold dnsw.  unfold dnlw.
induction xs ; simpl.  reflexivity.
rewrite IHxs. apply Nat.add_assoc. Qed.

Lemma AccT_dnsubfml : forall V (A : PropF V), AccT dnsubfml A.
Proof. intros *. eapply rsub_AccT. apply dnsub_fw. apply AccT_measure. Qed.

Lemma isub_dnsub V : rsub (@isubfml V) dnsubfml.
Proof. intros u v isf. destruct isf.
apply dnsub_ImpL.  apply dnsub_ImpR.  apply dnsub_AndL.
apply dnsub_AndR.  apply dnsub_OrL.  apply dnsub_OrR. Qed.

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

(* trying this rule in place of Dyckhoff's atom rule *)
Inductive ImpLrule_p {V} : rlsT (srseq (PropF V)) :=
  | ImpLrule_p_I : forall p B G, ImpLrule_p
    [pair [Imp (Var p) B] (Var p) ; pair [B] G] (pair [Imp (Var p) B] G).

Lemma ImpLrule_p_rsub {V} : rsub (@ImpLrule_p V) ImpLrule.
Proof. intros ps c ip. destruct ip. apply ImpLrule_I. Qed.

(* special ImpL rules in Dyckhoff's LJT system *)

Inductive ImpL_atom_rule {V} : rlsT (list (PropF V)) :=
  | ImpL_atom_rule_I : forall p B, 
    ImpL_atom_rule [[B ; Var p]] ([Imp (Var p) B ; Var p]).

Inductive ImpL_And_rule {V} : rlsT (list (PropF V)) :=
  | ImpL_And_rule_I : forall B C D, 
    ImpL_And_rule [[Imp C (Imp D B)]] ([Imp (And C D) B]).

Inductive ImpL_Or_rule {V} : rlsT (list (PropF V)) :=
  | ImpL_Or_rule_I : forall B C D, 
    ImpL_Or_rule [[Imp C B ; Imp D B]] ([Imp (Or C D) B]).

Inductive ImpL_Imp_rule {V} : rlsT (srseq (PropF V)) :=
  | ImpL_Imp_rule_I : forall B C D G, 
    ImpL_Imp_rule [pair [Imp D B ; C] D ; pair [B] G] (pair [Imp (Imp C D) B] G).

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

(* Dyckhoff rules with same rhs *)
Inductive LJTilrules {V} : rlsT (list (PropF V)) :=
  | And_il : forall ps c, ImpL_And_rule ps c -> LJTilrules ps c
  | Or_il : forall ps c, ImpL_Or_rule ps c -> LJTilrules ps c
  | atom_il : forall ps c, ImpL_atom_rule ps c -> LJTilrules ps c
  .

Inductive LJAilrules {V} : rlsT (list (PropF V)) :=
  | And_ail : forall ps c, ImpL_And_rule ps c -> LJAilrules ps c
  | Or_ail : forall ps c, ImpL_Or_rule ps c -> LJAilrules ps c
  .

Definition And_ail' V A B C := And_ail (@ImpL_And_rule_I V A B C).
Definition Or_ail' V A B C := Or_ail (@ImpL_Or_rule_I V A B C).

(* exchange rule, without context, avoiding trivial instances *)
Inductive exch_rule {W} : rlsT (list W) :=
  | exchI : forall x y X Y,
    exch_rule [(x :: X) ++ (y :: Y)] ((y :: Y) ++ (x :: X)).

(* all rules of LJT, without context - requires exchange rule *)
(* separate out rules with single principal formula *)
Inductive LJTSncrules {V} : rlsT (srseq (PropF V)) :=
  | il_tsnc : forall G ps c, 
    rlsmap (flip pair G) LJAilrules ps c -> LJTSncrules ps c
  | Imp_tsnc : forall ps c, ImpL_Imp_rule ps c -> LJTSncrules ps c
  | ImpR_tsnc : forall ps c, ImpRrule ps c -> LJTSncrules ps c
  | Id_tsnc : forall (A : V) ps c, Idrule (Var A) ps c -> LJTSncrules ps c
  | lrls_tsnc : forall G ps c,
    rlsmap (flip pair G) LJslrules ps c -> LJTSncrules ps c
  | rrls_tsnc : forall ps c, rlsmap (pair []) LJsrrules ps c -> LJTSncrules ps c
  .

Inductive LJTncrules {V} : rlsT (srseq (PropF V)) :=
  | sing_tnc : forall ps c, LJTSncrules ps c -> LJTncrules ps c
  | atom_tnc : forall G ps c, 
    rlsmap (flip pair G) ImpL_atom_rule ps c -> LJTncrules ps c
  | exch_tnc : forall G ps c, 
    rlsmap (flip pair G) exch_rule ps c -> LJTncrules ps c
  .

(* all rules of LJA, without context *)
Inductive LJAncrules {V} : rlsT (srseq (PropF V)) :=
  | il_anc : forall G ps c, 
    rlsmap (flip pair G) LJAilrules ps c -> LJAncrules ps c
  | Imp_anc : forall ps c, ImpL_Imp_rule ps c -> LJAncrules ps c
  | ImpL_anc : forall ps c, ImpLrule_p ps c -> LJAncrules ps c
  | ImpR_anc : forall ps c, ImpRrule ps c -> LJAncrules ps c
  | Id_anc : forall (A : V) ps c, Idrule (Var A) ps c -> LJAncrules ps c
  | lrls_anc : forall G ps c,
    rlsmap (flip pair G) LJslrules ps c -> LJAncrules ps c
  | rrls_anc : forall ps c, rlsmap (pair []) LJsrrules ps c -> LJAncrules ps c
  .

Lemma LJsl_single {V} ps c : @LJslrules V ps c -> {c' & c = [c']}.
Proof. intro ljsl.  destruct ljsl ; rename_last r ;
destruct r ; subst ; eexists ; reflexivity. Qed.

Lemma LJAil_single {V} ps c : LJAilrules ps c -> {c' : PropF V & c = [c']}.
Proof. intro. destruct X ; destruct i ; eexists ; reflexivity. Qed.

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
Definition LJTrules {V} := fst_ext_rls (@LJTncrules V).
Definition LJArules {V} := fst_ext_rls (@LJAncrules V).
Definition LJTSrules {V} := fst_ext_rls (@LJTSncrules V).

Definition rrls_nc' {V} ps c rpc := @rrls_nc V _ _ (rmI _ _ ps c rpc).
Definition lrls_nc' {V} G ps c rpc := @lrls_nc V G _ _ (rmI _ _ ps c rpc).
Definition ImpR_nc' {V} A B := ImpR_nc (@ImpRrule_I V A B).
Definition ImpL_nc' {V} A B G := ImpL_nc (@ImpLrule_I V A B G).

Definition rrls_tnc {V} ps c rpc := @sing_tnc V ps c (@rrls_tsnc V ps c rpc).
Definition lrls_tnc {V} G ps c rpc := 
  @sing_tnc V ps c (@lrls_tsnc V G ps c rpc).
Definition il_tnc {V} G ps c rpc := @sing_tnc V ps c (@il_tsnc V G ps c rpc).
Definition ImpR_tnc {V} ps c rpc := @sing_tnc V ps c (@ImpR_tsnc V ps c rpc).
Definition Imp_tnc {V} ps c rpc := @sing_tnc V ps c (@Imp_tsnc V ps c rpc).

Definition rrls_tnc' {V} ps c rpc := @rrls_tnc V _ _ (rmI _ _ ps c rpc).
Definition lrls_tnc' {V} G ps c rpc := @lrls_tnc V G _ _ (rmI _ _ ps c rpc).
Definition il_tnc' {V} G ps c rpc := @il_tnc V G _ _ (rmI _ _ ps c rpc).
Definition ImpR_tnc' {V} A B := ImpR_tnc (@ImpRrule_I V A B).
Definition Imp_tnc' {V} B C D G := Imp_tnc (@ImpL_Imp_rule_I V B C D G).

Definition rrls_anc' {V} ps c rpc := @rrls_anc V _ _ (rmI _ _ ps c rpc).
Definition lrls_anc' {V} G ps c rpc := @lrls_anc V G _ _ (rmI _ _ ps c rpc).
Definition il_anc' {V} G ps c rpc := @il_anc V G _ _ (rmI _ _ ps c rpc).
Definition ImpR_anc' {V} A B := ImpR_anc (@ImpRrule_I V A B).
Definition Imp_anc' V B C D G := Imp_anc (@ImpL_Imp_rule_I V B C D G).
Definition ImpL_anc' V p B G := ImpL_anc (@ImpLrule_p_I V p B G).
Definition Id_anc' {V} v := Id_anc (@Idrule_I V (Var v)).

Lemma LJrules_req V : req (@LJrules V) (fst_ext_rls LJncrules).
Proof.  unfold LJrules. apply req_refl. Qed.

Lemma LJTrules_req V : req (@LJTrules V) (fst_ext_rls LJTncrules).
Proof.  unfold LJTrules. apply req_refl. Qed.

Lemma LJArules_req V : req (@LJArules V) (fst_ext_rls LJAncrules).
Proof.  unfold LJArules. apply req_refl. Qed.

Lemma sing_anc V ps c : LJTSncrules ps c -> @LJAncrules V ps c.
Proof. intro. destruct X.
exact (il_anc r).  exact (Imp_anc i).  exact (ImpR_anc i).
exact (Id_anc i).  exact (lrls_anc r).  exact (rrls_anc r). Qed.

Lemma LJAncrules_ljts V ps c : 
  @LJAncrules V ps c -> LJTSncrules ps c + ImpLrule_p ps c.
Proof. intro. destruct X.
- exact (inl (il_tsnc r)).  - exact (inl (Imp_tsnc i)).  - exact (inr i).
- exact (inl (ImpR_tsnc i)).  - exact (inl (Id_tsnc i)).
- exact (inl (lrls_tsnc r)).  - exact (inl (rrls_tsnc r)). Qed.

Lemma LJnc_seL V ps cl cr : @LJncrules V ps (cl, cr) -> sing_empty cl.
Proof. intro ljnc. inversion ljnc ; subst ; clear ljnc.
- inversion X. apply se_single.
- inversion X. apply se_empty.
- inversion X. apply se_single.
- inversion X. destruct X0. + destruct a.  apply se_single.
  + destruct o.  apply se_single.  + destruct b.  apply se_single.
- inversion X.  apply se_empty. Qed.

(* doesn't hold for atom and exchange rules *) 
Lemma LJTSnc_seL V ps cl cr : @LJTSncrules V ps (cl, cr) -> sing_empty cl.
Proof. intro ljnc. inversion ljnc ; subst ; clear ljnc.
- inversion X. destruct X0 ; destruct i ; apply se_single.
- inversion X. apply se_single.
- inversion X. apply se_empty.
- inversion X. apply se_single.
- inversion X. destruct X0. + destruct a.  apply se_single.
  + destruct o.  apply se_single.  + destruct b.  apply se_single.
- inversion X.  apply se_empty. Qed.

Lemma LJAnc_seL V ps cl cr : @LJAncrules V ps (cl, cr) -> sing_empty cl.
Proof. intro ljnc. apply LJAncrules_ljts in ljnc. destruct ljnc.
eapply LJTSnc_seL. eassumption.
inversion i. apply se_single.  Qed.

Definition LJweakening V seq :=
  can_wkL_req (req_sym (LJrules_req V)) (@weakeningL _ _ seq _).
Definition LJTweakening V seq :=
  can_wkL_req (req_sym (LJTrules_req V)) (@weakeningL _ _ seq _).
Definition LJAweakening V seq :=
  can_wkL_req (req_sym (LJArules_req V)) (@weakeningL _ _ seq _).

Print Implicit LJweakening.  Print Implicit LJAweakening.

(* need to check derivability of Idrule for any formula *)
Lemma idrule_der_lj {V} A : derrec LJrules emptyT ([A : PropF V], A).
Proof. induction A.
- eapply derI. apply rsub_fer.
eapply Id_nc. apply Idrule_I. apply dlNil.
- eapply derI. apply rsub_fer.
eapply lrls_nc. eapply rmI_eqc.  apply Bot_sl.
apply Botrule_I.  reflexivity.  apply dlNil.

- (* Imp *) eapply derI.
+ eapply (@fextI _ _ _ [_] []).  eapply rmI_eqc.
apply ImpR_nc'.  reflexivity.
+ apply dersrec_singleI.  eapply derI.
++ eapply (@fextI _ _ _ [] [A1]).  eapply rmI_eqc.
eapply ImpL_nc'. reflexivity.
++ apply dlCons.
+++ apply (fer_der [Imp A1 A2] []) in IHA1.
rewrite app_nil_r in IHA1. exact IHA1.
+++ apply dersrec_singleI. apply (fer_der [] [A1] IHA2).

- (* And *) eapply derI. 
+ apply rsub_fer.  eapply lrls_nc.  eapply rmI_eqc.
apply AndL_sl.  apply AndLrule_I.  reflexivity.  
+ simpl.  apply dersrec_singleI. eapply derI.
++ eapply (@fextI _ _ _ [A1 ; A2] []).  eapply rmI_eqc.
eapply rrls_nc.  apply rmI.
apply AndR_sr.  apply AndRrule_I.  reflexivity.  
++ simpl. unfold fmlsext. simpl.  apply dlCons.
+++ apply (fer_der [] [A2] IHA1).
+++ apply dersrec_singleI.
apply (fer_der [A1] []) in IHA2.
rewrite app_nil_r in IHA2. exact IHA2.

- (* Or *) eapply derI. 
+ apply rsub_fer.  eapply lrls_nc.  eapply rmI_eq.
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

Print Implicit idrule_der_lj.

Lemma fer_Id V A ant : InT A ant -> fst_ext_rls (@Idrule V A) [] (ant, A).
Proof. intro ia. apply InT_split in ia.  cD. subst.
eapply fextI_eq'. apply Idrule_I. reflexivity. reflexivity. Qed.

Lemma InT_der_LJ V A ant : InT A ant -> derrec (@LJrules V) emptyT (ant, A).
Proof. intro ia.  apply InT_split in ia.  cD. subst.
  exact (fer_der _ _ (idrule_der_lj A)). Qed.

(* to prove Ail rules in LJ *)
Lemma LJ_ImpL_Or1 V B C D :
  derrec (@LJrules V) emptyT ([Imp (Or C D) B], Imp C B).
Proof.  eapply derI.  eapply (@fextI _ _ _ []).
eapply rmI_eqc.  apply ImpR_nc'.  reflexivity.
apply dersrec_singleI.  simpl.
eapply derI. eapply (@fextI _ _ _ [C] []).  eapply rmI_eqc.
eapply ImpL_nc'.  reflexivity.
simpl. apply dlCons.
eapply derI.  eapply (@fextI _ _ _ []).
eapply rmI_eqc.  apply rrls_nc'. apply OrR1_sr. apply OrR1rule_I.
simpl. unfold fmlsext. simpl.  reflexivity.
apply dersrec_singleI. apply InT_der_LJ. solve_InT.
apply dersrec_singleI. apply InT_der_LJ. solve_InT.
Qed.

Lemma LJ_ImpL_Or2 V B C D :
  derrec (@LJrules V) emptyT ([Imp (Or C D) B], Imp D B).
Proof.  eapply derI.  eapply (@fextI _ _ _ []).
eapply rmI_eqc.  apply ImpR_nc'.  reflexivity.
apply dersrec_singleI.  simpl.
eapply derI. eapply (@fextI _ _ _ [D] []).  eapply rmI_eqc.
eapply ImpL_nc'.  reflexivity.
simpl. apply dlCons.
eapply derI.  eapply (@fextI _ _ _ []).
eapply rmI_eqc.  apply rrls_nc'. apply OrR2_sr. apply OrR2rule_I.
simpl. unfold fmlsext. simpl.  reflexivity.
apply dersrec_singleI. apply InT_der_LJ. solve_InT.
apply dersrec_singleI. apply InT_der_LJ. solve_InT.
Qed.

Lemma LJ_ImpL_And V B C D :
  derrec (@LJrules V) emptyT ([Imp (And C D) B], Imp C (Imp D B)).
Proof.  eapply derI.  eapply (@fextI _ _ _ []).
eapply rmI_eqc.  apply ImpR_nc'.  reflexivity.
apply dersrec_singleI.  simpl.
eapply derI.  eapply (@fextI _ _ _ []). 
eapply rmI_eqc.  apply ImpR_nc'.
simpl. unfold fmlsext. simpl.  reflexivity.
apply dersrec_singleI.  unfold fmlsext. simpl.
eapply derI. eapply (@fextI _ _ _ [D; C] []).  eapply rmI_eqc.
eapply ImpL_nc'.  reflexivity.
simpl. apply dlCons.
eapply derI.  eapply (@fextI _ _ _ []).
eapply rmI_eqc.  apply rrls_nc'. apply AndR_sr. apply AndRrule_I.
simpl. unfold fmlsext. simpl.  reflexivity.
simpl. apply dlCons.  apply InT_der_LJ. solve_InT.
apply dersrec_singleI.  apply InT_der_LJ. solve_InT.
apply dersrec_singleI.  apply InT_der_LJ. solve_InT.
Qed.

Lemma LJ_II V B C D :
  derrec (@LJrules V) emptyT ([Imp (Imp C D) B ; C], Imp D B).
Proof.  eapply derI.  eapply (@fextI _ _ _ []).
eapply rmI_eqc.  apply ImpR_nc'.  reflexivity.
apply dersrec_singleI.  simpl.
eapply derI. eapply (@fextI _ _ _ [D] [C]).  eapply rmI_eqc.
eapply ImpL_nc'.  reflexivity.
simpl. unfold fmlsext. simpl. apply dlCons.
eapply derI.  eapply (@fextI _ _ _ []).
eapply rmI_eqc.  apply ImpR_nc'.  reflexivity.
simpl. apply dersrec_singleI.  apply InT_der_LJ. solve_InT.
apply dersrec_singleI.  apply InT_der_LJ. solve_InT.
Qed.

(** exchange - largely copied from ../modal/k4_exch.v **)
(* properties can exchange adjacent sublists, and resulting sequent
  is derivable (not conditional on unexchanged version being derivable) *)

Print Implicit exchL_std_rule.

(* exchange for LJ system *)
Lemma exchL_lj: forall V concl,
  derrec (@LJrules V) emptyT concl ->
     forall concl', fst_rel (@swapped _) concl concl' ->
    derrec (@LJrules V) emptyT concl'.
Proof. unfold LJrules. intro. apply der_trf.
apply exchL_std_rule. apply LJnc_seL. Qed.

(* exchange for LJA system *)
Lemma exchL_lja: forall V concl,
  derrec (@LJArules V) emptyT concl ->
     forall concl', fst_rel (@swapped _) concl concl' ->
    derrec (@LJArules V) emptyT concl'.
Proof. unfold LJArules. intro. apply der_trf.
apply exchL_std_rule. apply LJAnc_seL. Qed.

Print Implicit exchL_lja.

(* insertion for LJ, LJA systems *)
Definition insL_lj V cl cr mid G := @gen_insL _ _ _ cl cr mid G (@LJnc_seL V).
Definition insL_lja V cl cr mid G := @gen_insL _ _ _ cl cr mid G (@LJAnc_seL V).

(* atom rule derivable in LJ *)
Lemma lj_der_atom V ps c G : 
  rlsmap (flip pair G) (@ImpL_atom_rule V) ps c -> derl LJrules ps c.
Proof. intro r. destruct r. destruct i. simpl.
eapply dtderI.  eapply (@fextI _ _ _ [] [_]).  eapply rmI_eqc.
eapply ImpL_nc'.  reflexivity.
simpl. unfold fmlsext. simpl.  eapply (@dtCons _ _ []).
apply derrec_nil_derl.  apply InT_der_LJ. solve_InT.
eapply (@dtCons _ _ [_]). apply asmI. apply dtNil.
Qed.
