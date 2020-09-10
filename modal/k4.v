
 
(* K4 modal logic, using lists of formulae *)
(* weakening *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.

Test Universe Polymorphism. (* NB Set this causes errors *)
Test Polymorphic Inductive Cumulativity.
(* see
https://coq.inria.fr/distrib/current/refman/addendum/universe-polymorphism.html
*)
Test Printing All.
Test Printing Universes.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../tense-lns".
Require Import gen. 
Require Import genT.
Require Import ddT.
Require Import gstep.
Require Import gen_ext.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import lntT.
Require Import lntacsT.

(** * Definitions

definition of Propositional Formulas*)

(* already in ~/coq/lnt/tense-logic-in-Coq/lntT.v 

Inductive PropF (V : Type): Type :=
 | Var : V -> PropF V
 | Bot : PropF V
 | Imp : PropF V -> PropF V -> PropF V
(*
 | Not : PropF V -> PropF V
 | And : PropF V -> PropF V -> PropF V
 | Or : PropF V -> PropF V -> PropF V
 | BBox : PropF V -> PropF V
 | BDia : PropF V -> PropF V
*)
 | WBox : PropF V -> PropF V
 | WDia : PropF V -> PropF V
.
*)

(* already in ~/coq/lnt/tense-logic-in-Coq/lntT.v

Definition rel W := prod W W.

Definition trf W := W -> W.
*)

Inductive isubf V : PropF V -> PropF V -> Type :=
  | Imp_subL : forall A B, isubf A (Imp A B)
  | Imp_subR : forall A B, isubf B (Imp A B)
  | WBox_sub : forall A, isubf A (WBox A)
  .

Lemma AccT_isubf: forall V f, AccT (@isubf V) f.
Proof. induction f ; apply AccT_intro ; intros ; inversion H ; clear H ; 
  subst ; assumption. Qed.

(* two-sided sequent of lists of (eg) formulae *)
Definition Seql W := rel (list W).

(* two-sided sequent of lists of formulae *)
Definition Seqlf V := Seql (PropF V).

(* already in ~/coq/lnt/tense-logic-in-Coq/lntT.v
(* we may also want to refer to rules individually *)
Inductive Idrule V : rlsT (Seqlf V) :=
  | Idrule_I : forall A, Idrule [] (pair [A] [A]).

(* propositional version of axiom rule *)
Inductive Idrule_p V : rlsT (Seqlf V) :=
  | Idrule_p_I : forall p, Idrule_p [] (pair [Var p] [Var p]).

Inductive Botrule V : rlsT (Seqlf V) :=
  | Botrule_I : Botrule [] (pair [Bot V] []).

Inductive ImpLrule V : rlsT (Seqlf V) :=
  | ImpLrule_I : forall A B,
    ImpLrule [pair [B] [] ; pair [] [A]] (pair [Imp A B] []).

Inductive ImpRrule V : rlsT (Seqlf V) :=
  | ImpRrule_I : forall A B, ImpRrule [pair [A] [B]] (pair [] [Imp A B]).
*)

(* shadows definition in ~/coq/lnt/tense-logic-in-Coq/lntT.v *)
Inductive princrule {V} : rlsT (Seqlf V) :=
  | Id : forall ps c, Idrule ps c -> princrule ps c
  | ImpR : forall ps c, ImpRrule ps c -> princrule ps c
  | ImpL : forall ps c, ImpLrule ps c -> princrule ps c
  | BotL : forall ps c, Botrule ps c -> princrule ps c
  .

(* expanded cases in princrule *)
Definition ImpLe V A B := ImpL (@ImpLrule_I V A B).
Definition ImpRe V A B := ImpR (@ImpRrule_I V A B).
Definition BotLe V := BotL (@Botrule_I V).
Definition Ide V A := Id (@Idrule_I (PropF V) A).

Definition rsId {V : Set} := rsubI _ _ (@Id V).
Definition rsImpL {V : Set} := rsubI _ _ (@ImpL V).
Definition rsImpR {V : Set} := rsubI _ _ (@ImpR V).
Definition rsBotL {V : Set} := rsubI _ _ (@BotL V).

Definition rsseqImpL {V : Set} := seqrule_mono (@rsImpL V).
Definition rsseqImpR {V : Set} := seqrule_mono (@rsImpR V).
Definition rsseqBotL {V : Set} := seqrule_mono (@rsBotL V).

(* getting rules invertible *)
Inductive ImpRinv {V} : relationT (Seqlf V) :=
  | ImpRinv_I : forall C D, ImpRinv (pair [] [Imp C D]) (pair [C] [D]).
Inductive ImpLinv2 {V} : relationT (Seqlf V) :=
  | ImpLinv2_I : forall C D, ImpLinv2 (pair [Imp C D] []) (pair [] [C]).
Inductive ImpLinv1 {V} : relationT (Seqlf V) :=
  | ImpLinv1_I : forall C D, ImpLinv1 (pair [Imp C D] []) (pair [D] []).

(* a sequent containing exactly one formula *)
Inductive one_fml W : rel (list W) -> Type := 
  | singL : forall a : W, one_fml ([a], []) 
  | singR : forall a : W, one_fml ([], [a]).
  
(* relation from sequents containing exactly one formula *)
Inductive from_one_fml W : relationT (rel (list W)) := 
  | fofI : forall f t, one_fml f -> from_one_fml f t.

(* see ~/coq/lnt/tense-logic-in-Coq/lnt.v for seqext *)

(* as seqrel, but just one side of sequent *)
Inductive ssrel W R : relationT (list W) :=
  | Ctxt_relI : forall c c' Φ Ψ, R c c' ->
    ssrel R (Φ ++ c ++ Ψ) (Φ ++ c' ++ Ψ).

(* for a simple relation between sequents *)
(* putting Polymorphic here causes an error in the line 
apply (Sctxt_relI_eq _ [] [Imp C D] [C] [D] 
  (Φ1 ++ A :: H) Φ3 (Ψ1 ++ B :: H2) Ψ3).
  of the proof of can_trf_ImpRinv_ImpR
Polymorphic
Cumulative
  *)
Inductive seqrel W R : relationT (Seql W) :=
  | Sctxt_relI : forall c c' Φ1 Φ2 Ψ1 Ψ2, R c c' ->
    seqrel R (seqext Φ1 Φ2 Ψ1 Ψ2 c) (seqext Φ1 Φ2 Ψ1 Ψ2 c').

Lemma Sctxt_relI_e W R (X Y U V Φ1 Φ2 Ψ1 Ψ2 : list W): R (X, Y) (U, V) ->
  seqrel R (Φ1 ++ X ++ Φ2, Ψ1 ++ Y ++ Ψ2) (Φ1 ++ U ++ Φ2, Ψ1 ++ V ++ Ψ2).
Proof. rewrite - !seqext_def. apply Sctxt_relI. Qed.

Lemma seqrel_mono W (R R' : relationT (Seql W)) :
  rsub R R' -> rsub (seqrel R) (seqrel R').
Proof. unfold rsub. intros. destruct X0. apply X in r.
  apply Sctxt_relI. assumption. Qed.  

Definition seqrel_mono' W R R' rs := rsubD (@seqrel_mono W R R' rs).

Lemma seqrel_req W (R R' : relationT (rel (list W))):
  req R R' -> req (seqrel R) (seqrel R').
Proof. unfold req. intros. cD. split ; apply seqrel_mono ; assumption. Qed.

Lemma seqrel_seqrel' W R (p q : rel (list W)): 
  seqrel (seqrel R) p q -> seqrel R p q.
Proof. intro ssr. destruct ssr. destruct s.
rewrite !seqext_seqext. apply Sctxt_relI. exact r. Qed.

Lemma seqrel_id' W R (p q : rel (list W)): R p q -> seqrel R p q.
Proof. intro rpq. apply (Sctxt_relI R p q [] [] [] []) in rpq.
unfold seqext in rpq. destruct p. destruct q. 
simpl in rpq. rewrite ?app_nil_r in rpq. exact rpq. Qed.

Definition seqrel_seqrel W R := rsubI _ _ (@seqrel_seqrel' W R).
Definition seqrel_id W R := rsubI _ _ (@seqrel_id' W R).

Lemma Sctxt_relI_eq W R (X Y U V Φ1 Φ2 Ψ1 Ψ2 : list W) seq1 seq2: 
  R (X, Y) (U, V) -> seq1 = (Φ1 ++ X ++ Φ2, Ψ1 ++ Y ++ Ψ2) ->
  seq2 = (Φ1 ++ U ++ Φ2, Ψ1 ++ V ++ Ψ2) -> seqrel R seq1 seq2.
Proof. intros. subst. apply Sctxt_relI_e. assumption. Qed.

(* extend conclusion only *)
(* this isn't enough to derive any weakened version of box rule conclusion, eg
  X, []A, Y, [](A->B), Z |- []B *)
Inductive cerule W (pr : rlsT (Seql W)) : rlsT (Seql W) :=
  | Cctxt : forall ps c Φ1 Φ2 Ψ1 Ψ2, pr ps c ->
    cerule pr ps (seqext Φ1 Φ2 Ψ1 Ψ2 c).

(* this rule uses gen_ext on both sides of |-, even though the only rule
  using it (Box rule) has singletons on the right *)
Inductive cgerule W (pr : rlsT (Seql W)) : rlsT (Seql W) :=
  | CGctxt : forall ps ca cs cea ces, pr ps (ca, cs) ->
    gen_ext ca cea -> gen_ext cs ces -> cgerule pr ps (cea, ces).

Lemma Cctxt_e: forall (W : Type) (pr : rlsT (Seql W)) (ps : list (Seql W)) 
       (ca cs : list W) (Φ1 Φ2 Ψ1 Ψ2 : list W),
       pr ps (ca, cs) -> cerule pr ps (Φ1 ++ ca ++ Φ2, Ψ1 ++ cs ++ Ψ2).
Proof. intros. eapply Cctxt in X. unfold seqext in X. exact X. Qed.

Lemma cgerule_id (W : Type) (pr : rlsT (rel (list W))) :
  forall ps c, pr ps c -> cgerule pr ps c.
Proof. intros. destruct c as [ca cs].
apply (CGctxt _ _ X) ; apply gen_ext_refl. Qed.

Inductive trivrule {W} : rlsT W :=
  | trivrule_I : forall c, trivrule [c] c.

Inductive K4prrule {V} : rlsT (Seqlf V) :=
  | K4prrule_I : forall Gam phi, K4prrule 
    [pair (map (@WBox V) Gam ++ Gam) [phi]]
    (pair (map (@WBox V) Gam) [WBox phi]).

Inductive K4rules {V} : rlsT (Seqlf V) :=
  | K4_I : forall ps c, cgerule (@K4prrule V) ps c -> K4rules ps c
  | cpl_I : forall ps c, seqrule (@princrule V) ps c -> K4rules ps c
  .

Inductive K4rules_sw {V} : rlsT (Seqlf V) :=
  | K4_sw_I : forall ps c, K4prrule ps c -> K4rules_sw ps c
  | cplsw_I : forall ps c, seqrule (@princrule V) ps c -> K4rules_sw ps c
  | K4_wk_I : forall ps c, cgerule (@trivrule _) ps c -> K4rules_sw ps c
  .

Print K4rules.  Print K4rules_sw.

Definition rsK4 {V : Set} := rsubI _ _ (@K4_I V).
Definition rscpl {V : Set} := rsubI _ _ (@cpl_I V).
Definition rsK4_sw {V : Set} := rsubI _ _ (@K4_sw_I V).
Definition rscplsw {V : Set} := rsubI _ _ (@cplsw_I V).
Definition rsK4_wk {V : Set} := rsubI _ _ (@K4_wk_I V).

Lemma seqext_seqext: forall V (Γ1 Γ2 Δ1 Δ2 Φ1 Φ2 Ψ1 Ψ2 : list V) seq, 
  seqext Γ1 Γ2 Δ1 Δ2 (seqext Φ1 Φ2 Ψ1 Ψ2 seq) = 
  seqext (Γ1 ++ Φ1) (Φ2 ++ Γ2) (Δ1 ++ Ψ1) (Ψ2 ++ Δ2) seq.
Proof. intros. unfold seqext. destruct seq.
rewrite !app_assoc. reflexivity. Qed.

(* simple version of weakening, new stuff added at beginning or end *)
Definition wk_valid V rules (seq : Seql V) :=
  forall Γ1 Γ2 Δ1 Δ2, derrec rules (@emptyT _) (seqext Γ1 Γ2 Δ1 Δ2 seq).

Definition can_wk V rules seq :=
  derrec rules (@emptyT (Seql V)) seq -> @wk_valid V rules seq.

Lemma weakening: forall V seq, can_wk (@K4rules V) seq.
Proof. unfold can_wk. intros. 
eapply derrec_all_rect in X. exact X.
intros. contradiction H. 
intros ps concl k4r dsps fwk.  destruct k4r.  destruct c0.  
inversion k. clear k. clear fwk. subst. unfold wk_valid.
intros. unfold seqext.
eapply derI. apply K4_I. eapply CGctxt. apply K4prrule_I. 
apply gen_ext_appL.  apply gen_ext_appR. eassumption.
apply gen_ext_appL.  apply gen_ext_appR. eassumption.
assumption.  
(* now propositional rules *)
destruct s. unfold wk_valid.
intros. rewrite seqext_seqext.

eapply derI. apply cpl_I. apply Sctxt. exact p. clear dsps.
apply dersrecI_forall. intros c0 incm.
apply InT_mapE in incm. cD.
eapply ForallTD_forall in fwk. 
2: apply InT_map.  2: exact incm1.
unfold wk_valid in fwk.  rewrite - incm0.  
rewrite - seqext_seqext. apply fwk. Qed.

Check weakening.

Lemma prod_uncurry_def: forall A B C (f : prod A B -> C) x y,
  prod_uncurry f x y = f (x, y).
Proof. unfold prod_uncurry. tauto. Qed.

Lemma prod_curry_def: forall A B C (g : A -> B -> C) x y,
  prod_curry g (x, y) = g x y.
Proof. unfold prod_curry. tauto. Qed.

Definition prod_curryD A B g x y := iffD1 (@prod_curry_def A B Type g x y).
Definition prod_curryI A B g x y := iffD2 (@prod_curry_def A B Type g x y).
Definition prod_uncurryD A B f x y := iffD1 (@prod_uncurry_def A B Type f x y).
Definition prod_uncurryI A B f x y := iffD2 (@prod_uncurry_def A B Type f x y).

(* this definition replaces Type by Prop *)
Inductive singleton_rel U V u v : U -> V -> Type :=
  | srI : @singleton_rel U V u v u v : Type.

Check singleton_rel : forall U V : Type, U -> V -> U -> V -> Type.

Lemma rsub_sing_rel U V (u : U) (v : V) rules:
  rules u v -> rsub (singleton_rel u v) rules.
Proof. intro ruv. unfold rsub. intros u0 v0 sr. destruct sr. assumption. Qed.

Inductive srr U V (rules : U -> V -> Type) : ((U -> V -> Type) -> Type) :=
  | srrI : forall u v, rules u v -> @srr U V rules (singleton_rel u v).

(* a rule set is equal (req) to the union of the singleton rule sets *)
Lemma srr_eq U V rules: req rules (rUnion (@srr U V rules)).
Proof. unfold req. unfold rsub. split ; intros.
eapply rUnI. eapply srrI. apply X. apply srI.
inversion X. destruct X0. destruct X1. apply r. Qed.

Inductive is_sr_of W rr : relationT (Seql W) -> Type :=
  is_srI : forall rules, rr rules -> @is_sr_of W rr (seqrel rules).

Inductive image U V (f : U -> V) p fx : Type :=
  | imI : forall x, p x -> fx = f x -> @image U V f p fx.

Inductive image2 U V W (f : U -> V -> W) p fuv : Type :=
  | im2I : forall u v, p u v -> fuv = f u v -> @image2 U V W f p fuv.

(* this one causes universe inconsistency (between Type and Prop)
Lemma req_sr2 U V rules: req (rUnion (image2 (@singleton_rel U V) rules)) rules.
*)
Lemma req_sr2 U V rules: req (rUnion (image2 
  (@singleton_rel U V : U -> V -> U -> V -> Type) rules)) rules.
Proof. unfold req. unfold rsub. split ; intros *.
- intros rui.
inversion rui as [r isr ruv].
destruct isr. subst. inversion ruv. clear ruv. subst. assumption.
- intros ruv. eapply rUnI. 
eapply im2I. apply ruv. reflexivity. apply srI. Qed.

Inductive Union U (rr : (U -> Type) -> Type) x : Type :=
  UnI : forall r, rr r -> r x -> Union rr x.

(* this gave universe inconsistency without rUnion, rUnI Polymorphic *)
Lemma seqrel_rUnion W rr : req (seqrel (rUnion rr)) (rUnion (@is_sr_of W rr)). 
Proof. unfold req. unfold rsub. split ; intros *.
intro srr.  destruct srr. destruct r.
eapply (rUnI (is_sr_of rr)).  eapply (is_srI rr r). exact r0.
apply (Sctxt_relI r). exact r1.
intro rui. destruct rui. destruct i.
eapply seqrel_mono'. 2 : eassumption.
apply rsubI. intros. eapply rUnI ; eassumption. Qed.

Lemma rsr_rusr W rules: req (seqrel rules) (rUnion (@is_sr_of W (srr rules))).
Proof. eapply req_trans. eapply seqrel_req. apply srr_eq.
apply seqrel_rUnion. Qed.

Lemma seq_ss W (A B Ac Bc Ar Br Arc Brc : list W):
  iffT (prod (ssrel (singleton_rel A Ar) Ac Arc)
    (ssrel (singleton_rel B Br) Bc Brc))
  (seqrel (singleton_rel (A, B) (Ar, Br)) (Ac, Bc) (Arc, Brc)).
Proof. unfold iffT. split ; intros ; cD.
- destruct X. destruct X0.  destruct s. destruct s0.
eapply Sctxt_relI_eq.  apply srI. reflexivity.  reflexivity.
- inversion X. inversion H1. subst. 
unfold seqext in H.  unfold seqext in H0. 
injection H as .  injection H0 as . clear H1. subst.
split ; apply Ctxt_relI ; apply srI. Qed.

Definition seq_ssD W A B Ac Bc Ar Br Arc Brc x y :=
  iffT_D1 (@seq_ss W A B Ac Bc Ar Br Arc Brc) (x, y).
Definition seq_ssI W A B Ac Bc Ar Br Arc Brc :=
  iffT_D2 (@seq_ss W A B Ac Bc Ar Br Arc Brc).

(* note, not a safe rule! *)
Lemma ss_appL W R (A B C : list W): ssrel R A B -> ssrel R (C ++ A) (C ++ B).
Proof. intro ss. destruct ss.
rewrite !(app_assoc C). apply Ctxt_relI. exact r. Qed.
  
Lemma ss_appLe1' W R (B C : list W): ssrel R [] B -> ssrel R C (C ++ B).
Proof. intro ss. eapply ss_appL in ss. 
rewrite app_nil_r in ss. apply ss. Qed.

Lemma ss_appLe2' W R (A C : list W): ssrel R A [] -> ssrel R (C ++ A) C.
Proof. intro ss. eapply ss_appL in ss. 
rewrite app_nil_r in ss. apply ss. Qed.

Lemma ss_appR W R (A B C : list W): ssrel R A B -> ssrel R (A ++ C) (B ++ C).
Proof. intro ss. destruct ss.
rewrite - !app_assoc. apply Ctxt_relI. exact r. Qed.

Lemma ss_appRe1' W R (B C : list W): ssrel R [] B -> ssrel R C (B ++ C).
Proof. intro ss. eapply ss_appR in ss.  simpl in ss. apply ss. Qed.

Lemma ss_appRe2' W R (A C : list W): ssrel R A [] -> ssrel R (A ++ C) C.
Proof. intro ss. eapply ss_appR in ss.  simpl in ss. apply ss. Qed.

Lemma ss_cons W R A B (x : W): ssrel R A B -> ssrel R (x :: A) (x :: B).
Proof. intro ss. apply (ss_appL [x]) in ss.  simpl in ss. apply ss. Qed.

Lemma ss_app_conse1' W R C (x : W): ssrel R [] [x] -> ssrel R C (x :: C).
Proof. intro ss. eapply ss_appR in ss.  simpl in ss. apply ss. Qed.

Lemma ss_app_conse2' W R C (x : W): ssrel R [x] [] -> ssrel R (x :: C) C.
Proof. intro ss. eapply ss_appR in ss.  simpl in ss. apply ss. Qed.

Lemma ss_app_cons1 W R A C (x : W): ssrel R A [x] -> ssrel R (A ++ C) (x :: C).
Proof. intro ss. eapply ss_appR in ss.   apply ss. Qed.

Lemma ss_app_cons2 W R B C (x : W): ssrel R [x] B -> ssrel R (x :: C) (B ++ C).
Proof. intro ss. eapply ss_appR in ss.   apply ss. Qed.

Lemma ss_id W R (A B : list W): R A B -> ssrel R A B.
Proof. intro ss. apply (Ctxt_relI _ A B [] []) in ss.
simpl in ss. rewrite !app_nil_r in ss. exact ss. Qed.

Lemma ssrule_testL1 W pr ps (X ca cs : list W):
  seqrule pr ps (X ++ ca, cs) -> seqrule pr ps (X ++ ca, cs).
Proof. tauto. Qed.

Lemma ssrule_testL2 W pr ps (X ca cs : list W):
  seqrule pr ps (ca, X ++ cs) -> seqrule pr ps (ca, X ++ cs).
Proof. tauto. Qed.

Lemma ssrule_testR1 W pr ps (X ca cs : list W):
  seqrule pr ps (ca ++ X, cs) -> seqrule pr ps (ca ++ X, cs). 
Proof. tauto. Qed.

Lemma ssrule_testR2 W pr ps (X ca cs : list W):
  seqrule pr ps (ca, cs ++ X) -> seqrule pr ps (ca, cs ++ X). 
Proof. tauto. Qed.

Ltac ssratac sqr := intro sqr ; eapply Sctxt_eq in sqr ; [> | | | reflexivity] ;
[> apply seqrule_seqrule ; apply sqr |
  simpl ; rewrite ?app_nil_r ; reflexivity |
  simpl ; rewrite ?app_nil_r ; reflexivity ].

Lemma ssrule_appL1 W pr ps (ca cs X : list W): seqrule pr ps (ca, cs) ->
  seqrule pr (map (seqext X [] [] []) ps) (X ++ ca, cs).
Proof. ssratac sqr. Qed.

Lemma ssrule_appR1 W pr ps (ca cs X : list W): seqrule pr ps (ca, cs) ->
  seqrule pr (map (seqext [] X [] []) ps) (ca ++ X, cs).
Proof. ssratac sqr. Qed.

Lemma ssrule_appR1c W pr ps c (cs X : list W): seqrule pr ps ([c], cs) ->
  seqrule pr (map (seqext [] X [] []) ps) (c :: X, cs).
Proof. intro sqr. rewrite cons_singleton. apply ssrule_appR1. exact sqr. Qed.

Lemma ssrule_appL2 W pr ps (ca cs X : list W): seqrule pr ps (ca, cs) ->
  seqrule pr (map (seqext [] [] X []) ps) (ca, X ++ cs).
Proof. ssratac sqr. Qed.

Lemma ssrule_appR2 W pr ps (ca cs X : list W): seqrule pr ps (ca, cs) ->
  seqrule pr (map (seqext [] [] [] X) ps) (ca, cs ++ X).
Proof. ssratac sqr. Qed.

Lemma ssrule_appR2c W pr ps ca c (X : list W): seqrule pr ps (ca, [c]) ->
  seqrule pr (map (seqext [] [] [] X) ps) (ca, c :: X).
Proof. intro sqr. rewrite cons_singleton. apply ssrule_appR2. exact sqr. Qed.

Definition ss_appLe1 W R B C x := @ss_appLe1' W R B C (ss_id _ _ _ x).
Definition ss_appLe2 W R A C x := @ss_appLe2' W R A C (ss_id _ _ _ x).
Definition ss_appRe1 W R B C x := @ss_appRe1' W R B C (ss_id _ _ _ x).
Definition ss_appRe2 W R A C x := @ss_appRe2' W R A C (ss_id _ _ _ x).
Definition ss_app_conse1 W R B C x := @ss_app_conse1' W R B C (ss_id _ _ _ x).
Definition ss_app_conse2 W R A C x := @ss_app_conse2' W R A C (ss_id _ _ _ x).

Lemma sqr_appL2 W pr (ca cs da ds X : list W): seqrel pr (da, ds) (ca, cs) ->
  seqrel pr (da, X ++ ds) (ca, X ++ cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] X []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_appR2 W pr (ca cs da ds X : list W): seqrel pr (da, ds) (ca, cs) ->
  seqrel pr (da, ds ++ X) (ca, cs ++ X).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] [] X) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_appL1 W pr (ca cs da ds X : list W): seqrel pr (da, ds) (ca, cs) ->
  seqrel pr (X ++ da, ds) (X ++ ca, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ X [] [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_appR1 W pr (ca cs da ds X : list W): seqrel pr (da, ds) (ca, cs) ->
  seqrel pr (da ++ X, ds) (ca ++ X, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] X [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_cons_na2 W pr (ca da X : list W) x:
  seqrel pr (da, [x]) (ca, []) -> seqrel pr (da, x :: X) (ca, X).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] [] X) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_na_cons2 W pr (ca da X : list W) x:
  seqrel pr (da, []) (ca, [x]) -> seqrel pr (da, X) (ca, x :: X).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] [] X) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_cons_na1 W pr (cs ds X : list W) x:
  seqrel pr ([x], ds) ([], cs) -> seqrel pr (x :: X, ds) (X, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] X [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_na_cons1 W pr (cs ds X : list W) x:
  seqrel pr ([], ds) ([x], cs) -> seqrel pr (X, ds) (x :: X, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] X [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_cons_app2 W pr (ca cs da X : list W) x:
  seqrel pr (da, [x]) (ca, cs) -> seqrel pr (da, x :: X) (ca, cs ++ X).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] [] X) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_app_cons2 W pr (ca da ds X : list W) x:
  seqrel pr (da, ds) (ca, [x]) -> seqrel pr (da, ds ++ X) (ca, x :: X).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] [] X) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_cons_app1 W pr (ca cs ds X : list W) x:
  seqrel pr ([x], ds) (ca, cs) -> seqrel pr (x :: X, ds) (ca ++ X, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] X [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_app_cons1 W pr (cs da ds X : list W) x:
  seqrel pr (da, ds) ([x], cs) -> seqrel pr (da ++ X, ds) (x :: X, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] X [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_cons1 W pr (ca cs da ds : list W) x:
  seqrel pr (da, ds) (ca, cs) -> seqrel pr (x :: da, ds) (x :: ca, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [x] [] [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_cons2 W pr (ca cs da ds : list W) x:
  seqrel pr (da, ds) (ca, cs) -> seqrel pr (da, x :: ds) (ca, x :: cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] [x] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_nn1 W pr (cs ds X : list W):
  seqrel pr ([], ds) ([], cs) -> seqrel pr (X, ds) (X, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] X [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_nn2 W pr (ca da X : list W):
  seqrel pr (da, []) (ca, []) -> seqrel pr (da, X) (ca, X).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] [] X) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_cc1 W pr (cs ds X : list W) x y:
  seqrel pr ([x], ds) ([y], cs) -> seqrel pr (x :: X, ds) (y :: X, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] X [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_cc2 W pr (ca da X : list W) x y:
  seqrel pr (da, [x]) (ca, [y]) -> seqrel pr (da, x :: X) (ca, y :: X).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] [] X) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_saL2 W pr (ca da cs X : list W):
  seqrel pr (da, []) (ca, cs) -> seqrel pr (da, X) (ca, X ++ cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] X []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_saR2 W pr (ca cs da X : list W):
  seqrel pr (da, []) (ca, cs) -> seqrel pr (da, X) (ca, cs ++ X).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] [] X) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_saL1 W pr (ca cs ds X : list W):
  seqrel pr ([], ds) (ca, cs) -> seqrel pr (X, ds) (X ++ ca, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ X [] [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_saR1 W pr (ca cs ds X : list W):
  seqrel pr ([], ds) (ca, cs) -> seqrel pr (X, ds) (ca ++ X, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] X [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_asL2 W pr (ca da ds X : list W):
  seqrel pr (da, ds) (ca, []) -> seqrel pr (da, X ++ ds) (ca, X).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] X []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_asR2 W pr (ca ds da X : list W):
  seqrel pr (da, ds) (ca, []) -> seqrel pr (da, ds ++ X) (ca, X).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] [] [] X) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_asL1 W pr (da cs ds X : list W):
  seqrel pr (da, ds) ([], cs) -> seqrel pr (X ++ da, ds) (X, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ X [] [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Lemma sqr_asR1 W pr (da cs ds X : list W):
  seqrel pr (da, ds) ([], cs) -> seqrel pr (da ++ X, ds) (X, cs).
Proof. intro sqr. apply seqrel_seqrel'.
apply (Sctxt_relI _ _ _ [] X [] []) in sqr.
unfold seqext in sqr. simpl in sqr. rewrite ?app_nil_r in sqr. exact sqr. Qed.

Definition gwk_valid V rules (ca cs : list V) := forall cea ces : list V,
  gen_ext ca cea -> gen_ext cs ces ->
  derrec rules (emptyT (X:=Seql V)) (cea, ces).

Definition can_gwk V rules ca cs :=
  derrec rules (@emptyT _) (ca, cs) -> @gwk_valid V rules ca cs.

Lemma princrule_sing_empty: forall X ps U S,
  @princrule X ps (U, S) -> prod (sing_empty U) (sing_empty S).
Proof.  intros *. intro pp. inversion pp ; subst ; rename_last q ;
  inversion q ; subst ; split ; (apply se_empty || apply se_single). Qed.

Lemma gen_weakening: forall V ca cs, can_gwk (@K4rules V) ca cs.
Proof. unfold can_gwk. intros. 
eapply derrec_all_rect in X. apply prod_curryD. exact X.
intros. contradiction H. 
intros ps concl k4r dps agwk.  destruct k4r. 
inversion c0 as [? ? ? ? ? k4 ga gs]. subst.  inversion k4. subst.
clear k4 c0. unfold prod_curry. unfold gwk_valid.
intros.  eapply derI. apply K4_I. eapply CGctxt. apply K4prrule_I. 
eapply gen_ext_trans ; eassumption.
eapply gen_ext_trans ; eassumption.
assumption.  

(* now propositional rules *)
destruct c. unfold prod_curry. inversion s. subst. clear s.
destruct c. unfold seqext in H1. inversion H1. subst. clear H1.
unfold gwk_valid.  intros cea ces gea ges. 

apply gen_ext_single in gea.  apply gen_ext_single in ges. cD. subst.
rewrite - seqext_def.
eapply derI. apply cpl_I. apply Sctxt. eassumption.
clear dps.
apply dersrecI_forall. intros c cin.
apply InT_mapE in cin. cD.
subst. destruct cin. unfold seqext.
eapply ForallTD_forall in agwk.
2 : apply InT_map.  2 : eassumption.
unfold prod_curry in agwk.
unfold seqext in agwk.
unfold gwk_valid in agwk.
apply agwk.  apply gen_ext_app.  apply gen_ext_app.
assumption. apply gen_ext_refl. assumption.
apply gen_ext_app.  apply gen_ext_app.
assumption. apply gen_ext_refl. assumption.
apply princrule_sing_empty in X0. tauto.
apply princrule_sing_empty in X0. tauto. Qed.

Check gen_weakening.

(* this should mean that the systems K4rules_sw and K4rules are equivalent *) 

Lemma der_k4_imp_sw V: forall ps c,
  derrec (@K4rules V) ps c -> derrec (@K4rules_sw V) ps c.
Proof. intro. apply derrec_all_rect. 
intros. apply (dpI _ _ _ X).
intros ps0 concl k4 drs allps.  clear drs. destruct k4.
- destruct c0. 
eapply derI. apply K4_wk_I. eapply CGctxt. apply trivrule_I.
eassumption.  eassumption.
apply dersrec_singleI. eapply derI. apply K4_sw_I. eassumption.
exact (dersrecI_all allps).
- eapply derI. apply (cplsw_I s).  exact (dersrecI_all allps). 
Qed.

Lemma der_k4_sw_imp V: forall c,
  derrec (@K4rules_sw V) (@emptyT _) c -> derrec (@K4rules V) (@emptyT _) c.
Proof. intro. apply derrec_all_rect. 
intros. destruct H.
intros ps concl k4 drs allps.  clear drs. destruct k4.
- eapply derI. apply K4_I. apply cgerule_id. apply k.
exact (dersrecI_all allps).
- eapply derI. apply cpl_I. apply s.
exact (dersrecI_all allps).
- destruct c1. inversion t. subst. clear t.
apply ForallT_singleD in allps.
apply gen_weakening in allps.
unfold gwk_valid in allps. apply allps ; assumption. Qed.

