Require Import ssreflect.
 
Require Import gen.
Require Import ddP.
Require Import List_lemmasP.
Require Import lntP lntacsP lntlsP lntbRP lntmtacsP.
Require Import lntb1LP lntb2LP.
Require Import lnt_weakeningP.
Require Import lntkt_exchP.
Require Import swappedP.


Inductive PropF_basic (V : Set) (A : PropF V) : Type :=
 | Var_basic p : A = Var p -> PropF_basic V A
 | Bot_basic : A = Bot V -> PropF_basic V A
 | Imp_basic B C : A = Imp B C -> PropF_basic V B -> PropF_basic V C -> PropF_basic V A.

Lemma LNSKt_gen_init : forall (V : Set) A ns,
    PropF_basic V A -> can_gen_init (@LNSKt_rules V) ns A.
Proof.
  induction A; unfold can_gen_init in *;
    intros ns Hprop G seq d Γ1 Γ2 Δ1 Δ2 Heq1 Heq2;
    inversion Hprop; subst; try discriminate.
  (* Id_pfc *)
  + eapply derI.
    apply prop. apply NSlcctxt_nil.
    rewrite <- seqext_def.
    apply Sctxt_nil. apply Id_pfc.
    apply dersrec_nil.
  (* BotL_pfc *)
  + eapply derI. apply prop.
    apply NSlcctxt_nil.
    rewrite <- (app_nil_l ([Bot V] ++ Δ2)).
    rewrite <- seqext_def.
    apply Sctxt_nil.  apply BotL_pfc.
    apply dersrec_nil.
  (* Imp *)
  + eapply derI. apply prop.
    apply NSlcctxt'.
    rewrite <- (app_nil_l ([Imp A1 A2] ++ Γ2)).
    rewrite <- seqext_def. eapply Sctxt.
    (* application of ImpR_pfc *)
    apply ImpR_pfc.  apply dlCons.
    eapply derI. apply prop.
    apply NSlcctxt'.  unfold seqext. 
    rewrite <- (app_nil_l ([Imp A1 A2;A2] ++ _)).
    rewrite (app_assoc Γ1).  rewrite <- seqext_def.
    eapply Sctxt.
    (* application of ImpL_pfc *)
    apply ImpL_pfc.
    inversion H; subst.
    apply dlCons;
    unfold nslcext;
    unfold seqext;
    list_assoc_r_single.
    assoc_mid ([C]).  rewrite (app_assoc Δ1).
    eapply IHA2; auto.
    apply dlCons.
    eapply IHA1; auto.
    all : apply dersrec_nil.
Qed.

Lemma LNSKt_gen_init_original : forall (V : Set),
  forall A G (d : dir) Γ1 Γ2 Δ1 Δ2,
    PropF_basic V A ->
    derrec (@LNSKt_rules V) (fun _ => False)
         (G ++ [(Γ1 ++ [A] ++ Γ2, Δ1 ++ [A] ++ Δ2, d)]).
Proof.
  induction A; intros G d Γ1 Γ2 Δ1 Δ2 Hprop;
    inversion Hprop; subst; try discriminate.
  (* Id_pfc *)
  + eapply derI.
    apply prop. apply NSlcctxt_nil.
    rewrite <- seqext_def.
    apply Sctxt_nil. apply Id_pfc.
    apply dersrec_nil.
  (* BotL_pfc *)
  + eapply derI. apply prop.
    apply NSlcctxt_nil.
    rewrite <- (app_nil_l ([Bot V] ++ Δ2)).
    rewrite <- seqext_def.
    apply Sctxt_nil.  apply BotL_pfc.
    apply dersrec_nil.
  (* Imp *)
  + eapply derI. apply prop.
    apply NSlcctxt'.
    rewrite <- (app_nil_l ([Imp A1 A2] ++ Γ2)).
    rewrite <- seqext_def. eapply Sctxt.
    (* application of ImpR_pfc *)
    apply ImpR_pfc.  apply dlCons.
    eapply derI. apply prop.
    apply NSlcctxt'.  unfold seqext. 
    rewrite <- (app_nil_l ([Imp A1 A2;A2] ++ _)).
    rewrite (app_assoc Γ1).  rewrite <- seqext_def.
    eapply Sctxt.
    (* application of ImpL_pfc *)
    apply ImpL_pfc.  apply dlCons;
    unfold nslcext;
    unfold seqext;
    list_assoc_r_single.
    assoc_mid ([A2]).  rewrite (app_assoc Δ1).
    eapply IHA2. inversion H. subst. auto.
    apply dlCons.
    eapply IHA1. inversion H. subst. auto.
    all : apply dersrec_nil.
Qed.