
(* all rules for LNSKt* *)

Require Import ssreflect.
Require Import Omega.

Require Import gen.
Require Import ddP.
Require Import List_lemmasP.
Require Import lntP.
Require Import lntacsP.
Require Import lntmtacsP.
Require Import lntbRP.
Require Import lntb1LP.
Require Import lntb2LP.
Require Import lntlsP.
Require Import lntrsP.

Set Implicit Arguments.

Inductive EW_rule (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | EW : forall H K d, EW_rule [[]] [(pair H K, d)].

(* proofs for EW rule, which simply adds a sequent *)
Lemma gen_swapR_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. subst. (* keep drs in this case *)

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_swapR_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacDe ; subst ; rewrite -> ?app_nil_r in *. 

- inversion sppc ; subst ; clear sppc.

+ derIrs rs.
* apply NSlclctxt.  apply EW.
* apply drs.

- exchL2 rs sppc acm swap.

- inversion sppc ; subst ; clear sppc.
acacDe ; subst ; rewrite -> ?app_nil_r in *.
derIrs rs.
+ apply NSlclctxt.  apply EW.
+ apply drs.

Qed.

Lemma gen_swapL_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. subst. (* keep drs in this case *)

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacDe ; subst ; rewrite -> ?app_nil_r in *. 

- inversion sppc ; subst ; clear sppc.

+ derIrs rs.
* apply NSlclctxt.  apply EW.
* apply drs.

- exchL2 rs sppc acm swap.

- inversion sppc ; subst ; clear sppc.
acacDe ; subst ; rewrite -> ?app_nil_r in *.
derIrs rs.
+ apply NSlclctxt.  apply EW.
+ apply drs.

Qed.

Check gen_swapL_step_EW_lc.
Check gen_swapR_step_EW_lc.

(* at present this allows any context on both sides, within a sequent,
  and propositional rules don't copy principal formula into premises *)
Inductive LNSKt_rules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | b2r : forall ps c, nslclrule (@b2rrules V) ps c -> LNSKt_rules ps c
  | b1r : forall ps c, nslclrule (@b1rrules V) ps c -> LNSKt_rules ps c
  | b2l : forall ps c, nslclrule (@b2lrules V) ps c -> LNSKt_rules ps c
  | b1l : forall ps c, nslclrule (@b1lrules V) ps c -> LNSKt_rules ps c
  | nEW : forall ps c, nslclrule (@EW_rule V) ps c -> LNSKt_rules ps c
  | prop : forall ps c, 
    nslcrule (seqrule (@princrule_pfc V)) ps c -> LNSKt_rules ps c.

Ltac egx g := eapply g ; [>
  reflexivity | eassumption | assumption | assumption | ].

(* note, we don't yet have the weakening rule
  (ie EW, which adds an extra nested sequent,
  and princrule is in fact for different propositional rules *)
Lemma LNSKt_exchR: forall (V : Set) ns
  (D : derrec (@LNSKt_rules V) (fun _ => False) ns),
      can_gen_swapR (@LNSKt_rules V) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H ; subst ; [> pose gen_swapR_step_b2R_lc 
  | pose gen_swapR_step_b1R_lc
  | pose gen_swapR_step_b2L_lc
  | pose gen_swapR_step_b1L_lc
  | pose gen_swapR_step_EW_lc
  | pose gen_swapR_step_pr_lc ] ; 
unfold gen_swapR_step in g ; egx g ;
  clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.

Qed.

Lemma LNSKt_exchL: forall (V : Set) ns
  (D : derrec (@LNSKt_rules V) (fun _ => False) ns),
      can_gen_swapL (@LNSKt_rules V) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H ; subst ; [> pose gen_swapL_step_b2R_lc 
  | pose gen_swapL_step_b1R_lc
  | pose gen_swapL_step_b2L_lc
  | pose gen_swapL_step_b1L_lc
  | pose gen_swapL_step_EW_lc
  | pose gen_swapL_step_pr_lc ] ; 
unfold gen_swapL_step in g ; egx g ;
  clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.

Qed.

Check LNSKt_exchR.
Check LNSKt_exchL.


