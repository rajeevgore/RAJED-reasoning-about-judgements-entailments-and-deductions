
(* all rules for LNSKt* *)

Require Import ssreflect.
Require Import Omega.

Require Import genT gen.
Require Import ddT.
Require Import List_lemmasT.
Require Import lntT.
Require Import lntacsT.
Require Import lntmtacsT.
Require Import lntbRT.
Require Import lntb1LT.
Require Import lntb2LT.
Require Import lntlsT.
Require Import lntrsT.

Set Implicit Arguments.

Inductive EW_rule (V : Set) : rlsT (list (rel (list (PropF V)) * dir)) :=
| EW : forall H K d, EW_rule [[]] [(pair H K, d)].

(* proofs for EW rule, which simply adds a sequent *)
Lemma gen_swapR_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. subst. (* keep drs in this case *)

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
eapply can_gen_swapR_imp_rev.
intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacDeT2 ; subst ; rewrite -> ?app_nil_r in *. 

- inversion sppc ; subst ; clear sppc.

+ derIrs rs.
* apply NSlclctxt.  apply EW.
* apply drs.

- exchL2T rs sppc acm swap.

- inversion sppc ; subst ; clear sppc.
acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
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
eapply can_gen_swapL_imp_rev.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacDeT2 ; subst ; rewrite -> ?app_nil_r in *. 

- inversion sppc ; subst ; clear sppc.

+ derIrs rs.
* apply NSlclctxt.  apply EW.
* apply drs.

- exchL2T rs sppc acm swap.

- inversion sppc ; subst ; clear sppc.
acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
derIrs rs.
+ apply NSlclctxt.  apply EW.
+ apply drs.

Qed.

(* at present this allows any context on both sides, within a sequent,
  and propositional rules don't copy principal formula into premises *)
Inductive LNSKt_rules (V : Set) : rlsT (list (rel (list (PropF V)) * dir)) :=
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
eapply derrec_all_indT in D.
exact D. tauto.
intros H1 H2 H3 H4 H5; inversion H3 ; subst ; [> pose gen_swapR_step_b2R_lc as g
  | pose gen_swapR_step_b1R_lc as g
  | pose gen_swapR_step_b2L_lc as g
  | pose gen_swapR_step_b1L_lc as g
  | pose gen_swapR_step_EW_lc as g
  | pose gen_swapR_step_pr_lc as g] ;
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
eapply derrec_all_indT in D.
exact D. tauto.
intros H1 H2 H3 H4 H5. inversion H3 ; subst ; [> pose gen_swapL_step_b2R_lc 
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

