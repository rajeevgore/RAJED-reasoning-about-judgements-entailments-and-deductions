

(* proving the form of exchange where two adjacent lists are interchanged 
  for system with princrule and seqrule *)

(* 
coqc gen.v
coqc dd.v
coqc List_lemmas.v
coqc lnt.v
coqc lntacs.v
*)

Require Import ssreflect.

Require Import gen.
Require Import ddP.
Require Import List_lemmas.
Require Import lnt.
Require Import lntacs.

(* proof of exchange using step lemma *)
(* version of step lemma generic as regards rules satisfying rules_L_oe *)
(* proof using swapped, don't need 20 separate cases!! *) 
Lemma gen_swapL_step_loe: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_L_oe princrules -> 
  last_rule = nsrule (seqrule princrules) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros loe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? K ? sppc mnsp nsc]. clear nsr.
unfold nsext in nsc.
rewrite can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nsext in pp.

apply partition_2_2 in pp.

destruct c.
sE ; subst.

{ nsgen_sw rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }
all : cycle 1.
{ nsgen_sw rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{
injection H0 as. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst. clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oe in loe.
inversion_clear swap ; subst.

(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameL princrules rs pr q qin inmps acm inps0 x0. 
}

Qed.

Check gen_swapL_step_loe.

Lemma gen_swapL_step_Id: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nsrule (seqrule (@Idrule V)) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros. eapply gen_swapL_step_loe. apply Idrule_L_oe'. exact H. Qed.

Check gen_swapL_step_Id.

Lemma gen_swapL_step_pr: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nsrule (seqrule (@princrule V)) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros. eapply gen_swapL_step_loe. apply princrule_L_oe'. exact H. Qed.

Check gen_swapL_step_pr.

Lemma gen_swapL: forall {V : Set} ns
  (D : derrec (nsrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_swapL (nsrule (seqrule (@princrule V))) ns.

Proof. 
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H. 
subst.
pose gen_swapL_step_pr.
unfold gen_swapL_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.

Check gen_swapL.

(** now the same thing for left context only **)

Lemma gen_swapL_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_L_oe princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros loe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
rewrite can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2 in pp.

destruct c.
sE ; subst.

{ nsgen_sw rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{
injection H0 as. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oe in loe.
inversion_clear swap ; subst.

(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameL princrules rs pr q qin inmps acm inps0 x0. 
}

{ list_eq_nc. contradiction. }

Qed.

Check gen_swapL_step_loe_lc.

Lemma gen_swapL_step_pr_lc: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros. eapply gen_swapL_step_loe_lc.
  apply princrule_pfc_L_oe'. exact H. Qed.

Check gen_swapL_step_pr_lc.

Lemma gen_swapL_lc: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule_pfc V))) (fun _ => False) ns),
  can_gen_swapL (nslcrule (seqrule (@princrule_pfc V))) ns.

Proof. 
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H. 
subst.
pose gen_swapL_step_pr_lc.
unfold gen_swapL_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.

Check gen_swapL_lc.

